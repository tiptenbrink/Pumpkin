#![allow(unused)]

use std::ops::Range;
use std::{
    collections::{HashMap, HashSet},
    i32,
    num::NonZero, ops::RangeInclusive,
};

use crate::{
    basic_types::{Inconsistency, PropagationStatusCP},
    engine::propagation::{
        PropagationContextMut, Propagator, PropagatorInitialisationContext, ReadDomains,
    },
    predicate,
    predicates::{Predicate, PropositionalConjunction},
    variables::DomainId,
};

pub(crate) struct CumulativePropagator<const SIZE: usize> {
    start_times: Box<[DomainId; SIZE]>,
    processing_times: Box<[u32; SIZE]>,
    // INVARIANT: usage may not be 0 and must fit within i32
    resource_usages: Box<[u32; SIZE]>,
    resource_capacity: u32,
}

/// An event where an activity with index `activity` becomes either active (then usage_change > 0) or inactive (then usage_change < 0)
struct Event {
    activity: usize,
    time: i32,
    usage_change: i32,
}

struct Interval {
    start: i32,
    end_inclusive: i32,
    // total usage of activities
    usage: i64,
    // active activities
    active: Vec<usize>,
}

fn process_event(
    active: &mut HashSet<usize>,
    event: &Event,
    usage: i64,
    capacity: u32,
    time: i32,
) -> Result<i64, TimeTableInconsistency> {
    // We can avoid using HashSet by maybe sorting on removal time, then in log n we can find and remove it
    if event.usage_change > 0 {
        let _ = active.insert(event.activity);
    } else if event.usage_change < 0 {
        let _ = active.remove(&event.activity);
    } else {
        unreachable!("Usages should never be zero!")
    }

    let new_usage = usage + (event.usage_change as i64);

    if new_usage > (capacity as i64) {
        Err(TimeTableInconsistency {
            time,
            activities: active.iter().copied().collect(),
        })
    } else {
        Ok(new_usage)
    }
}

impl<const SIZE: usize> CumulativePropagator<SIZE> {
    fn build_resource_profile_from_bounds(
        &self,
        bounds: &BoundsSlice,
    ) -> Result<ResourceProfile, TimeTableInconsistency> {
        self.build_resource_profile(|v| (bounds[v].0, bounds[v].1))
    }

    fn build_resource_profile<F: Fn(usize) -> (i32, i32)>(
        &self,
        bound_fn: F,
    ) -> Result<ResourceProfile, TimeTableInconsistency> {
        // At most SIZE*2 events, so let's pre-allocate
        let mut events: Vec<Event> = Vec::with_capacity(SIZE * 2);

        for i in 0..self.start_times.len() {
            let processing_time = self.processing_times[i];
            let (start_upper_bound, start_lower_bound) = bound_fn(i);

            let end_lower_bound = start_lower_bound + (processing_time as i32);

            let usage = self.resource_usages[i];

            if start_upper_bound < end_lower_bound {
                events.push(Event {
                    activity: i,
                    time: start_upper_bound,
                    usage_change: (usage as i32),
                });
                events.push(Event {
                    activity: i,
                    time: end_lower_bound,
                    usage_change: -(usage as i32),
                });
            } else {
                // We don't know anything in this case
            };
        }

        if events.len() == 0 {
            return Ok(ResourceProfile {
                intervals: Vec::new(),
            });
        }

        // Sorts events in ascending order by time
        events.sort_by_key(|e| e.time);

        ResourceProfile::from_events(events, self.resource_capacity)
    }
}

#[derive(Debug)]
enum CompulsoryPart {
    Interval((i32, i32)),
    Unknown,
}

type BoundsSlice = [(i32, i32)];

struct ResourceProfile {
    intervals: Vec<Interval>,
}

/// An inconsistency that indicates the resource was overloaded at time `time` by activities in `activities` being active
struct TimeTableInconsistency {
    time: i32,
    // Using the index into the propagator
    activities: Vec<usize>,
}

impl TimeTableInconsistency {
    fn into_prop_conj(
        self,
        activities: &[DomainId],
        processing_times: &[u32],
    ) -> PropositionalConjunction {
        debug_assert!(self.activities.len() < processing_times.len());
        debug_assert!(activities.len() == processing_times.len());

        let mut predicate_vec = Vec::<Predicate>::new();

        for i in self.activities {
            let activity = &activities[i];
            let processing_time = processing_times[i];
            // pointwise explanation
            let expl_lb = self.time + 1 - (processing_time as i32);
            predicate_vec.push(predicate!(activity >= expl_lb));
            predicate_vec.push(predicate!(activity <= self.time));
        }

        PropositionalConjunction::new(predicate_vec)
    }
}

type Histogram = HashMap<i32, (u32, Vec<usize>)>;

impl ResourceProfile {
    /// INVARIANT: events must be sorted in ascending order
    fn from_events(mut events: Vec<Event>, capacity: u32) -> Result<Self, TimeTableInconsistency> {
        let mut intervals = Vec::new();
        let mut active = HashSet::new();
        let mut usage = 0;
        let mut event = events.pop().unwrap();

        // preconditions: events are sorted, so next_event.time >= previous_event.time
        while events.len() > 0 {
            let interval_start = event.time;

            usage = process_event(&mut active, &event, usage, capacity, interval_start)?;

            // We checked len > 0, so we can unwrap
            let mut next_event = events.pop().unwrap();
            while events.len() > 0 && next_event.time == interval_start {
                // We know next_event.time == interval_start, so we don't advance the interval
                usage = process_event(&mut active, &next_event, usage, capacity, interval_start)?;

                // We checked len > 0, so we can unwrap
                next_event = events.pop().unwrap();
                debug_assert!(next_event.time >= interval_start);
            }

            // Postcondition: events.len() == 0 \/ next_event.time != interval_start
            if (next_event.time != interval_start) {
                // We have an interval end!

                // Next event starts at next_event.time, so previous one ends one time earlier
                let interval_end = next_event.time - 1;

                // TODO see if we ever need the active later? 
                let interval = Interval {
                    start: interval_start,
                    end_inclusive: interval_end,
                    usage,
                    // Copy all the ones active
                    active: active.iter().copied().collect(),
                };

                intervals.push(interval);
                event = next_event;
            } else {
                // We know that events.len() == 0 in this case and same time as interval_start
                // So we cannot determine the interval end
                // No more should be active, every start should have associated end
                debug_assert!(active.len() == 0);
                debug_assert!(usage == 0);

                // No more interval has to be created, because they should have all ended
            }
        }

        Ok(Self { intervals })
    }

    fn intersecting_intervals(&self, lb: i32, ub: i32) -> Option<RangeInclusive<usize>> {
        debug_assert!(lb <= ub);

        // We return the ub_i s.t. ub >= interval_(ub_i).start (*1)
        // But also ub < interval(ub_i+1).start (*2)
        let ub_i = match &self.intervals.binary_search_by_key(&ub, |i| i.start) {
            // ub == interval_i.start, so (*1) holds
            // ub_i.start < ub_(i+1).start, so (*2) holds
            Ok(i) => *i,
            Err(i) => {
                // In this case we know ub > interval_(i-1).start && ub < interval_i.start
                // However, in case i == 0, ub < interval_0.start
                // Also lb <= ub so lb <= ub < interval_0.start, so no intersection
                if *i == 0 {
                    return None
                }

                // Here we know that ub > interval_(i-1), since we return i-1, (*1) holds
                // Also ub < interval_i.start from earlier so (*2) holds
                (*i - 1) 
            },
        };


        // lb <= interval_(lb_i).end_inclusive (*1)
        // lb > interval_(lb_i - 1).end_inclusive (*2)
        let lb_i = match &self.intervals.binary_search_by_key(&lb, |i| i.end_inclusive) {
            // lb == interval_i.end_incl
            Ok(i) => *i,
            Err(i) => {
                // In this case we know lb > interval_(i-1).end_inclusive && lb < interval_i.end_inclusive
                // So it can never intersect with interval_(i-1), because the entire interval is less than
                // However, it might still intersect with interval_i
                *i
            },
        };

        // Also lb > interval_(lb_i - 1).end_inclusive, so no intersection with earlier
        // Also ub < interval(ub_i+1).start, so no intersection with later
        // So definitely no intersections with lower lb_i or higher ub_i!

        if lb_i < ub_i {
            // Then lb <= interval_(lb_i).end_inclusive < interval_(ub_i).start <= ub
            return Some(lb_i..=ub_i)
        } else if lb_i == ub_i {
            // So lb_i == ub_i, just i from now on
            // lb <= interval_i.end
            // ub >= interval_i.start
            // So only way there is no intersection is if lb > interval_i.end
            // But we have lb <= interval_i.end, so we also have intersection!
            return Some(lb_i..=ub_i)
        } else {
            // ub_i < lb_i
            // ub >= interval_(ub_i).start
            // But ub < interval(ub_i+1).start
            // So ub < interval_(lb_i).start, since lb_i >= ub_i+1
            // So lb <= ub < interval_(lb_i).start
            
            // lb > interval_(lb_i-1).end_inclusive
            // lb > interval_(ub_i).end_inclusive, since ub_i <= lb_i-1
            // interval_(ub_i).end_inclusive < lb <= ub < interval_(lb_i).start

            // But ub < interval_(ub_i+1).start
            // But also ub > interval_(ub_i).end_inclusive
            // So no space in between! So this is inconsistent and cannot happen
            unreachable!()
        }
    }

    fn time_table_filtering<const SIZE: usize>(
        &self,
        bounds: &[(i32, i32); SIZE],
        usages: &[u32; SIZE],
        capacity: u32,
    ) -> [(i32, i32); SIZE] {
        let mut new_bounds = Vec::with_capacity(SIZE);

        for (i, (lb, ub)) in bounds.iter().enumerate() {
            let activity_usage = usages[i];

            let (lb, ub) = if let Some(intersections) = self.intersecting_intervals(*lb, *ub) {
                let mut new_lb = *lb;
                
                for interval in intersections.clone() {
                    let interval = &self.intervals[interval];
                    let interval_usage = interval.usage;

                    if interval_usage + (activity_usage as i64) <= (capacity as i64) {
                        break;
                    }

                    new_lb = interval.end_inclusive+1;
                }

                let mut new_ub = *ub;

                for interval in intersections.rev() {
                    let interval = &self.intervals[interval];
                    let interval_usage = interval.usage;

                    if interval_usage + (activity_usage as i64) <= (capacity as i64) {
                        // Lower bound cannot be changed
                        // Maybe do holes?
                        break;
                    }

                    new_ub = interval.start-1;
                }

                (new_lb, new_ub)
            } else {
                (*lb, *ub)
            };

            new_bounds.push((lb, ub));
        }

        new_bounds.try_into().unwrap()
    }
}

impl<const SIZE: usize> Propagator for CumulativePropagator<SIZE> {
    fn name(&self) -> &str {
        "TipCumulative"
    }

    fn debug_propagate_from_scratch(&self, context: PropagationContextMut) -> PropagationStatusCP {
        let bounds = self.start_times.map(|v| {
            (context.lower_bound(&v), context.upper_bound(&v))
        });
        
        // Is it right that we don't know what event caused the propagator to be called? Useful for global propagator?
        let profile = self
            .build_resource_profile_from_bounds(&bounds)
            .map_err(|e| {
                e.into_prop_conj(
                    self.start_times.as_slice(),
                    self.processing_times.as_slice(),
                )
            })?;
        
        let new_bounds = profile.time_table_filtering(&bounds, &self.resource_usages, self.resource_capacity);

        for (i, (old_lb, old_ub)) in bounds.into_iter().enumerate() {
            let (lb, ub) = new_bounds[i];

            if lb > old_lb {
                context.set_lower_bound(var, bound, reason)
            }
        }

        Ok(())
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        let profile = self
            .build_resource_profile(|v| {
                let var = &self.start_times[v];
                (context.lower_bound(var), context.upper_bound(var))
            })
            .map_err(|e| {
                e.into_prop_conj(
                    self.start_times.as_slice(),
                    self.processing_times.as_slice(),
                )
            })?;

        Ok(())
    }
}
