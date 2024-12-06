#![allow(unused)]

use std::{
    collections::{HashMap, HashSet},
    i32,
    num::NonZero,
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

    fn time_table_filtering(
        &self,
        bounds: &BoundsSlice,
        capacity: u32,
    ) -> Result<(), TimeTableInconsistency> {
        for (lb, ub) in bounds {}

        Ok(())
    }
}

impl<const SIZE: usize> Propagator for CumulativePropagator<SIZE> {
    fn name(&self) -> &str {
        "TipCumulative"
    }

    fn debug_propagate_from_scratch(&self, context: PropagationContextMut) -> PropagationStatusCP {
        // Is it right that we don't know what event caused the propagator to be called? Useful for global propagator?
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
