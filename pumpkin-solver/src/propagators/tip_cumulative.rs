#![allow(unused)]

use std::cmp::Reverse;
use std::ops::Range;
use std::fmt::Debug;
use std::{
    collections::{HashMap, HashSet},
    i32,
    num::NonZero, ops::RangeInclusive,
};

use crate::conjunction;
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
#[derive(Debug)]
struct Event {
    activity: usize,
    time: i32,
    usage_change: i32,
}

impl Event {
    fn pair(activity: usize, usage: u32, start: i32, end: i32) -> (Event, Event) {
        assert!(end > start);

        (Event {
            activity,
            usage_change: usage as i32,
            time: start
        }, Event {
            activity,
            usage_change: -(usage as i32),
            time: end
        })
    }
}

#[derive(Debug)]
struct Interval {
    start: i32,
    end_inclusive: i32,
    // total usage of activities
    usage: i64,
    // active activities
    active: Vec<usize>,
}

impl Interval {
    fn contains(&self, time: i32) -> bool {
        time >= self.start && time <= self.end_inclusive
    }
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

pub(crate) type ParameterVec = Vec<(DomainId, u32, u32)>;

impl<const SIZE: usize> CumulativePropagator<SIZE> {
    pub(crate) fn new_from_slice<T: Into<ParameterVec>>(tasks: T, capacity: u32) -> Self 
    {
        let tasks: ParameterVec= tasks.into();
        assert!(tasks.len() == SIZE, "Number of tasks={} should equal SIZE={}!", tasks.len(), SIZE);

        let (start_times, (usages, processing_times)): (Vec<_>, (Vec<_>, Vec<_>)) = tasks.into_iter().map(|(a, b, c)| (a, (b, c))).collect();
        

        Self::new(start_times.try_into().unwrap(), usages.try_into().unwrap(), processing_times.try_into().unwrap(), capacity)
    }

    pub(crate) fn new(start_times: [DomainId; SIZE], usages: [u32; SIZE], processing_times: [u32; SIZE], capacity: u32) -> Self {
        Self {
            start_times: Box::new(start_times),
            processing_times: Box::new(processing_times),
            resource_usages: Box::new(usages),
            resource_capacity: capacity
        }
    }


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
            let (start_lower_bound, start_upper_bound) = bound_fn(i);

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

        // Sorts events in descending order by time
        events.sort_by_key(|e| Reverse(e.time));
        println!("events!");
        ResourceProfile::from_events(events, self.resource_capacity)
    }
}

#[derive(Debug)]
enum CompulsoryPart {
    Interval((i32, i32)),
    Unknown,
}

type BoundsSlice = [(i32, i32)];

#[derive(Debug)]
struct ResourceProfile {
    intervals: Vec<Interval>,
}

/// An inconsistency that indicates the resource was overloaded at time `time` by activities in `activities` being active
#[derive(Debug)]
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
        // Activities in inconsistency should be subset
        debug_assert!(self.activities.len() <= processing_times.len());
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
    /// INVARIANT: events must be sorted in descending order
    /// INVARIANT: events come in pairs (one that increments, one that decrements usage)
    fn from_events(mut events: Vec<Event>, capacity: u32) -> Result<Self, TimeTableInconsistency> {
        println!("{:?}", events);
        let mut intervals = Vec::new();
        let mut active = HashSet::new();
        let mut usage = 0;
        let mut event = events.pop().unwrap();
        println!("new event: {:?}", event);
        // event is unprocessed

        // preconditions: events are sorted, so next_event.time >= previous_event.time
        // every event has a counterpat, so this should always be >= 1
        while events.len() > 0 {
            let interval_start = event.time;

            usage = process_event(&mut active, &event, usage, capacity, interval_start)?;
            // event is always processed by now
            println!("nwloop active: {:?}", active);

            // We checked len > 0, so we can unwrap
            let mut next_event = events.pop().unwrap();
            // next event is always unprocessed
            println!("new event: {:?}", next_event);
            while events.len() > 0 && next_event.time == interval_start {
                // We know next_event.time == interval_start, so we don't advance the interval
                usage = process_event(&mut active, &next_event, usage, capacity, interval_start)?;
                println!("inloop active: {:?}", active);
                // We checked len > 0, so we can unwrap
                next_event = events.pop().unwrap();
                println!("new event: {:?}", next_event);
                debug_assert!(next_event.time >= interval_start);
            }
            // next_event is always unprocessed (if loop executes 0 times, it's the one before, otherwise from
            // last iteration of loop)
            
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
                // next_event will be processed as event next iteration
                event = next_event;
            } else {
                // Ensure last event is processed
                usage = process_event(&mut active, &next_event, usage, capacity, interval_start)?;

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

    /// This doesn't actually really return what is useful, it returns all intervals >= lb and <= ub
    /// However, actually what we want is only if the intervals actually start intersecting at the lb and ub
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
        processing_times: &[u32; SIZE],
        usages: &[u32; SIZE],
        capacity: u32,
    ) -> [(i32, i32); SIZE] {
        let mut new_bounds = Vec::with_capacity(SIZE);

        println!("profile: {:?}", &self);

        for (i, (lb, ub)) in bounds.iter().enumerate() {
            let activity_usage = usages[i];
            let processing_time = processing_times[i] as i32;

            let (lb, ub) = if let Some(intersections) = self.intersecting_intervals(*lb, *ub + processing_time) {
                println!("intervals for lb={} and ub={}: {:?}", lb, ub, intersections);
                let mut new_lb = *lb;
                
                for interval in intersections.clone() {
                    let interval = &self.intervals[interval];
                    
                    let interval_usage = interval.usage;

                    // We only do bounds, so the moment that it's okay that means we can't change anything
                    // If lb + processing is strictly before interval start, no problem
                    if (new_lb + processing_time) < interval.start {
                        break;
                    }
                    // If capacity is not exceeded, no problem
                    if interval_usage + (activity_usage as i64) <= (capacity as i64) {
                        break;
                    }
                    // If interval already contains activity, we're not adding it again
                    if interval.active.contains(&i) {
                        break;
                    }

                    new_lb = interval.end_inclusive+1;
                }

                let mut new_ub = *ub;

                for interval in intersections.rev() {
                    let interval = &self.intervals[interval];
                    let interval_usage = interval.usage;

                    if new_ub > interval.end_inclusive {
                        break;
                    }
                    if interval_usage + (activity_usage as i64) <= (capacity as i64) {
                        break;
                    }
                    if interval.active.contains(&i) {
                        break;
                    }

                    new_ub = interval.start-processing_time;
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

    fn debug_propagate_from_scratch(&self, mut context: PropagationContextMut) -> PropagationStatusCP {
        println!("propagate!");
        
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
        
        let new_bounds = profile.time_table_filtering(&bounds, &self.processing_times, &self.resource_usages, self.resource_capacity);

        for (i, (old_lb, old_ub)) in bounds.into_iter().enumerate() {
            let var = &self.start_times[i];
            let (lb, ub) = new_bounds[i];

            if lb > old_lb {
                println!("filtering lb from {} to {}!", old_lb, lb);
                context.set_lower_bound(var, lb, conjunction!());
            }
            if ub < old_ub {
                context.set_upper_bound(var, ub, conjunction!());
            }
        }

        Ok(())
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        println!("initialise!");

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

        println!("{:?}", profile);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::basic_types::Inconsistency;
    use crate::conjunction;
    use crate::engine::test_helper::TestSolver;
    use crate::engine::variables::TransformableVariable;

    #[test]
    fn test_value_no_problem() {
        let mut solver = TestSolver::default();
        let start_x = solver.new_variable(0, 2);
        let start_y = solver.new_variable(0, 2);
        let start_z = solver.new_variable(0, 2);

        let problem = vec![(start_x, 1, 3), (start_y, 1, 3), (start_z, 1, 3)];
        
        let _ = solver.new_propagator(CumulativePropagator::<3>::new_from_slice(problem, 3)).expect("non-empty domain");
    }

    #[test]
    fn test_exceeds() {
        let mut solver = TestSolver::default();
        let start_x = solver.new_variable(0, 2);
        let start_y = solver.new_variable(0, 2);
        let start_z = solver.new_variable(0, 2);

        let problem = vec![(start_x, 1, 3), (start_y, 1, 3), (start_z, 1, 3)];
        
        let _ = solver.new_propagator(CumulativePropagator::<3>::new_from_slice(problem, 2)).expect_err("expected inconsistency!");
    }

    #[test]
    fn test_profile() {
        let mut events = Vec::new();
        let (event_1, event_2) = Event::pair(0, 1, 0, 4);
        events.push(event_1);
        events.push(event_2);
        let (event_1, event_2) = Event::pair(1, 1, 0, 3);
        events.push(event_1);
        events.push(event_2);
        let (event_1, event_2) = Event::pair(2, 1, 0, 3);
        events.push(event_1);
        events.push(event_2);
        let (event_1, event_2) = Event::pair(3, 1, 0, 4);
        events.push(event_1);
        events.push(event_2);

        events.sort_by_key(|e| Reverse(e.time));

        let profile = ResourceProfile::from_events(events, 4).unwrap();

        assert!(profile.intervals[0].start == 0);
        assert!(profile.intervals[0].end_inclusive == 2);
        assert!(profile.intervals[1].start == 3);
        assert!(profile.intervals[1].end_inclusive == 3);
        assert!(profile.intervals[1].active.contains(&0));
        assert!(profile.intervals[1].active.contains(&3));

        println!("test_profile:\n{:?}", profile);
    }

    #[test]
    fn test_value_filter() {
        let mut solver = TestSolver::default();
        let start_x = solver.new_variable(0, 2);
        let start_y = solver.new_variable(0, 2);
        let start_z = solver.new_variable(0, 2);
        
        let start_filter = solver.new_variable(2, 10);

        let problem = vec![(start_x, 1, 3), (start_y, 1, 3), (start_z, 1, 3), (start_filter, 1, 3)];
        // Due to the mandatory parts, time 2 is now full
        // So the lb from start_filter will be increased to 3
        
        let _ = solver.new_propagator(CumulativePropagator::<4>::new_from_slice(problem, 3)).expect("non-empty domain");

        // These unchanged
        solver.assert_bounds(start_x, 0, 2);
        solver.assert_bounds(start_y, 0, 2);
        solver.assert_bounds(start_z, 0, 2);
        // Lb should have increased by 1
        solver.assert_bounds(start_filter, 3, 10);
    }

    #[test]
    fn test_value_filter_ub() {
        let mut solver = TestSolver::default();
        let start_x = solver.new_variable(3, 5);
        let start_y = solver.new_variable(3, 5);
        let start_z = solver.new_variable(3, 5);
        
        let start_filter = solver.new_variable(0, 3);

        let problem = vec![(start_x, 1, 3), (start_y, 1, 3), (start_z, 1, 3), (start_filter, 1, 3)];
        // Due to the mandatory parts, time 5 is now full
        // So the ub from start_filter will be decreased to 2
        
        let _ = solver.new_propagator(CumulativePropagator::<4>::new_from_slice(problem, 3)).expect("non-empty domain");

        // These unchanged
        solver.assert_bounds(start_x, 3, 5);
        solver.assert_bounds(start_y, 3, 5);
        solver.assert_bounds(start_z, 3, 5);
        // ub should have decreased by 1
        solver.assert_bounds(start_filter, 0, 2);
    }
}