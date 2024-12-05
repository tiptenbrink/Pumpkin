use std::collections::HashMap;

use crate::{basic_types::{Inconsistency, PropagationStatusCP}, engine::propagation::{PropagationContextMut, Propagator, PropagatorInitialisationContext, ReadDomains}, predicate, predicates::{Predicate, PropositionalConjunction}, variables::DomainId};

pub(crate) struct CumulativePropagator<const SIZE: usize> {
    start_times: Box<[DomainId; SIZE]>,
    processing_times: Box<[u32; SIZE]>,
    resource_usages: Box<[u32; SIZE]>,
    resource_capacity: u32,
}

// "Trait alias"
trait BoundFn: Fn(&DomainId) -> i32 {}
impl<T: Fn(&DomainId) -> i32> BoundFn for T {}

impl<const SIZE: usize> CumulativePropagator<SIZE> {
    fn build_resource_profile<UB: BoundFn, LB: BoundFn>(&self, ub: UB, lb: LB) -> ResourceProfile<SIZE> {
        let mut compulsory_parts = Vec::<CompulsoryPart>::with_capacity(SIZE);
        
        for (i, activity) in self.start_times.iter().enumerate() {
            let processing_time = self.processing_times[i];
            let start_upper_bound = ub(activity);
            let start_lower_bound = lb(activity);
            
            let end_lower_bound = start_lower_bound + (processing_time as i32); 

            let compulsory_part = if start_upper_bound < end_lower_bound {
                CompulsoryPart::Interval((start_upper_bound, end_lower_bound))
            } else {
                CompulsoryPart::Unknown
            };

            compulsory_parts.push(compulsory_part);
        }

        ResourceProfile {
            compulsory_parts: compulsory_parts.try_into().unwrap()
        }
    }
}



#[derive(Debug)]
enum CompulsoryPart {
    Interval((i32, i32)),
    Unknown
}

struct ResourceProfile<const SIZE: usize> {
    compulsory_parts: Box<[CompulsoryPart; SIZE]>
}

struct TimeTableInconsistency {
    time: i32,
    // Using the index into the propagator
    activities: Vec<usize>
}

impl TimeTableInconsistency {
    fn into_prop_conj(self, activities: &[DomainId], processing_times: &[u32]) -> PropositionalConjunction {
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

impl<const SIZE: usize> ResourceProfile<SIZE> {
    fn time_table_consistency_check(&self, usages: &[u32; SIZE], capacity: u32) -> Result<(), TimeTableInconsistency> {
        // Computed from scratch

        // Alternatively we could create events "becomes active at t", "stops being active at t" and sort them (O (n log n))
        // Then go through it and increment/decremen total usage based on these events
        // Here we make a hashmap histogram instead, this allows O(n * max_t_interval) check I think
        // However it makes generating explanations more difficult (doesn't gives us as much flexibility to choose the time)

        let mut histogram = HashMap::<i32, (u32, Vec<usize>)>::new();

        for (i, compulsory_part) in self.compulsory_parts.iter().enumerate() {
            let (start, end) = match compulsory_part {
                CompulsoryPart::Interval((start, end)) => (*start, *end),
                CompulsoryPart::Unknown => continue,
            };
            
            let usage = usages[i];
            
            debug_assert!(start <= end);

            // For every time we are active, we increase the usage
            // This part is suboptimal because we depend on the size of the time values
            for t in start..=end {
                // We put this in separate scope so that we no longer have mutable reference to histogram entries
                let ok = {
                    let (prev_usage, active_activities) = histogram.entry(t).or_insert_with(|| (0, Vec::new()));
                    active_activities.push(i);
                    // If usage exceeds capacity, infeasible
                    if *prev_usage + usage > capacity {                    
                        false
                    } else {
                        *prev_usage += usage;
                        true
                    }
                };

                if !ok {
                    // We know it exists
                    let inconsistency = TimeTableInconsistency {
                        time: t,
                        activities: histogram.remove(&t).unwrap().1
                    };
                    return Err(inconsistency)
                }
            }
        }

        Ok(())
    }
}

impl<const SIZE: usize> Propagator for CumulativePropagator<SIZE> {
    fn name(&self) -> &str {
        "TipCumulative"
    }

    fn debug_propagate_from_scratch(&self, context: PropagationContextMut) -> PropagationStatusCP {
        // Is it right that we don't know what event caused the propagator to be called? Useful for global propagator?
        let profile: ResourceProfile<SIZE> = self.build_resource_profile(
            |v| context.upper_bound(v),
            |v| context.lower_bound(v)
        );

        profile.time_table_consistency_check(&self.resource_usages, self.resource_capacity).map_err(|e| {
            e.into_prop_conj(self.start_times.as_slice(), self.processing_times.as_slice()).into()
        })
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        let profile: ResourceProfile<SIZE> = self.build_resource_profile(
            |v| context.upper_bound(v),
            |v| context.lower_bound(v)
        );

        profile.time_table_consistency_check(&self.resource_usages, self.resource_capacity).map_err(|e| {
            e.into_prop_conj(self.start_times.as_slice(), self.processing_times.as_slice())
        })
    }
}