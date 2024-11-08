use log::warn;

use super::ValueSelector;
use crate::basic_types::KeyedVec;
use crate::basic_types::ProblemSolution;
use crate::basic_types::SolutionReference;
use crate::basic_types::StorageKey;
use crate::branching::SelectionContext;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::variables::Literal;
use crate::engine::variables::PropositionalVariable;
use crate::pumpkin_assert_moderate;
use crate::pumpkin_assert_simple;

/// The [solution-guided \[1\]](https://people.eng.unimelb.edu.au/pstuckey/papers/lns-restarts.pdf) [`ValueSelector`], this method searches around the provided solution.
///
/// It does this by saving the values found in the solution and assigning to those values
/// whenever possible, if it is not possible then it will fall back on the provided
/// `backup_selector`.
///
/// # Bibliography
/// \[1\] E. Demirović, G. Chu, and P. J. Stuckey, ‘Solution-based phase saving for CP: A
/// value-selection heuristic to simulate local search behavior in complete solvers’, in Principles
/// and Practice of Constraint Programming: 24th International Conference, CP 2018, Lille, France,
/// August 27-31, 2018, Proceedings 24, 2018, pp. 99–108.
#[derive(Debug)]
pub struct SolutionGuidedValueSelector<Var, Value, BackUpSelector> {
    /// The value of the variable in the provided solution.
    saved_values: KeyedVec<Var, Option<Value>>,
    /// The [`ValueSelector`] to use in case that the saved value is already assigned
    backup_selector: BackUpSelector,
}

impl<BackupSelector> SolutionGuidedValueSelector<PropositionalVariable, bool, BackupSelector>
where
    BackupSelector: ValueSelector<PropositionalVariable>,
{
    pub fn new(
        variables: &[PropositionalVariable],
        variables_with_initial_value: Vec<(PropositionalVariable, bool)>,
        backup_selector: BackupSelector,
    ) -> Self {
        pumpkin_assert_simple!(
            variables.len() >= variables_with_initial_value.len(),
            "More values were provided than SolutionGuidedValueSelector variables"
        );
        pumpkin_assert_moderate!(
            variables_with_initial_value
                .iter()
                .all(|(variable, _)| variables.contains(variable)),
            "Not every variable in the provided values was in variables"
        );
        if variables.is_empty() {
            warn!("Empty set of variables provided to solution guided value selector, this could indicate an error");
            return SolutionGuidedValueSelector {
                saved_values: KeyedVec::default(),
                backup_selector,
            };
        }
        let max_index = variables
            .iter()
            .map(|variable| variable.index())
            .max()
            .unwrap();
        let saved_values = KeyedVec::new(vec![None; max_index + 1]);
        let mut solution_guided = SolutionGuidedValueSelector {
            saved_values,
            backup_selector,
        };
        for (var, value) in variables_with_initial_value {
            solution_guided.update(var, value)
        }
        solution_guided
    }
}

impl<Var, Value, BackupSelector> SolutionGuidedValueSelector<Var, Value, BackupSelector>
where
    Var: StorageKey,
    Value: Copy,
    BackupSelector: ValueSelector<Var>,
{
    /// Update the value of the current variable
    fn update(&mut self, var: Var, new_value: Value) {
        self.saved_values[var] = Some(new_value);
    }
}

impl<BackupSelector> ValueSelector<PropositionalVariable>
    for SolutionGuidedValueSelector<PropositionalVariable, bool, BackupSelector>
where
    BackupSelector: ValueSelector<PropositionalVariable>,
{
    fn select_value(
        &mut self,
        context: &mut SelectionContext,
        decision_variable: PropositionalVariable,
    ) -> Predicate {
        self.saved_values.accomodate(decision_variable, None);
        match self.saved_values[decision_variable] {
            Some(value) => {
                pumpkin_assert_moderate!(
                    !context.is_propositional_variable_fixed(decision_variable)
                );
                Literal::new(decision_variable, value).into()
            }
            None => self
                .backup_selector
                .select_value(context, decision_variable),
        }
    }

    fn on_solution(&mut self, solution: SolutionReference) {
        for propositional_variable in solution.get_propostional_variables() {
            self.saved_values.accomodate(propositional_variable, None);
            self.update(
                propositional_variable,
                solution.get_propositional_variable_value(propositional_variable),
            )
        }
        self.backup_selector.on_solution(solution)
    }

    fn is_restart_pointless(&mut self) -> bool {
        self.backup_selector.is_restart_pointless()
    }
}

#[cfg(test)]
mod tests {
    use super::SolutionGuidedValueSelector;
    use crate::basic_types::tests::TestRandom;
    use crate::basic_types::StorageKey;
    use crate::branching::value_selection::PhaseSaving;
    use crate::branching::value_selection::ValueSelector;
    use crate::branching::SelectionContext;
    use crate::engine::predicates::predicate::Predicate;
    use crate::results::SolutionReference;
    use crate::variables::Literal;
    use crate::variables::PropositionalVariable;

    #[test]
    fn saved_value_is_returned_prop() {
        let (assignments_integer, assignments_propositional) =
            SelectionContext::create_for_testing(0, 1, None);
        let mut test_rng = TestRandom::default();
        let mut context = SelectionContext::new(
            &assignments_integer,
            &assignments_propositional,
            &mut test_rng,
        );
        let propositional_variables = context.get_propositional_variables().collect::<Vec<_>>();

        let mut solution_guided = SolutionGuidedValueSelector::new(
            &propositional_variables,
            Vec::new(),
            PhaseSaving::new(&propositional_variables),
        );

        solution_guided.update(propositional_variables[0], true);

        let chosen = solution_guided.select_value(&mut context, propositional_variables[0]);

        if let Predicate::Literal(chosen) = chosen {
            assert!(chosen.is_positive())
        } else {
            panic!("Predicate which was not a literal was returned")
        }
    }

    #[test]
    fn initial_value_is_returned_prop() {
        let (assignments_integer, assignments_propositional) =
            SelectionContext::create_for_testing(0, 1, None);
        let mut test_rng = TestRandom::default();
        let mut context = SelectionContext::new(
            &assignments_integer,
            &assignments_propositional,
            &mut test_rng,
        );
        let propositional_variables = context.get_propositional_variables().collect::<Vec<_>>();

        let mut solution_guided = SolutionGuidedValueSelector::new(
            &propositional_variables,
            vec![(propositional_variables[0], true)],
            PhaseSaving::new(&propositional_variables),
        );

        let chosen = solution_guided.select_value(&mut context, propositional_variables[0]);

        if let Predicate::Literal(chosen) = chosen {
            assert!(chosen.is_positive())
        } else {
            panic!("Predicate which was not a literal was returned")
        }
    }

    #[test]
    fn backup_is_used_when_value_is_not_saved() {
        let (assignments_integer, assignments_propositional) =
            SelectionContext::create_for_testing(0, 1, None);
        let mut test_rng = TestRandom::default();
        let mut context = SelectionContext::new(
            &assignments_integer,
            &assignments_propositional,
            &mut test_rng,
        );
        let propositional_variables = context.get_propositional_variables().collect::<Vec<_>>();

        let backup = PhaseSaving::with_initial_values(
            &propositional_variables,
            vec![(propositional_variables[0], true)],
            false,
        );

        let mut solution_guided =
            SolutionGuidedValueSelector::new(&propositional_variables, Vec::new(), backup);

        let chosen = solution_guided.select_value(&mut context, propositional_variables[0]);

        if let Predicate::Literal(chosen) = chosen {
            assert!(chosen.is_positive())
        } else {
            panic!("Predicate which was not a literal was returned")
        }
    }

    #[test]
    fn does_not_panic_with_unknown_selected_variable() {
        let variable = PropositionalVariable::create_from_index(1);

        let backup = PhaseSaving::new(&[variable]);

        let mut solution_guided = SolutionGuidedValueSelector::new(&[], vec![], backup);

        let (assignments_integer, assignments_propositional) =
            SelectionContext::create_for_testing(0, 1, None);
        let mut test_rng = TestRandom::default();
        let mut context = SelectionContext::new(
            &assignments_integer,
            &assignments_propositional,
            &mut test_rng,
        );

        let selected = solution_guided.select_value(&mut context, variable);

        assert_eq!(selected, Predicate::Literal(Literal::new(variable, false)));
    }

    #[test]
    fn does_not_panic_with_unknown_on_solution() {
        let variable = PropositionalVariable::create_from_index(1);

        let backup = PhaseSaving::new(&[variable]);

        let mut solution_guided = SolutionGuidedValueSelector::new(&[], vec![], backup);

        let (assignments_integer, mut assignments_propositional) =
            SelectionContext::create_for_testing(0, 1, None);
        let mut test_rng = TestRandom::default();

        assignments_propositional.increase_decision_level();

        assignments_propositional.enqueue_decision_literal(Literal::new(variable, true));

        solution_guided.on_solution(SolutionReference::new(
            &assignments_propositional,
            &assignments_integer,
        ));

        let _ = assignments_propositional.synchronise(0).collect::<Vec<_>>();

        let mut context = SelectionContext::new(
            &assignments_integer,
            &assignments_propositional,
            &mut test_rng,
        );

        let selected = solution_guided.select_value(&mut context, variable);

        assert_eq!(selected, Predicate::Literal(Literal::new(variable, true)));
    }
}
