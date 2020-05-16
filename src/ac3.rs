use crate::*;

// TODO:
// def constraints_on(csp, variable) do
// Enum.filter(csp.constraints, fn constraint ->
//   variable in Constraint.arguments(constraint)
// end)
// end

pub fn ac3<Var, Domain>(csp: &CSP<Var, Domain>)
where
  Var: Eq + hash::Hash + Copy + Clone,
  Domain: Copy + Clone,
{
  let mut constraint_refs = csp.constraints.iter().collect::<Vec<_>>();
  for constraint in constraint_refs {
    match constraint.arguments().as_slice() {
      [variable] => {
        let reduced_domain = csp
          .domains
          .get(variable)
          .unwrap()
          .into_iter()
          .map(|value| *value)
          .filter(|value| {
            let mut assignment = HashMap::new();
            assignment.insert(*variable, *value);

            constraint.is_satisfied(&assignment)
          })
          .collect::<Vec<_>>();
      }
      [x, y] => {}
      _ => {}
    }
  }
}
