use std::collections::HashMap;
use std::fmt;
use std::io;
use std::io::Write;
use std::time::Instant;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct Cell {
  row: u32,
  col: u32,
}

#[derive(Debug)]
struct CSP {
  variables: Vec<Cell>,
  domains: HashMap<Cell, Vec<bool>>,
  constraints: Vec<Box<dyn Constraint>>,
}

impl CSP {
  /// Checks if all constraints are satisfied & all variables are assigned
  fn is_solved(&self, assignment: &Assignment) -> bool {
    assignment.len() == self.variables.len()
      && self
        .constraints
        .iter()
        .all(|constraint| constraint.is_satisfied(assignment))
  }

  /// Checks if possibly partial assignment is consistent.
  fn is_consistent(&self, assignment: &Assignment) -> bool {
    self.constraints.iter().all(|constraint| {
      // only test constraints all arguments of which are assigned
      if constraint.arguments().iter().all(|arg| assignment.contains_key(arg)) {
        constraint.is_satisfied(assignment)
      } else {
        true
      }
    })
  }
}

type Assignment = HashMap<Cell, bool>;

fn pretty_print(n: u32, assignment: &Assignment) {
  let ansi_reset = "\x1B[49m";
  let light_yellow_background = "\x1B[103m";

  let mut is_white = true;

  for row in 0..n {
    for col in 0..n {
      // set background
      let background = if is_white { ansi_reset } else { light_yellow_background };

      let is_occupied = assignment.get(&Cell { row, col }).unwrap_or(&false);

      if *is_occupied {
        print!("{} Q {}", background, ansi_reset);
      } else {
        print!("{}   {}", background, ansi_reset);
      }

      is_white = !is_white;
    }

    is_white = !is_white;

    io::stdout().flush().unwrap();
    println!("");
  }
}

// NOTE: constraint requires to always be debuggable to make CSP debuggable too
trait Constraint: fmt::Debug {
  fn arguments(&self) -> Vec<Cell>;
  fn is_satisfied(&self, assignment: &Assignment) -> bool;
}

/// Verifies that queens are not present at the same time
/// in `curr_cell` and `another_cell`.
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
struct NotPresentInBothCells {
  curr_cell: Cell,
  another_cell: Cell,
}

impl Constraint for NotPresentInBothCells {
  fn arguments(&self) -> Vec<Cell> {
    vec![self.curr_cell, self.another_cell]
  }

  fn is_satisfied(&self, assignment: &Assignment) -> bool {
    match assignment.get(&self.curr_cell) {
      None => true,
      Some(false) => true,
      Some(true) => match assignment.get(&self.another_cell) {
        None => true,
        Some(present_in_another) => !present_in_another,
      },
    }
  }
}

/// Verifies that only one of the `cells` has a Queen.
#[derive(Debug, Hash)]
struct PresentInOneCell {
  cells: Vec<Cell>,
}

impl PresentInOneCell {
  fn make_for_row(row: u32, n: u32) -> PresentInOneCell {
    let cells = (0..n).map(|col| Cell { row, col }).collect::<Vec<_>>();

    PresentInOneCell { cells }
  }
}

impl Constraint for PresentInOneCell {
  fn arguments(&self) -> Vec<Cell> {
    self.cells.clone()
  }

  fn is_satisfied(&self, assignment: &Assignment) -> bool {
    let placed = self
      .cells
      .iter()
      .map(|cell| assignment.get(cell).unwrap_or(&false))
      .filter(|presence| **presence)
      .count();

    placed == 1
  }
}

fn n_queens_csp(n: u32) -> CSP {
  assert_ne!(n, 0);

  let cells = (0..n)
    .flat_map(move |row| (0..n).map(move |col| Cell { row, col }))
    .collect::<Vec<_>>();

  let domains = cells
    .iter()
    .map(|cell| (cell.clone(), vec![true, false]))
    .collect::<HashMap<_, _>>();

  let mut not_present_constraints = cells
    .iter()
    .flat_map(|cell| {
      let mut curr_cell_constraints: Vec<Box<NotPresentInBothCells>> = vec![];

      // same row constraints
      for col in 0..n {
        if col != cell.col {
          curr_cell_constraints.push(Box::new(NotPresentInBothCells {
            curr_cell: cell.clone(),
            another_cell: Cell { row: cell.row, col },
          }));
        }
      }

      // same column constraints
      for row in 0..n {
        if row != cell.row {
          curr_cell_constraints.push(Box::new(NotPresentInBothCells {
            curr_cell: cell.clone(),
            another_cell: Cell {
              row: row,
              col: cell.col,
            },
          }));
        }
      }

      // same diagonals constraints
      for row in 0..n {
        for col in 0..n {
          if row != cell.row
            && col != cell.col
            && (row as i32 - cell.row as i32).abs() == (col as i32 - cell.col as i32)
          {
            curr_cell_constraints.push(Box::new(NotPresentInBothCells {
              curr_cell: cell.clone(),
              another_cell: Cell { row, col },
            }));
          }
        }
      }

      curr_cell_constraints
    })
    .collect::<Vec<_>>();

  // we first need to sort for dedup to work as Elixir's Enum.uniq
  //  n = 8, total constraints = 1116 with this logic
  //  n = 8, total constraints = 1184 without it
  not_present_constraints.sort();
  not_present_constraints.dedup();

  let mut constraints: Vec<Box<dyn Constraint>> = not_present_constraints
    .into_iter()
    .map(|x| x as Box<dyn Constraint>)
    .collect();

  // add "queen should be placed in each row" constraint to make trivial solutions illegal
  for row in 0..n {
    constraints.push(Box::new(PresentInOneCell::make_for_row(row, n)));
  }

  // NOTE: it's not possible trivially to run unique on a vector of Box<dyn Constraint>s:
  // Hash trait objects are not possible, since Hash takes generic parameter,
  // thus, we cannot define Hash as Constraint's supertrait.

  CSP {
    variables: cells,
    domains,
    constraints,
  }
}

// TODO: basic recursive version of backtracking (should be runnable for small N,
// and will demonstrate the overflow), and then the stack version
// comparison to elixir in terms of generality, verbosity, and performance

fn backtrack(assignment: Assignment, unassigned: &[Cell], csp: &CSP) -> Option<Assignment> {
  //   println!("unassigned = {:?}, assignment = {:?}", unassigned, assignment);
  match unassigned.split_first() {
    None => Some(assignment),
    Some((unassigned_var, rest)) => {
      let domain = csp.domains.get(unassigned_var).unwrap();

      for value in domain {
        let mut candidate = assignment.clone();
        candidate.insert(*unassigned_var, *value);

        if csp.is_consistent(&candidate) {
          match backtrack(candidate, rest, csp) {
            None => continue,
            Some(solution) => return Some(solution),
          }
        }
      }

      None
    }
  }
}

enum RecursionState<'a> {
  Proceed {
    assignment: Assignment,
    unassigned: &'a [Cell],
    csp: &'a CSP,
  },
}

fn backtrack_iter(assignment: Assignment, unassigned: &[Cell], csp: &CSP) -> Option<Assignment> {
  use RecursionState::*;

  let mut stack = vec![Proceed {
    assignment,
    unassigned,
    csp,
  }];

  while let Some(state) = stack.pop() {
    match state {
      Proceed {
        assignment,
        unassigned,
        csp,
      } => match unassigned.split_first() {
        None => return Some(assignment),
        Some((unassigned_var, rest)) => {
          let domain = csp.domains.get(unassigned_var).unwrap();

          // need to consider domain values in reverse direction
          // to match execution order of recursive version
          for value in domain.iter().rev() {
            let mut candidate = assignment.clone();
            candidate.insert(*unassigned_var, *value);

            if csp.is_consistent(&candidate) {
              stack.push(Proceed {
                assignment: candidate,
                unassigned: rest,
                csp,
              });
            } else {
              continue;
            }
          }
        }
      },
    }
  }

  None
}

fn main() {
  let n = 8;
  let csp = n_queens_csp(n);

  println!(
    "{} queens CSP total vars = {}, total constraints = {}",
    n,
    csp.variables.len(),
    csp.constraints.len()
  );

  let t = Instant::now();
  let solution = backtrack(HashMap::new(), &csp.variables, &csp);
  let execution_time_mcs = t.elapsed().as_micros();
  println!("Solved in {} µs.", execution_time_mcs);

  match solution.clone() {
    Some(solution) => pretty_print(n, &solution),
    None => println!("No solution."),
  }

  let t = Instant::now();
  let solution2 = backtrack_iter(HashMap::new(), &csp.variables, &csp);
  let execution_time_mcs = t.elapsed().as_micros();

  println!("Solved with iteration in {} µs.", execution_time_mcs);

  match solution2.clone() {
    Some(solution2) => pretty_print(n, &solution2),
    None => println!("No solution."),
  }

  if (solution == solution2) {
    println!("Solutions match!");
  } else {
    println!("Solutions don't match!");
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn non_present_in_both_cells_works() {
    let top_left = Cell { row: 0, col: 0 };
    let next_to_top_left = Cell { row: 0, col: 1 };
    let unrelated_place = Cell { row: 3, col: 7 };

    let constraint = NotPresentInBothCells {
      curr_cell: top_left,
      another_cell: next_to_top_left,
    };

    assert_eq!(constraint.arguments(), vec![top_left, next_to_top_left]);

    let mut assignment = HashMap::new();
    assignment.insert(top_left, true);
    assignment.insert(unrelated_place, true);

    assert!(constraint.is_satisfied(&assignment));

    assignment.insert(next_to_top_left, false);
    assert!(constraint.is_satisfied(&assignment));

    assignment.insert(next_to_top_left, true);
    assert!(!constraint.is_satisfied(&assignment));
  }

  #[test]
  fn present_in_one_cell_works() {
    let top_row = (0..8).map(|col| Cell { row: 0, col }).collect::<Vec<_>>();
    let unrelated_place = Cell { row: 3, col: 7 };

    let constraint = PresentInOneCell { cells: top_row.clone() };
    assert_eq!(constraint.arguments(), top_row);

    let mut assignment = HashMap::new();
    // no queens are placed yet => not satisfied
    assert!(!constraint.is_satisfied(&assignment));

    assignment.insert(unrelated_place, true);
    // no queens in the row under consideration => not satisfied
    assert!(!constraint.is_satisfied(&assignment));

    assignment.insert(Cell { row: 0, col: 3 }, true);
    // exactly 1 queen in the row => satisfied
    assert!(constraint.is_satisfied(&assignment));

    assignment.insert(Cell { row: 0, col: 6 }, true);
    // more than 1 queen in the row => not satisfied
    assert!(!constraint.is_satisfied(&assignment));
  }

  #[test]
  fn is_consistent_and_is_solved_work() {
    let csp = n_queens_csp(4);

    let mut assignment = HashMap::new();
    assignment.insert(Cell { row: 0, col: 0 }, false);
    assignment.insert(Cell { row: 0, col: 1 }, true);
    assignment.insert(Cell { row: 0, col: 2 }, false);
    assignment.insert(Cell { row: 0, col: 3 }, false);

    assignment.insert(Cell { row: 1, col: 0 }, false);
    assignment.insert(Cell { row: 1, col: 1 }, false);
    assignment.insert(Cell { row: 1, col: 2 }, false);
    assignment.insert(Cell { row: 1, col: 3 }, true);

    assert!(csp.is_consistent(&assignment));
    assert!(!csp.is_solved(&assignment));

    assignment.insert(Cell { row: 0, col: 0 }, true);

    assert!(!csp.is_consistent(&assignment));
    assert!(!csp.is_solved(&assignment));

    assignment.insert(Cell { row: 0, col: 0 }, false);

    assignment.insert(Cell { row: 2, col: 0 }, true);
    assignment.insert(Cell { row: 2, col: 1 }, false);
    assignment.insert(Cell { row: 2, col: 2 }, false);
    assignment.insert(Cell { row: 2, col: 3 }, false);

    assignment.insert(Cell { row: 3, col: 0 }, false);
    assignment.insert(Cell { row: 3, col: 1 }, false);
    assignment.insert(Cell { row: 3, col: 2 }, true);
    assignment.insert(Cell { row: 3, col: 3 }, false);

    assert!(csp.is_consistent(&assignment));
    assert!(csp.is_solved(&assignment));
  }
}
