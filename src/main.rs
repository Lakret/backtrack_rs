use backtrack_rs::n_queens::*;
use backtrack_rs::*;

use lazy_static::lazy_static;
use std::collections::HashMap;
use std::time::Instant;

// lazy_static! {
//   static ref CSP_PAR: CSP<Cell, bool> = { n_queens_csp(8) };
// }

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
  println!("Solved in {} µs. (Recursive)", execution_time_mcs);

  match solution.clone() {
    Some(solution) => pretty_print(n, &solution),
    None => println!("No solution."),
  }

  // let t = Instant::now();
  // let solution = backtrack_par(HashMap::new(), &CSP_PAR.variables, &CSP_PAR);
  // let execution_time_mcs = t.elapsed().as_micros();
  // println!("Solved in {} µs. (Parallel)", execution_time_mcs);

  // match solution.clone() {
  //   Some(solution) => pretty_print(n, &solution),
  //   None => println!("No solution."),
  // }

  let t = Instant::now();
  let solution2 = backtrack_iter(HashMap::new(), &csp.variables, &csp);
  let execution_time_mcs = t.elapsed().as_micros();

  println!("Solved with iteration in {} µs.", execution_time_mcs);

  match solution2.clone() {
    Some(solution2) => pretty_print(n, &solution2),
    None => println!("No solution."),
  }

  if solution == solution2 {
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
