use std::collections::HashMap;
use std::fmt;

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

type Assignment = HashMap<Cell, bool>;

// NOTE: constraint requires to always be debuggable to make CSP debuggable too
trait Constraint: fmt::Debug {
  fn arguments(&self) -> Vec<Cell>;
  fn satisfies(&self, assignment: &Assignment) -> bool;
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

  fn satisfies(&self, assignment: &Assignment) -> bool {
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

  fn satisfies(&self, assignment: &Assignment) -> bool {
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
        if row != cell.col {
          curr_cell_constraints.push(Box::new(NotPresentInBothCells {
            curr_cell: cell.clone(),
            another_cell: Cell {
              row: row,
              col: cell.row,
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

  // FIXME: how to run unique on constraints? Hash trait objects are not possible, since Hash takes generic parameter,
  // thus, we cannot define Hash as Constraint's supertrait.

  CSP {
    variables: cells,
    domains,
    constraints,
  }
}

fn main() {
  let csp = n_queens_csp(8);

  println!(
    "8 queens CSP total vars = {}, total constraints = {}",
    csp.variables.len(),
    csp.constraints.len()
  );
  //   println!("8 queens CSP:\n{:?}", csp);
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

    assert!(constraint.satisfies(&assignment));

    assignment.insert(next_to_top_left, false);
    assert!(constraint.satisfies(&assignment));

    assignment.insert(next_to_top_left, true);
    assert!(!constraint.satisfies(&assignment));
  }

  #[test]
  fn present_in_one_cell_works() {
    let top_row = (0..8).map(|col| Cell { row: 0, col }).collect::<Vec<_>>();
    let unrelated_place = Cell { row: 3, col: 7 };

    let constraint = PresentInOneCell { cells: top_row.clone() };
    assert_eq!(constraint.arguments(), top_row);

    let mut assignment = HashMap::new();
    // no queens are placed yet => not satisfied
    assert!(!constraint.satisfies(&assignment));

    assignment.insert(unrelated_place, true);
    // no queens in the row under consideration => not satisfied
    assert!(!constraint.satisfies(&assignment));

    assignment.insert(Cell { row: 0, col: 3 }, true);
    // exactly 1 queen in the row => satisfied
    assert!(constraint.satisfies(&assignment));

    assignment.insert(Cell { row: 0, col: 6 }, true);
    // more than 1 queen in the row => not satisfied
    assert!(!constraint.satisfies(&assignment));
  }
}
