use crate::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Cell {
  pub row: u32,
  pub col: u32,
}

pub fn pretty_print(n: u32, assignment: &Assignment<Cell, bool>) {
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

/// Verifies that queens are not present at the same time
/// in `curr_cell` and `another_cell`.
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct NotPresentInBothCells {
  pub curr_cell: Cell,
  pub another_cell: Cell,
}

impl Constraint for NotPresentInBothCells {
  type Var = Cell;
  type Domain = bool;

  fn arguments(&self) -> Vec<Cell> {
    vec![self.curr_cell, self.another_cell]
  }

  fn is_satisfied(&self, assignment: &Assignment<Cell, bool>) -> bool {
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
pub struct PresentInOneCell {
  pub cells: Vec<Cell>,
}

impl PresentInOneCell {
  pub fn make_for_row(row: u32, n: u32) -> PresentInOneCell {
    let cells = (0..n).map(|col| Cell { row, col }).collect::<Vec<_>>();

    PresentInOneCell { cells }
  }
}

impl Constraint for PresentInOneCell {
  type Var = Cell;
  type Domain = bool;

  fn arguments(&self) -> Vec<Cell> {
    self.cells.clone()
  }

  fn is_satisfied(&self, assignment: &Assignment<Cell, bool>) -> bool {
    let placed = self
      .cells
      .iter()
      .map(|cell| assignment.get(cell).unwrap_or(&false))
      .filter(|presence| **presence)
      .count();

    placed == 1
  }
}

pub fn n_queens_csp(n: u32) -> CSP<Cell, bool> {
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

  let mut constraints: Vec<Box<dyn Constraint<Var = Cell, Domain = bool>>> = not_present_constraints
    .into_iter()
    .map(|x| x as Box<dyn Constraint<Var = Cell, Domain = bool>>)
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
