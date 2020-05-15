use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash;
use std::io;
use std::io::Write;

pub mod n_queens;

// NOTE: constraint requires to always be debuggable to make CSP debuggable too
// Sync + Send is required for parallel versions
pub trait Constraint: fmt::Debug + Sync + Send {
  type Var;
  type Domain;

  fn arguments(&self) -> Vec<Self::Var>;
  fn is_satisfied(&self, assignment: &Assignment<Self::Var, Self::Domain>) -> bool;
}

#[derive(Debug)]
pub struct CSP<Var, Domain> {
  pub variables: Vec<Var>,
  pub domains: HashMap<Var, Vec<Domain>>,
  pub constraints: Vec<Box<dyn Constraint<Var = Var, Domain = Domain>>>,
}

impl<Var, Domain> CSP<Var, Domain>
where
  Var: Eq + hash::Hash,
{
  /// Checks if all constraints are satisfied & all variables are assigned
  pub fn is_solved(&self, assignment: &Assignment<Var, Domain>) -> bool {
    assignment.len() == self.variables.len()
      && self
        .constraints
        .iter()
        .all(|constraint| constraint.is_satisfied(assignment))
  }

  /// Checks if possibly partial assignment is consistent.
  pub fn is_consistent(&self, assignment: &Assignment<Var, Domain>) -> bool {
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

pub type Assignment<Var, Domain> = HashMap<Var, Domain>;

pub fn backtrack<Var, Domain>(
  assignment: Assignment<Var, Domain>,
  unassigned: &[Var],
  csp: &CSP<Var, Domain>,
) -> Option<Assignment<Var, Domain>>
where
  Var: Eq + hash::Hash + Clone + Copy,
  Domain: Clone + Copy,
{
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

//---------------------------
// Caching implementation
//---------------------------

use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;

fn assignment_hash<Var, Domain>(assignment: &Assignment<Var, Domain>) -> u64
where
  Var: Eq + hash::Hash + Clone + Copy,
  Domain: Eq + hash::Hash + Clone + Copy,
{
  let mut hasher = DefaultHasher::new();

  for (var, val) in assignment.iter() {
    var.hash(&mut hasher);
    val.hash(&mut hasher);
  }

  hasher.finish()
}

pub fn backtrack_cache<Var, Domain>(
  assignment: Assignment<Var, Domain>,
  unassigned: &[Var],
  csp: &CSP<Var, Domain>,
  rejected: &mut HashSet<u64>,
) -> Option<Assignment<Var, Domain>>
where
  Var: Eq + hash::Hash + Clone + Copy,
  Domain: Eq + hash::Hash + Clone + Copy,
{
  match unassigned.split_first() {
    None => Some(assignment),
    Some((unassigned_var, rest)) => {
      let domain = csp.domains.get(unassigned_var).unwrap();

      for value in domain {
        let mut candidate = assignment.clone();
        candidate.insert(*unassigned_var, *value);

        let hash = assignment_hash(&candidate);

        if !rejected.contains(&hash) {
          if csp.is_consistent(&candidate) {
            match backtrack(candidate, rest, csp) {
              None => continue,
              Some(solution) => return Some(solution),
            }
          } else {
            rejected.insert(hash);
          }
        }
      }

      None
    }
  }
}

//---------------------------
// Iterative implementation
//---------------------------

struct StackFrame<'a, Var, Domain> {
  assignment: Assignment<Var, Domain>,
  unassigned: &'a [Var],
  csp: &'a CSP<Var, Domain>,
}

pub fn backtrack_iter<Var, Domain>(
  assignment: Assignment<Var, Domain>,
  unassigned: &[Var],
  csp: &CSP<Var, Domain>,
) -> Option<Assignment<Var, Domain>>
where
  Var: Eq + hash::Hash + Clone + Copy,
  Domain: Clone + Copy,
{
  let mut stack = vec![StackFrame {
    assignment,
    unassigned,
    csp,
  }];

  while let Some(state) = stack.pop() {
    match state {
      StackFrame {
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
              stack.push(StackFrame {
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

//---------------------------
// Parallel implementation
//---------------------------

use std::thread;
use std::thread::JoinHandle;

use crossbeam::crossbeam_channel;
use crossbeam::crossbeam_channel::Sender;

enum Message<'a, Var, Domain> {
  Terminate,
  Job(StackFramePar<'a, Var, Domain>),
}

struct StackFramePar<'a, Var, Domain> {
  assignment: Assignment<Var, Domain>,
  unassigned: &'a [Var],
  csp: &'a CSP<Var, Domain>,
}

pub fn backtrack_par<Var, Domain>(
  assignment: Assignment<Var, Domain>,
  unassigned: &'static [Var],
  csp: &'static CSP<Var, Domain>,
) -> Option<Assignment<Var, Domain>>
where
  Var: Eq + hash::Hash + Clone + Copy + Sync + Send,
  Domain: Clone + Copy + Sync + Send,
{
  use Message::*;

  let n_threads = 4;

  let (send_work, get_work) = crossbeam_channel::unbounded();
  let (send_result, get_result) = crossbeam_channel::unbounded();

  let _pool = (0..n_threads)
    .map(|idx| {
      let (send_work, get_work) = (send_work.clone(), get_work.clone());
      let send_result = send_result.clone();

      thread::spawn(move || loop {
        match get_work.recv().unwrap() {
          Job(work_unit) => do_work(work_unit, send_work.clone(), send_result.clone()),
          Terminate => {
            println!("Thread {} terminating.", idx);
            break;
          }
        }
      })
    })
    .collect::<Vec<_>>();

  let first_unit = StackFramePar {
    assignment,
    unassigned,
    csp,
  };

  send_work.send(Job(first_unit)).unwrap();

  let result = get_result.recv().unwrap();

  for _ in 0..n_threads {
    send_work.send(Terminate).unwrap();
  }

  result
}

// TODO: instead of sending job out for each job, maintain a level variable,
// and only send a new task to the queue
// if the level is higher than certain value:
// https://www.drdobbs.com/architecture-and-design/three-parallel-backtracking-designs/232300302
fn do_work<'a, Var, Domain>(
  work_unit: StackFramePar<'a, Var, Domain>,
  send_work: Sender<Message<'a, Var, Domain>>,
  send_result: Sender<Option<Assignment<Var, Domain>>>,
) where
  Var: Eq + hash::Hash + Clone + Copy + Sync + Send,
  Domain: Clone + Copy + Sync + Send,
{
  match work_unit {
    StackFramePar {
      assignment,
      unassigned,
      csp,
    } => match unassigned.split_first() {
      None => send_result.send(Some(assignment)).unwrap(),
      Some((unassigned_var, rest)) => {
        let domain = csp.domains.get(unassigned_var).unwrap();

        // need to consider domain values in reverse direction
        // to match execution order of recursive version
        for value in domain.iter().rev() {
          let mut candidate = assignment.clone();
          candidate.insert(*unassigned_var, *value);

          if csp.is_consistent(&candidate) {
            send_work
              .send(Message::Job(StackFramePar {
                assignment: candidate,
                unassigned: rest,
                csp,
              }))
              .unwrap();
          }
        }
      }
    },
  }
}

// TODO: parallel backtracking: https://arxiv.org/pdf/1312.7626.pdf
// TODO: AC3 optimization
