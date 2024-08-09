use alloc::{format, string::String, vec, vec::Vec};
use core::fmt::{Debug, Display};

#[derive(Clone)]
pub struct Model<State, Transition>
where
    State: Display + Clone + Eq + Debug,
    Transition: Display + Clone + Eq + Debug,
{
    states: Vec<State>,
    transitions: Vec<(State, Transition, State)>,
    current_state: State,
}

impl<State, Transition> Model<State, Transition>
where
    State: Display + Clone + Eq + Debug,
    Transition: Display + Clone + Eq + Debug,
{
    pub(crate) fn new(
        initial_state: State,
        states: Vec<State>,
        transitions: Vec<(State, Transition, State)>,
    ) -> Self {
        let model = Model {
            current_state: initial_state,
            states,
            transitions,
        };
        model.validate();
        model
    }

    fn validate(&self) {
        let mut visited = vec![];
        for (src, edge, dest) in &self.transitions {
            for st in [src, dest] {
                if !visited.contains(st) {
                    visited.push(st.clone());
                }
                if !self.states.contains(st) {
                    log::debug!(
                        "Warning: an invalid state is found in the transition function\n  state: {:?}\n  transition: {:?} --{:?}--> {:?}",
                        st, src, edge, dest
                    );
                }
            }
        }
        for st in &self.states {
            if !visited.contains(st) {
                log::debug!(
                    "Warning: a not-used state is found in the state set: {:?}",
                    st
                );
            }
        }
    }

    pub fn next(&mut self, symbol: &Transition) -> Result<State, String> {
        let dests: Vec<State> = self
            .transitions
            .iter()
            .filter(|(src, tr, _)| *src == self.current_state && *tr == *symbol)
            .map(|(_, _, dest)| dest.clone())
            .collect();
        if dests.len() == 1 {
            let dest_st = dests[0].clone();
            // log::debug!(
            //     "[RV] {} ---- {} ---> {}",
            //     self.current_state,
            //     symbol,
            //     dest_st.clone()
            // );
            self.current_state = dest_st.clone();
            Ok(dest_st)
        } else {
            Err(format!(
                "Error: an invalid transition is found.\r\n  current state: {}\r\n  symbol: {}",
                self.current_state, symbol
            ))
        }
    }
}
