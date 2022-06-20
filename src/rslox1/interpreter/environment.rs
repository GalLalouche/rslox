use std::cell::{Ref, RefCell};
use std::collections::{HashMap, LinkedList};
use std::fmt::{Display, Formatter};
use std::ops::Deref;
use std::rc::Rc;
use std::time::SystemTime;

use crate::rslox1::ast::ScopeJumps;
use crate::rslox1::interpreter::lox_value::LoxValue;
use crate::rslox1::interpreter::lox_value::LoxValue::{Native, Number};

type Map = Rc<RefCell<HashMap<String, LoxValue>>>;

#[derive(Debug, Clone)]
pub struct Environment {
    parents: LinkedList<Map>,
    values: Map,
}

impl Environment {
    pub fn new() -> Self {
        // TODO this shouldn't be here!
        let clock = Native {
            name: "clock",
            arity: 0,
            func: |_| {
                Ok(
                    Number(
                        SystemTime::now()
                            .duration_since(SystemTime::UNIX_EPOCH)
                            .unwrap()
                            .as_secs() as f64)
                )
            },
        };
        let mut map = HashMap::new();
        map.insert("clock".to_owned(), clock);
        Environment { parents: LinkedList::new(), values: Rc::new(RefCell::new(map)) }
    }
    pub fn new_nested(&mut self) -> Environment {
        let mut parents = self.parents.clone();
        parents.push_front(self.values.clone());
        Environment { values: Rc::new(RefCell::new(HashMap::new())), parents }
    }
    pub fn get(&self, key: &str) -> Option<Ref<LoxValue>> {
        Environment::get_map(&self.values, key)
            .or_else(||
                self.parents
                    .iter()
                    .find_map(|p| Environment::get_map(p, key))
            )
    }

    pub fn get_resolved(&self, key: &str, jumps: &ScopeJumps) -> Ref<LoxValue> {
        use std::borrow::Borrow;
        assert!(jumps >= &0);
        assert!(jumps <= &self.parents.len());
        let map =
            if jumps == &0 {
                &self.values
            } else {
                self.parents.borrow().iter().nth(jumps - 1).unwrap()
            };
        Environment::get_map(&map, key).expect(
            format!("Could not find key '{}' with scope jumps '{:?}'", key, jumps).as_ref())
    }
    pub fn define(&mut self, key: String, value: LoxValue) {
        self.values.deref().borrow_mut().insert(key, value);
    }
    pub fn assign(&mut self, key: &str, value: &LoxValue) -> bool {
        Environment::assign_map(&self.values, key, value) ||
            self.parents
                .iter()
                .find(|p| Environment::assign_map(p, key, value))
                .is_some()
    }
    pub fn resolved_assign(&mut self, key: &str, value: &LoxValue, jumps: &ScopeJumps) {
        use std::borrow::{BorrowMut};
        assert!(jumps >= &0);
        let map =
            if jumps == &0 {
                &self.values
            } else {
                self.parents.borrow_mut().iter().nth(jumps - 1).unwrap()
            };
        let result = Environment::assign_map(&map, key, value);
        assert!(result, "Could not find key '{}' with scope jumps '{:?}'", key, jumps)
    }

    fn get_map<'a>(
        map: &'a Rc<RefCell<HashMap<String, LoxValue>>>, key: &str) -> Option<Ref<'a, LoxValue>> {
        Ref::filter_map(map.deref().borrow(), |map| map.get(key)).ok()
    }

    fn assign_map(map: &Rc<RefCell<HashMap<String, LoxValue>>>, key: &str, value: &LoxValue) -> bool {
        let result = map.deref().borrow().contains_key(key);
        if result {
            map.deref().borrow_mut().insert(key.into(), value.to_owned());
        }
        result
    }
}

impl Display for Environment {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let self_short: String =
            self.values
                .borrow()
                .deref()
                .iter()
                .map(|(k, v)| format!("{} -> {}", k, v.stringify()))
                .intersperse(",".into())
                .collect();
        let parents_short: String =
            self.parents
                .iter()
                .map(|p| p
                    .borrow()
                    .iter()
                    .map(|(k, v)| format!("{} -> {}", k, v.stringify()))
                    .intersperse(",,".to_owned())
                    .collect::<String>()
                )
                .intersperse(";;".into())
                .collect();
        write!(f, "{}\n{}", self_short, parents_short)
    }
}

