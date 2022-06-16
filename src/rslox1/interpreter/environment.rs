use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::mem;
use std::time::SystemTime;

use crate::rslox1::interpreter::lox_value::LoxValue;
use crate::rslox1::interpreter::lox_value::LoxValue::{Native, Number};

#[derive(Debug)]
pub struct Environment {
    parent: Option<Box<Environment>>,
    values: HashMap<String, LoxValue>,
}

impl Environment {
    pub fn new() -> Self {
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
        let mut values = HashMap::new();
        values.insert("clock".to_owned(), clock);
        Environment { parent: None, values }
    }
    pub fn nest(&mut self) {
        let parent = Some(Box::new(Environment {
            parent: mem::take(&mut self.parent),
            values: mem::take(&mut self.values),
        }));
        self.parent = parent
    }
    pub fn unnest(&mut self) {
        match self.parent.as_deref_mut() {
            None => panic!("Cannot unnest if parent doesn't exist"),
            Some(p) => {
                self.values = mem::take(&mut p.values);
                self.parent = mem::take(&mut p.parent);
            }
        }
    }
    pub fn get(&self, key: &str) -> Option<&LoxValue> {
        self.values.get(key).or_else(|| self.parent.as_deref().and_then(|p| p.get(key)))
    }
    pub fn define(&mut self, key: String, value: LoxValue) {
        self.values.insert(key, value);
    }
    pub fn assign(&mut self, key: String, value: LoxValue) -> bool {
        if self.values.contains_key(&key) {
            self.values.insert(key, value);
            true
        } else {
            self.parent.as_deref_mut().map(|p| p.assign(key, value)).unwrap_or(false)
        }
    }
}

impl Display for Environment {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let self_short: String = self.values.borrow()
            .into_iter()
            .map(|(k, v)| format!("{} -> {}", k, v.stringify()))
            .intersperse("\t\n".to_owned())
            .collect();
        write!(f, "{}", self_short)
    }
}

