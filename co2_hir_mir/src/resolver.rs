use std::collections::HashSet;

#[derive(Default)]
pub(crate) struct Resolver {
    type_names: HashSet<String>,
}

impl Resolver {
    pub(crate) fn new() -> Self {
        let mut r = Resolver::default();
        r.type_names.insert("int".to_owned());
        r.type_names.insert("char".to_owned());
        r.type_names.insert("void".to_owned());
        r
    }

    pub(crate) fn register_typedef(&mut self, name: &str) {
        self.type_names.insert(name.to_owned());
    }

    pub(crate) fn register_use(&mut self, path: &str) {
        let last = path.rsplit("::").next().unwrap_or(path);
        self.type_names.insert(last.to_owned());
        self.type_names.insert(path.to_owned());
    }
}
