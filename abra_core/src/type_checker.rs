use types::Type;
type Constraint = (Type, Type);

type Identifier = String;
struct Assumption {
    id: Identifier,
    typ: Type
}
struct Context {
    assumptions: Vec<Assumption>
}

impl Context {
    fn lookup(&self, id: &Identifier) -> Option<Type> {
        for &a in self.assumptions {
            if a.id == id {
                return Some(a.typ);
            }
        }
        return None;
    }

    fn extend(&self, a: Assumption) {
    }
}

pub fn syn(ctx: &Context, e: Box<parse_tree::Expr>) -> (Type, Vec<Constraint>) {
    match e {
        Var(s) -> 
    }
}