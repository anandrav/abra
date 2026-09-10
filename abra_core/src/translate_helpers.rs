use crate::environment::Environment;
use crate::statics::{Declaration, PolytypeDeclaration};
use crate::statics::{FuncResolutionKind, Type};

pub(crate) type MonomorphEnv = Environment<PolytypeDeclaration, Type>;

impl MonomorphEnv {
    pub(crate) fn update(&self, overloaded_ty: &Type, monomorphic_ty: &Type) {
        match (overloaded_ty, monomorphic_ty) {
            // recurse
            (Type::Function(args, out), Type::Function(args2, out2)) => {
                for i in 0..args.len() {
                    self.update(&args[i], &args2[i]);
                }
                self.update(out, out2);
            }
            (Type::Nominal(ident, params), Type::Nominal(ident2, params2)) => {
                assert_eq!(ident, ident2);
                for i in 0..params.len() {
                    self.update(&params[i], &params2[i]);
                }
            }
            (Type::Poly(polyty), _) => {
                self.extend(polyty.clone(), monomorphic_ty.clone());
            }
            (Type::Tuple(elems1), Type::Tuple(elems2)) => {
                for i in 0..elems1.len() {
                    self.update(&elems1[i], &elems2[i]);
                }
            }
            _ => {}
        }
    }
}

impl Type {
    pub(crate) fn subst(&self, monomorphic_env: &MonomorphEnv) -> Type {
        match self {
            Type::Function(args, out) => {
                let new_args = args.iter().map(|arg| arg.subst(monomorphic_env)).collect();
                let new_out = out.subst(monomorphic_env);
                Type::Function(new_args, Box::new(new_out))
            }
            Type::Nominal(ident, params) => {
                let new_params = params
                    .iter()
                    .map(|param| param.subst(monomorphic_env))
                    .collect();
                Type::Nominal(ident.clone(), new_params)
            }
            Type::Poly(polyty) => {
                if let Some(monomorphic_ty) = monomorphic_env.lookup(polyty) {
                    monomorphic_ty
                } else {
                    self.clone()
                }
            }
            Type::Tuple(elems) => {
                let new_elems = elems
                    .iter()
                    .map(|elem| elem.subst(monomorphic_env))
                    .collect();
                Type::Tuple(new_elems)
            }
            _ => self.clone(),
        }
    }
}
