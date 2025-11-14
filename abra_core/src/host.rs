use crate::addons::name_of_ty;
use crate::ast::{FileAst, ItemKind, Type, TypeDefKind, TypeKind};
use crate::vm::{ValueTrait, Vm};
use crate::{ErrorSummary, FileProvider, get_files, statics};
use std::path::Path;
use std::process::Command;
use std::rc::Rc;
use utils::swrite;

// TODO: all this crap doesn't belong in lib.rs move it to addons.rs or somewhere else
pub fn generate_host_function_enum(
    main_host_func_file_name: &str,
    file_provider: Box<dyn FileProvider>,
    destination: &Path,
) -> Result<(), ErrorSummary> {
    let (file_asts, file_db) =
        get_files(&[main_host_func_file_name], &*file_provider).map_err(ErrorSummary::msg)?;
    let inference_ctx = statics::analyze(&file_asts, &file_db, file_provider)?;

    let output = &mut String::new();
    output.push_str(
        r#"// This is an auto-generated file.

use abra_core::vm::*;
use abra_core::host::*;
"#,
    );

    output.push_str(
        r#"
#[allow(dead_code)]
pub enum HostFunction {
    "#,
    );
    for f in inference_ctx.host_funcs.iter() {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        swrite!(output, "{camel_name},");
    }
    output.push_str(
        r#"
    }"#,
    );

    // conversion from integer
    output.push_str(
        r#"impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
"#,
    );
    for (i, f) in inference_ctx.host_funcs.iter().enumerate() {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        swrite!(output, "{i} => HostFunction::{camel_name},");
    }
    output.push_str("i => panic!(\"unrecognized host func: {i}\")");
    output.push_str(
        r#"}
    }}
"#,
    );

    output.push_str(
        r#"pub enum HostFunctionArgs {
    "#,
    );
    for f in &inference_ctx.host_funcs {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        let args = {
            if f.args.is_empty() {
                "".to_string()
            } else {
                let mut s = "(".to_string();
                for (i, arg) in f.args.iter().enumerate() {
                    let ty = arg.1.clone().unwrap();
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&name_of_ty(&ty));
                }
                s.push(')');
                s
            }
        };
        swrite!(output, "{camel_name}{args},");
    }
    output.push_str(
        r#"
    }
    "#,
    );

    output.push_str(
        r#"impl HostFunctionArgs {
                    "#,
    );
    output.push_str(
        r#"pub(crate) fn from_vm<Value: ValueTrait>(vm: &mut Vm<Value>, pending_host_func: u16) -> Self {
                        "#,
    );
    output.push_str("match pending_host_func {");
    for (i, f) in inference_ctx.host_funcs.iter().enumerate() {
        swrite!(output, "{i} => {{");
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        for (i, arg) in f.args.iter().enumerate().rev() {
            let ty = arg.1.clone().unwrap();
            let tyname = name_of_ty(&ty);
            swrite!(
                output,
                r#"let arg{}: {tyname} = <{tyname}>::from_vm(vm);
                            "#,
                i
            );
        }
        let args = &mut String::new();
        if !f.args.is_empty() {
            args.push('(');
            for i in 0..f.args.len() {
                if i != 0 {
                    args.push_str(", ");
                }
                swrite!(args, "arg{}", i);
            }
            args.push(')');
        }
        swrite!(output, "HostFunctionArgs::{camel_name}{args}");
        output.push('}');
    }
    output.push_str(r#"_ => panic!("unexpected tag encountered: {pending_host_func}")"#);
    output.push('}');
    output.push('}');
    output.push('}');

    output.push_str(
        r#"
pub enum HostFunctionRet {
    "#,
    );
    for f in &inference_ctx.host_funcs {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        let out = {
            match &*f.ret_type.kind {
                TypeKind::Void => "".to_string(),
                TypeKind::Tuple(elems) => {
                    let mut s = "(".to_string();
                    for (i, ty) in elems.iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&name_of_ty(ty));
                    }
                    s.push(')');
                    s
                }
                _ => {
                    format!("({})", name_of_ty(&f.ret_type))
                }
            }
        };
        swrite!(output, "{camel_name}{out},");
    }
    output.push_str(
        r#"
    }"#,
    );

    output.push_str(
        r#"impl HostFunctionRet {
                    "#,
    );
    output.push_str(
        r#"pub(crate) fn into_vm<Value: ValueTrait>(self, vm: &mut Vm<Value>,) {
                        "#,
    );
    output.push_str("match self {");
    for f in inference_ctx.host_funcs.iter() {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        let tuple_helper = |elems: &Vec<Rc<Type>>| {
            let mut s = "(".to_string();
            for i in 0..elems.len() {
                if i != 0 {
                    s.push_str(", ");
                }
                s.push_str(&format!("out{}", i));
            }
            s.push(')');
            s
        };
        let out = {
            match &*f.ret_type.kind {
                TypeKind::Void => "".to_string(),
                TypeKind::Tuple(elems) => tuple_helper(elems),
                _ => "(out)".into(),
            }
        };
        swrite!(output, "HostFunctionRet::{}{out} => {{", camel_name);
        let out_val = {
            match &*f.ret_type.kind {
                TypeKind::Void => "()".to_string(),
                TypeKind::Tuple(elems) => tuple_helper(elems),
                _ => "out".into(),
            }
        };
        swrite!(
            output,
            r#" {out_val}.to_vm(vm);
                            "#
        );
        output.push('}');
        output.push(',');
    }
    output.push('}');
    output.push_str("vm.clear_pending_host_func()");
    output.push('}');
    output.push('}');

    // TODO: this only adds from the root effects file. Need to add all types in the tree of files
    // Also, the types need to be namespaced or scoped properly if they're in child files
    add_items_from_ast(&file_asts[0], output);

    std::fs::write(destination, output).unwrap();

    Command::new("rustfmt")
        .arg(destination)
        .status()
        .map_err(|e| e.to_string())
        .map_err(ErrorSummary::msg)?;

    Ok(())
}

fn add_items_from_ast(ast: &Rc<FileAst>, output: &mut String) {
    for item in ast.items.iter() {
        if let ItemKind::TypeDef(tydef) = &*item.kind {
            match &**tydef {
                TypeDefKind::Struct(s) => {
                    swrite!(
                        output,
                        r#"pub struct {} {{
"#,
                        s.name.v
                    );
                    for field in &s.fields {
                        let tyname = name_of_ty(&field.ty);
                        swrite!(
                            output,
                            r#"pub {}: {},
"#,
                            field.name.v,
                            tyname
                        );
                    }
                    output.push('}');

                    swrite!(
                        output,
                        r#"impl<Value: ValueTrait> VmType<Value> for {} {{
"#,
                        s.name.v
                    );
                    output.push_str(
                        r#"fn from_vm<Value: ValueTrait>(vm: &mut Vm<Value>) -> Self {
"#,
                    );
                    output.push('{');
                    output.push_str("vm.deconstruct_struct();");
                    for field in s.fields.iter() {
                        if matches!(&*field.ty.kind, TypeKind::Void) {
                            output.push_str(
                                r#"vm.pop();
"#,
                            );
                        } else {
                            let tyname = name_of_ty(&field.ty);
                            swrite!(
                                output,
                                r#"let {} = <{}>::from_vm(vm);
"#,
                                field.name.v,
                                tyname
                            );
                        }
                    }
                    output.push_str(
                        r#"Self {
"#,
                    );
                    for field in &s.fields {
                        if matches!(&*field.ty.kind, TypeKind::Void) {
                            swrite!(output, "{}: (),", field.name.v);
                        } else {
                            swrite!(output, "{},", field.name.v);
                        }
                    }
                    output.push('}');
                    output.push('}');

                    output.push('}');

                    output.push_str(
                        r#"fn to_vm(self, vm: &mut Vm<Value>) {
"#,
                    );
                    output.push('{');
                    for field in s.fields.iter() {
                        if matches!(&*field.ty.kind, TypeKind::Void) {
                            output.push_str("(vm_funcs.push_nil)(vm);");
                        } else {
                            swrite!(
                                output,
                                r#"self.{}.to_vm(vm, vm_funcs);
"#,
                                field.name.v
                            );
                        }
                    }

                    swrite!(
                        output,
                        "(vm_funcs.construct_struct)(vm, {});",
                        s.fields.len()
                    );

                    output.push('}');

                    output.push('}');
                    output.push('}');
                }
                TypeDefKind::Enum(e) => {
                    swrite!(
                        output,
                        r#"pub enum {} {{
"#,
                        e.name.v
                    );
                    for variant in &e.variants {
                        swrite!(output, "{}", variant.ctor.v);
                        if let Some(ty) = &variant.data {
                            output.push('(');
                            output.push_str(&name_of_ty(ty));
                            output.push(')');
                        }
                        output.push(',');
                    }
                    output.push('}');

                    swrite!(
                        output,
                        r#"impl<Value: ValueTrait> VmType<Value> for {} {{
"#,
                        e.name.v
                    );
                    output.push_str(
                        r#"fn from_vm(vm: &mut Vm<Value>) -> Self {
"#,
                    );

                    output.push('{');
                    output.push_str("vm.deconstruct_variant();");
                    output.push_str("let tag = vm.pop_int();");
                    output.push_str("match tag {");
                    for (i, variant) in e.variants.iter().enumerate() {
                        output.push_str(&format!("{i} => {{"));
                        if let Some(ty) = &variant.data {
                            let tyname = name_of_ty(ty);
                            swrite!(
                                output,
                                r#"let value: {tyname} = <{tyname}>::from_vm(vm);
"#
                            );
                            swrite!(output, "{}::{}(value)", e.name.v, variant.ctor.v);
                        } else {
                            output.push_str("vm.pop();");
                            swrite!(output, "{}::{}", e.name.v, variant.ctor.v);
                        }
                        output.push('}');
                    }
                    output.push_str(r#"_ => panic!("unexpected tag encountered: {tag}")"#);

                    output.push('}');
                    output.push('}');

                    output.push('}');

                    output.push_str(
                        r#"fn to_vm(self, vm: &mut Vm<Value>) {
"#,
                    );
                    output.push('{');

                    output.push_str("match self {");
                    for (i, variant) in e.variants.iter().enumerate() {
                        if variant.data.is_some() {
                            swrite!(output, "{}::{}(value) => {{", e.name.v, variant.ctor.v);
                            output.push_str("value.to_vm(vm);");
                            swrite!(output, "vm.construct_variant({i});");
                        } else {
                            swrite!(output, "{}::{} => {{", e.name.v, variant.ctor.v);
                            output.push_str("vm.push_nil();");
                            swrite!(output, "vm.construct_variant({i});");
                        }
                        output.push('}');
                    }
                    output.push('}');

                    output.push('}');

                    output.push('}');
                    output.push('}');
                }
            }
        }
    }
}

pub trait VmType<Value: ValueTrait> {
    /// # Safety
    /// vm is non-null and valid
    fn from_vm(vm: &mut Vm<Value>) -> Self;

    /// # Safety
    /// vm is non-null and valid
    fn to_vm(self, vm: &mut Vm<Value>);
}

impl<Value: ValueTrait> VmType<Value> for i64 {
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        vm.pop_int()
    }

    fn to_vm(self, vm: &mut Vm<Value>) {
        vm.push_int(self);
    }
}

impl<Value: ValueTrait> VmType<Value> for f64 {
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        vm.pop_float()
    }

    fn to_vm(self, vm: &mut Vm<Value>) {
        vm.push_float(self);
    }
}

impl<Value: ValueTrait> VmType<Value> for () {
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        vm.pop();
    }

    fn to_vm(self, vm: &mut Vm<Value>) {
        vm.push_nil();
    }
}

impl<Value: ValueTrait> VmType<Value> for bool {
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        vm.pop_bool()
    }

    fn to_vm(self, vm: &mut Vm<Value>) {
        vm.push_bool(self);
    }
}

impl<Value: ValueTrait> VmType<Value> for String {
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        vm.pop().view_string(vm).to_string()
    }

    fn to_vm(self, vm: &mut Vm<Value>) {
        vm.push_str(self);
    }
}

impl<T, Value: ValueTrait> VmType<Value> for Option<T>
where
    T: VmType<Value>,
{
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        vm.deconstruct_variant();
        let tag = vm.pop_int();
        match tag {
            0 => {
                let t = T::from_vm(vm);
                Some(t)
            }
            1 => None,
            _ => panic!("unexpected tag for Option type {tag}"),
        }
    }

    fn to_vm(self, vm: &mut Vm<Value>) {
        {
            match self {
                Some(t) => {
                    t.to_vm(vm);
                    vm.construct_variant(0);
                }
                None => {
                    ().to_vm(vm);
                    vm.construct_variant(1);
                }
            }
        }
    }
}

impl<T, E, Value: ValueTrait> VmType<Value> for Result<T, E>
where
    T: VmType<Value>,
    E: VmType<Value>,
{
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        vm.deconstruct_variant();
        let tag = vm.pop_int();
        match tag {
            0 => {
                let t = T::from_vm(vm);
                Ok(t)
            }
            1 => {
                let e = E::from_vm(vm);
                Err(e)
            }
            _ => panic!("unexpected tag for Result type {tag}"),
        }
    }

    fn to_vm(self, vm: &mut Vm<Value>) {
        {
            match self {
                Ok(t) => {
                    t.to_vm(vm);
                    vm.construct_variant(0);
                }
                Err(e) => {
                    e.to_vm(vm);
                    vm.construct_variant(1);
                }
            }
        }
    }
}

impl<T, Value: ValueTrait> VmType<Value> for Vec<T>
where
    T: VmType<Value>,
{
    fn from_vm(vm: &mut Vm<Value>) -> Self {
        {
            let len = vm.array_len();
            vm.deconstruct_array();
            let mut ret = vec![];
            for _ in 0..len {
                let val = <T>::from_vm(vm);
                ret.push(val);
            }
            ret
        }
    }
    fn to_vm(self, vm: &mut Vm<Value>) {
        {
            let len = self.len();
            for elem in self.into_iter() {
                elem.to_vm(vm);
            }
            vm.construct_array(len);
        }
    }
}

macro_rules! replace_expr {
    ($t:tt, $e:expr_2021) => {
        $e
    };
}

macro_rules! tuple_impls {
    ( $( $name:ident ),+ $(,)? ) => {
        impl< Value: ValueTrait, $($name: VmType<Value>),+ > VmType<Value> for ( $($name,)+ ) {
            fn from_vm(vm: &mut Vm<Value>) -> Self {
                // Deconstruct the tuple on the VM.
                vm.deconstruct_struct();
                // Pop values in normal order.
                #[allow(non_snake_case)]
                let ($($name,)+) = ($( $name::from_vm(vm), )+);
                ($($name,)+)
            }
            fn to_vm(self, vm: &mut Vm<Value>) {
                // Destructure the tuple.
                #[allow(non_snake_case)]
                let ($($name,)+) = self;
                // Push each element onto the VM in order.
                $( $name.to_vm(vm); )+
                // Count the number of elements in the tuple.
                let count: usize = [$( replace_expr!($name, 1) ),+].len();
                // Reconstruct the tuple on the VM.
                vm.construct_struct(count);
            }
        }
    };
}

tuple_impls!(A);
tuple_impls!(A, B);
tuple_impls!(A, B, C);
tuple_impls!(A, B, C, D);
tuple_impls!(A, B, C, D, E);
tuple_impls!(A, B, C, D, E, F);
tuple_impls!(A, B, C, D, E, F, G);
tuple_impls!(A, B, C, D, E, F, G, H);
tuple_impls!(A, B, C, D, E, F, G, H, I);
tuple_impls!(A, B, C, D, E, F, G, H, I, J);
tuple_impls!(A, B, C, D, E, F, G, H, I, J, K);
tuple_impls!(A, B, C, D, E, F, G, H, I, J, K, L);
