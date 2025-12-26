use crate::ast::{FileAst, ImportList, ItemKind, Type, TypeDefKind, TypeKind};
use crate::foreign_bindings::{name_of_ty, run_formatter};
use crate::statics::{Declaration, StaticsContext};
use crate::vm::{AbraInt, Vm};
use crate::{ErrorSummary, FileProvider, get_files, statics};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::rc::Rc;
use utils::hash::{HashMap, HashSet};
use utils::swrite;

pub fn generate_host_function_enum(
    main_host_func_file_name: &str,
    file_provider: Box<dyn FileProvider>,
    destination: &Path,
) -> Result<(), ErrorSummary> {
    let mut ctx = StaticsContext::new(file_provider);
    let file_asts = get_files(&mut ctx, &[main_host_func_file_name]);
    statics::analyze(&mut ctx, &file_asts)?;

    // TODO: this only adds from the root effects file. Need to add all types in the tree of files
    // Also, the types need to be namespaced or scoped properly if they're in child files
    let destination = destination.join("generated");
    if fs::exists(&destination).unwrap() {
        fs::remove_dir_all(&destination).unwrap();
    }
    fs::create_dir(&destination).unwrap();

    // TODO: populate child modules
    // let mut path_to_ast = HashMap::default();

    // let mut child_modules = HashMap::default();

    let mut root_namespace = Namespace::new();

    for file_ast in &file_asts {
        let mut main_file_package = PathBuf::from(main_host_func_file_name);
        main_file_package.set_extension("");
        let path = if file_ast.package_name_str == "prelude"
            || file_ast.package_name_str == main_file_package.to_str().unwrap()
        {
            PathBuf::new()
        } else {
            file_ast.package_name.clone()
        };

        root_namespace.add(&path, file_ast.clone());
        // add_to_child_modules(file_ast, &mut child_modules, main_host_func_file_name);
        // path_to_ast.insert(file_ast.package_name_str.clone(), file_ast.clone());
    }

    generate_file_per_namespace(&root_namespace, &destination, true, &mut ctx);

    // panic!();
    //
    // add_items_from_ast(&file_asts[0], output, &child_modules, main_host_func_file_name);
    // for (parent, children) in child_modules.iter() {
    //     for child in children {
    //         println!("add_items_from_ast()");
    //         println!("parent=`{}`, child=`{}`", parent, child);
    //
    //         if child == "prelude" {
    //             continue;
    //         }
    //
    //         let path = parent.to_owned() + "/" + child;
    //
    //         let lookup = if child == main_host_func_file_name { "" } else { &path };
    //
    //         if let Some(children) = child_modules.get(lookup) {
    //             for child in children {
    //                 swrite!(output, "pub mod {};\n", child);
    //             }
    //         }
    //
    //         let path = parent.to_owned() + "/" + child;
    //         if let Some(file_ast) = path_to_ast.get(&path) {
    //             add_items_from_ast(file_ast, output, &child_modules, main_host_func_file_name);
    //         } else {
    //             swrite!(output, "")
    //         }
    //     }
    // }

    // add_items_from_ast(&file_asts[0], output, &child_modules, main_host_func_file_name);
    // for file_ast in &file_asts[1..] {
    //     if file_ast.package_name_str == "prelude" {
    //         continue;
    //     }
    //     println!("path = {}", file_ast.absolute_path.display());
    //     println!("name = {}", file_ast.package_name.display());
    //     let mut destination = destination.join(&file_ast.package_name);
    //     destination.set_extension("rs");
    //     println!("output path = {}", destination.display());
    //     let mut output = String::new();
    //     add_items_from_ast(file_ast, &mut output, &child_modules, main_host_func_file_name);
    //     // // TODO: remove the unwraps
    //     let parent = destination.parent().unwrap();
    //     fs::create_dir_all(parent).unwrap();
    //     fs::write(destination, output).unwrap();
    // }
    // panic!(); // TODO LAST HERE

    // {
    //     let destination = destination.join("mod.rs");
    //     fs::write(&destination, output).unwrap();
    // }

    let destination = destination.join("mod.rs");
    run_formatter(destination.to_str().unwrap(), false);
    // panic!();

    Ok(())
}

fn generate_host_args_and_ret(ctx: &StaticsContext, output: &mut String) {
    output.push_str(
        r#"
#[allow(dead_code)]
pub enum HostFunction {
    "#,
    );
    for f in ctx.host_funcs.iter() {
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
    for (i, f) in ctx.host_funcs.iter().enumerate() {
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
    for f in &ctx.host_funcs {
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
        r#"pub(crate) fn from_vm(vm: &mut Vm, pending_host_func: u16) -> Self {
                        "#,
    );
    output.push_str("match pending_host_func {");
    for (i, f) in ctx.host_funcs.iter().enumerate() {
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
    for f in &ctx.host_funcs {
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
        r#"pub(crate) fn into_vm(self, vm: &mut Vm,) {
                        "#,
    );
    output.push_str("match self {");
    for f in ctx.host_funcs.iter() {
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
                TypeKind::Tuple(elems) => tuple_helper(elems),
                _ => "out".into(),
            }
        };
        if *f.ret_type.kind != TypeKind::Void {
            swrite!(
                output,
                r#" {out_val}.to_vm(vm);
                            "#
            );
        }
        output.push('}');
        output.push(',');
    }
    output.push('}');
    output.push_str("vm.clear_pending_host_func()");
    output.push('}');
    output.push('}');
}

fn emit_header(output: &mut String) {
    output.push_str(
        r#"// This is @generated by Abra build system

use abra_core::vm::*;
use abra_core::host_bindings::*;
"#,
    );
}

fn generate_file_per_namespace(
    ns: &Namespace,
    destination: &Path,
    root: bool,
    ctx: &StaticsContext,
) {
    // println!("generating file for destination = {}", destination.display());
    let mut output = String::new();
    emit_header(&mut output);

    if root {
        generate_host_args_and_ret(&ctx, &mut output);
    }
    for (child_name, child_ns) in &ns.namespaces {
        swrite!(&mut output, "pub mod {child_name};\n");

        let child_destination = destination.join(child_name);
        generate_file_per_namespace(&child_ns, &child_destination, false, ctx);
    }
    for file_ast in &ns.files {
        add_items_from_ast(file_ast, &mut output);
    }

    let destination = if root {
        destination.join("mod.rs")
    } else {
        destination.with_added_extension("rs")
    };

    // let file = destination.join("mod.rs");
    // let mut destination = destination.join(&file_ast.package_name);
    // destination.set_extension("rs");
    // println!("output path = {}", file.display());
    // // // TODO: remove the unwraps
    let parent = destination.parent().unwrap();
    fs::create_dir_all(parent).unwrap();
    fs::write(destination, output).unwrap();
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Namespace {
    files: HashSet<Rc<FileAst>>,
    namespaces: HashMap<String, Box<Namespace>>,
}

impl Namespace {
    pub fn new() -> Self {
        Self::default()
    }

    fn add(&mut self, path: &Path, file_ast: Rc<FileAst>) {
        let segments: Vec<_> = path.components().rev().collect();
        self.add_(&segments, file_ast);
    }

    fn add_(&mut self, segments: &[Component], file_ast: Rc<FileAst>) {
        if segments.is_empty() {
            self.files.insert(file_ast);
        } else {
            let last = segments.last().unwrap();
            let last = last.as_os_str().to_str().unwrap().to_string();
            self.namespaces
                .entry(last)
                .or_default()
                .add_(&segments[0..segments.len() - 1], file_ast);
        }
    }
}

// fn add_to_child_modules(file_ast: &Rc<FileAst>, child_modules: &mut HashMap<String, Vec<String>>, main_host_func_file_name: &str) {
//     let package_name = &file_ast.package_name;
//     let child = package_name.file_name().unwrap().to_str().unwrap().to_owned(); // TODO: this rigamarole is really annoying....
//     if child == "prelude" || child == main_host_func_file_name {
//         return;
//     }
//     let parent = package_name.parent().unwrap().to_str().unwrap().to_owned(); // TODO: this rigamarole is really annoying....
//     println!("parent=`{}, child={}`", parent, child);
//
//     child_modules.entry(parent).or_default().push(child);
// }

fn add_items_from_ast(ast: &Rc<FileAst>, output: &mut String) {
    for item in ast.items.iter() {
        match &*item.kind {
            ItemKind::TypeDef(tydef) => {
                match tydef {
                    TypeDefKind::Struct(s) if s.attributes.iter().any(|a| a.is_host()) => {
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
                            r#"impl VmType for {} {{
       "#,
                            s.name.v
                        );
                        output.push_str(
                            r#"fn from_vm(vm: &mut Vm) -> Self {
"#,
                        );
                        output.push('{');
                        output.push_str("vm.deconstruct_struct();");
                        for field in s.fields.iter() {
                            if matches!(&*field.ty.kind, TypeKind::Void) {
                                //                             output.push_str(
                                //                                 r#"vm.pop();
                                // "#,
                                //                             );
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
                            r#"fn to_vm(self, vm: &mut Vm) {
"#,
                        );
                        output.push('{');
                        for field in s.fields.iter() {
                            if matches!(&*field.ty.kind, TypeKind::Void) {
                                // output.push_str("(vm_funcs.push_int)(vm, 0);"); // TODO: remove need for this dummy value
                            } else {
                                swrite!(
                                    output,
                                    r#"self.{}.to_vm(vm);
       "#,
                                    field.name.v
                                );
                            }
                        }

                        swrite!(output, "vm.construct_struct({});", s.fields.len());

                        output.push('}');

                        output.push('}');
                        output.push('}');
                    }
                    TypeDefKind::Enum(e) if e.attributes.iter().any(|a| a.is_host()) => {
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
                            r#"impl VmType for {} {{
       "#,
                            e.name.v
                        );
                        output.push_str(
                            r#"fn from_vm(vm: &mut Vm) -> Self {
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
                            r#"fn to_vm(self, vm: &mut Vm) {
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
                                output.push_str("vm.push_int(0);"); // TODO: remove need for this dummy value
                                swrite!(output, "vm.construct_variant({i});");
                            }
                            output.push('}');
                        }
                        output.push('}');

                        output.push('}');

                        output.push('}');
                        output.push('}');
                    }
                    _ => {}
                }
            }
            ItemKind::Import(ident, import_list) => {
                let module_name = &ident.v.replace("/", "::");
                match import_list {
                    Some(ImportList::Inclusion(includes)) => {
                        swrite!(output, "use crate::{}::{{", module_name);
                        for (i, include) in includes.iter().enumerate() {
                            if i != 0 {
                                swrite!(output, ", ");
                            }
                            swrite!(output, "{}", include.v);
                        }
                        swrite!(output, "}};\n");
                    }
                    Some(ImportList::Exclusion(..)) => unimplemented!(), // TODO: calculate inclusion list. Right now it would just be set difference. May change in the future with re-exports
                    None => {
                        // glob import
                        swrite!(output, "use crate::{}::*;\n", module_name);
                    }
                }
                /* TODO last here. emit things like
                    pub mod util_helper  }
                    use util_helper      }    <--- not sure if this is ideal, play it by ear
                    pub mod more_stuff   }
                    use more_stuff::*    }
                */

                // TODO: for the mod declarations, just create a tree of modules ahead of time. Then when writing the output per file, just add a `pub mod` for all its direct descendants

                // TODO: for the use statements, mirror the structure of the Abra import. If import_list = None, do a glob import. If it's an inclusion list, include using {}
                // TODO: if it's an exception list..... that has to be converted to an inclusion list, which sucks :/ but it must be done.
                // output.push_str(format!(""))
            }
            _ => {}
        }
    }
}

pub trait VmType {
    /// # Safety
    /// vm is non-null and valid
    fn from_vm(vm: &mut Vm) -> Self;

    /// # Safety
    /// vm is non-null and valid
    fn to_vm(self, vm: &mut Vm);
}

impl VmType for AbraInt {
    fn from_vm(vm: &mut Vm) -> Self {
        vm.pop_int()
    }

    fn to_vm(self, vm: &mut Vm) {
        vm.push_int(self);
    }
}

impl VmType for f64 {
    fn from_vm(vm: &mut Vm) -> Self {
        vm.pop_float()
    }

    fn to_vm(self, vm: &mut Vm) {
        vm.push_float(self);
    }
}

impl VmType for bool {
    fn from_vm(vm: &mut Vm) -> Self {
        vm.pop_bool()
    }

    fn to_vm(self, vm: &mut Vm) {
        vm.push_bool(self);
    }
}

impl VmType for String {
    fn from_vm(vm: &mut Vm) -> Self {
        vm.pop().view_string(vm).to_string()
    }

    fn to_vm(self, vm: &mut Vm) {
        vm.push_str(self);
    }
}

impl<T> VmType for Option<T>
where
    T: VmType,
{
    fn from_vm(vm: &mut Vm) -> Self {
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

    fn to_vm(self, vm: &mut Vm) {
        {
            match self {
                Some(t) => {
                    t.to_vm(vm);
                    vm.construct_variant(0);
                }
                None => {
                    // TODO: remove need for this dummy value
                    let nil: AbraInt = 0;
                    nil.to_vm(vm);
                    vm.construct_variant(1);
                }
            }
        }
    }
}

impl<T, E> VmType for Result<T, E>
where
    T: VmType,
    E: VmType,
{
    fn from_vm(vm: &mut Vm) -> Self {
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

    fn to_vm(self, vm: &mut Vm) {
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

impl<T> VmType for Vec<T>
where
    T: VmType,
{
    fn from_vm(vm: &mut Vm) -> Self {
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
    fn to_vm(self, vm: &mut Vm) {
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
        impl<$($name: VmType),+ > VmType for ( $($name,)+ ) {
            fn from_vm(vm: &mut Vm) -> Self {
                // Deconstruct the tuple on the VM.
                vm.deconstruct_struct();
                // Pop values in normal order.
                #[allow(non_snake_case)]
                let ($($name,)+) = ($( $name::from_vm(vm), )+);
                ($($name,)+)
            }
            fn to_vm(self, vm: &mut Vm) {
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
