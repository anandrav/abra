/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{EnumDef, StructDef, Type, TypeKind, VariantField};
use std::rc::Rc;
use utils::swrite;

#[derive(Clone, Copy)]
pub(crate) enum BindingFlavor {
    Host,
    Foreign,
}

impl BindingFlavor {
    fn trait_name(self) -> &'static str {
        match self {
            BindingFlavor::Host => "VmType",
            BindingFlavor::Foreign => "VmFfiType",
        }
    }

    fn vm_from_sig(self) -> &'static str {
        match self {
            BindingFlavor::Host => "fn from_vm(vm: &mut VmGreenThread) -> Self",
            BindingFlavor::Foreign => {
                "unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self"
            }
        }
    }

    fn to_vm_sig(self) -> &'static str {
        match self {
            BindingFlavor::Host => "fn to_vm(self, vm: &mut VmGreenThread)",
            BindingFlavor::Foreign => {
                "unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions)"
            }
        }
    }

    fn open_body(self, output: &mut String) {
        match self {
            BindingFlavor::Host => output.push('{'),
            BindingFlavor::Foreign => output.push_str("unsafe {"),
        }
    }

    fn deconstruct_struct(self, output: &mut String) {
        match self {
            BindingFlavor::Host => output.push_str("vm.deconstruct_struct();"),
            BindingFlavor::Foreign => output.push_str("(vm_funcs.deconstruct_struct)(vm);"),
        }
    }

    fn construct_struct(self, output: &mut String, arity: usize) {
        match self {
            BindingFlavor::Host => swrite!(output, "vm.construct_struct({arity});"),
            BindingFlavor::Foreign => swrite!(output, "(vm_funcs.construct_struct)(vm, {arity});"),
        }
    }

    fn deconstruct_variant(self, output: &mut String) {
        match self {
            BindingFlavor::Host => output.push_str("vm.deconstruct_variant();"),
            BindingFlavor::Foreign => output.push_str("(vm_funcs.deconstruct_variant)(vm);"),
        }
    }

    fn construct_variant(self, output: &mut String, tag: usize) {
        match self {
            BindingFlavor::Host => swrite!(output, "vm.construct_variant({tag});"),
            BindingFlavor::Foreign => swrite!(output, "(vm_funcs.construct_variant)(vm, {tag});"),
        }
    }

    fn pop_int(self, output: &mut String) {
        match self {
            BindingFlavor::Host => output.push_str("vm.pop_int()"),
            BindingFlavor::Foreign => output.push_str("(vm_funcs.pop_int)(vm)"),
        }
    }

    fn pop_discard(self, output: &mut String) {
        match self {
            BindingFlavor::Host => output.push_str("vm.pop();"),
            BindingFlavor::Foreign => output.push_str("(vm_funcs.pop)(vm);"),
        }
    }

    fn push_dummy(self, output: &mut String) {
        match self {
            BindingFlavor::Host => output.push_str("vm.push_int(0);"),
            BindingFlavor::Foreign => output.push_str("(vm_funcs.push_int)(vm, 0);"),
        }
    }

    fn vm_from_call(self, output: &mut String, tyname: &str) {
        match self {
            BindingFlavor::Host => swrite!(output, "<{tyname}>::from_vm(vm)"),
            BindingFlavor::Foreign => swrite!(output, "<{tyname}>::from_vm_unsafe(vm, vm_funcs)"),
        }
    }

    fn to_vm_call(self, output: &mut String, value: &str) {
        match self {
            BindingFlavor::Host => swrite!(output, "{value}.to_vm(vm);"),
            BindingFlavor::Foreign => swrite!(output, "{value}.to_vm_unsafe(vm, vm_funcs);"),
        }
    }
}

pub(crate) fn emit_struct_def(output: &mut String, s: &StructDef, flavor: BindingFlavor) {
    swrite!(
        output,
        r#"#[allow(dead_code)]
pub struct {} {{
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
        r#"impl {} for {} {{
"#,
        flavor.trait_name(),
        s.name.v
    );
    swrite!(output, "{} {{", flavor.vm_from_sig());
    flavor.open_body(output);
    flavor.deconstruct_struct(output);
    for field in s.fields.iter() {
        if !matches!(&*field.ty.kind, TypeKind::Void) {
            let tyname = name_of_ty(&field.ty);
            swrite!(output, "let {}: {tyname} = ", field.name.v);
            flavor.vm_from_call(output, &tyname);
            output.push(';');
        }
    }
    output.push_str("Self {");
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

    swrite!(output, "{} {{", flavor.to_vm_sig());
    flavor.open_body(output);
    for field in s.fields.iter() {
        if !matches!(&*field.ty.kind, TypeKind::Void) {
            flavor.to_vm_call(output, &format!("self.{}", field.name.v));
        }
    }

    let nfields = s
        .fields
        .iter()
        .filter(|field| !matches!(&*field.ty.kind, TypeKind::Void))
        .count();
    flavor.construct_struct(output, nfields);

    output.push('}');
    output.push('}');
    output.push('}');
}

pub(crate) fn emit_enum_def(output: &mut String, e: &EnumDef, flavor: BindingFlavor) {
    swrite!(
        output,
        r#"#[allow(dead_code)]
pub enum {} {{
"#,
        e.name.v
    );
    for variant in &e.variants {
        swrite!(output, "{}", variant.ctor.v);
        if !variant.fields.is_empty() {
            output.push('(');
            output.push_str(&name_of_variant_data_ty(&variant.fields));
            output.push(')');
        }
        output.push(',');
    }
    output.push('}');

    swrite!(
        output,
        r#"impl {} for {} {{
"#,
        flavor.trait_name(),
        e.name.v
    );
    swrite!(output, "{} {{", flavor.vm_from_sig());
    flavor.open_body(output);
    flavor.deconstruct_variant(output);
    output.push_str("let tag = ");
    flavor.pop_int(output);
    output.push(';');
    output.push_str("match tag {");
    for (i, variant) in e.variants.iter().enumerate() {
        swrite!(output, "{i} => {{");
        if !variant.fields.is_empty() {
            let tyname = name_of_variant_data_ty(&variant.fields);
            swrite!(output, "let value: {tyname} = ");
            flavor.vm_from_call(output, &tyname);
            output.push(';');
            swrite!(output, "{}::{}(value)", e.name.v, variant.ctor.v);
        } else {
            flavor.pop_discard(output);
            swrite!(output, "{}::{}", e.name.v, variant.ctor.v);
        }
        output.push('}');
    }
    output.push_str(r#"_ => panic!("unexpected tag encountered: {tag}")"#);
    output.push('}');
    output.push('}');
    output.push('}');

    swrite!(output, "{} {{", flavor.to_vm_sig());
    flavor.open_body(output);
    output.push_str("match self {");
    for (i, variant) in e.variants.iter().enumerate() {
        if !variant.fields.is_empty() {
            swrite!(output, "{}::{}(value) => {{", e.name.v, variant.ctor.v);
            flavor.to_vm_call(output, "value");
            flavor.construct_variant(output, i);
        } else {
            swrite!(output, "{}::{} => {{", e.name.v, variant.ctor.v);
            flavor.push_dummy(output);
            flavor.construct_variant(output, i);
        }
        output.push('}');
    }
    output.push('}');
    output.push('}');
    output.push('}');
    output.push('}');
}

pub(crate) fn name_of_variant_data_ty(elems: &[VariantField]) -> String {
    if elems.is_empty() {
        panic!("variant data is empty. You probably didn't mean to call it.")
    }
    let mut ret = "".to_string();
    if elems.len() == 1 {
        ret.push_str(&name_of_ty(&elems[0].ty));
        return ret;
    }
    ret.push('(');
    for (i, elem) in elems.iter().enumerate() {
        if i != 0 {
            ret.push(',');
        }
        ret.push_str(&name_of_ty(&elem.ty));
    }
    ret.push(')');
    ret
}

pub(crate) fn name_of_ty(ty: &Rc<Type>) -> String {
    match &*ty.kind {
        TypeKind::Bool => "bool".to_string(),
        TypeKind::Float => "f64".to_string(),
        TypeKind::Int => "AbraInt".to_string(),
        TypeKind::Str => "String".to_string(),
        TypeKind::Void => "()".to_string(),
        TypeKind::Tuple(elems) => {
            let mut s = "(".to_string();
            for elem in elems {
                s.push_str(&name_of_ty(elem));
                s.push(',');
            }
            s.push(')');
            s
        }
        TypeKind::NamedWithParams {
            package: _,
            name: ident,
            params,
        } => {
            let mut s = ident.v.clone();
            if s == "option" {
                s = "Option".into();
            } else if s == "array" {
                s = "Vec".into();
            } else if s == "result" {
                s = "Result".into();
            }
            s.push('<');
            for param in params {
                s.push_str(&name_of_ty(param));
                s.push(',');
            }
            s.push('>');
            s
        }
        TypeKind::Wildcard => "WildcardNotSupported".into(),
        TypeKind::Function(..) => "FunctionNotSupported".into(),
        TypeKind::Poly(..) => "PolyNotSupported".into(),
    }
}

pub(crate) fn run_formatter(output_path: &str, skip_children: bool) {
    let mut cmd = std::process::Command::new("rustfmt");
    cmd.arg("+nightly");
    if skip_children {
        cmd.arg("--unstable-features").arg("--skip-children");
    }
    cmd.arg(output_path);
    let status = cmd.status();
    match status {
        Ok(status) => {
            if !status.success() {
                println!(
                    "cargo:warning=Failed to format {output_path}. {}. command: rustfmt {output_path}",
                    status
                );
            }
        }
        Err(e) => {
            println!(
                "cargo:warning=Failed to format {output_path}. error={}. command: rustfmt {output_path}",
                e
            );
        }
    }
}
