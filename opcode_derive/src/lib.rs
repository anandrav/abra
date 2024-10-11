extern crate proc_macro;
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, Data, DeriveInput, Fields};

#[proc_macro_derive(Opcode)]
pub fn opcode_derive(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    // Extract the enum data
    let variants = if let Data::Enum(data_enum) = input.data {
        data_enum.variants
    } else {
        panic!("Opcode derive macro only works on enums");
    };

    let mut opcode_arms = Vec::new();
    let mut encode_arms = Vec::new();
    let mut decode_arms = Vec::new();
    let mut size_arms = Vec::new();

    // Counter for assigning opcodes automatically
    let mut opcode_counter = 0u8;

    // Iterate over each variant in the enum
    for variant in variants {
        let variant_name = variant.ident;
        let opcode_literal = opcode_counter;
        opcode_counter += 1; // Increment opcode counter for each variant

        // Handle the case where the variant has fields
        match variant.fields {
            Fields::Unit => {
                // No fields, simple encoding/decoding, and size is just 1 byte (for opcode)
                opcode_arms.push(quote! {
                    #name::#variant_name => #opcode_literal
                });
                encode_arms.push(quote! {
                    #name::#variant_name => vec![#opcode_literal],
                });
                decode_arms.push(quote! {
                    #opcode_literal => Ok(#name::#variant_name),
                });
                size_arms.push(quote! {
                    #name::#variant_name => 1,  // 1 byte for opcode
                });
            }
            Fields::Unnamed(ref fields) => {
                // Unnamed fields (tuple-like)
                let field_sizes = fields.unnamed.iter().map(|f| {
                    let ty = &f.ty;
                    quote! {
                        std::mem::size_of::<#ty>()
                    }
                });

                // Create encoding logic for tuple-like variants
                let encode_logic = fields.unnamed.iter().enumerate().map(|(i, _)| {
                    quote! {
                        bytes.extend(&self.#i.to_le_bytes());
                    }
                });

                // Create decoding logic with dynamic field names
                let decode_logic = fields.unnamed.iter().enumerate().map(|(i, ty)| {
                    let field_var = format_ident!("field_{}", i);
                    quote! {
                        let #field_var = <#ty>::from_le_bytes([
                            bytes[start_idx + 1], bytes[start_idx + 2], bytes[start_idx + 3], bytes[start_idx + 4]
                        ]);
                    }
                });

                opcode_arms.push(quote! {
                    #name::#variant_name(_) => #opcode_literal
                });

                encode_arms.push(quote! {
                    #name::#variant_name(ref fields) => {
                        let mut bytes = vec![#opcode_literal];
                        #(#encode_logic)*
                        bytes
                    }
                });

                decode_arms.push(quote! {
                    #opcode_literal => {
                        #(#decode_logic)*
                        Ok(#name::#variant_name(field_0))  // Adjust based on field count if needed
                    }
                });

                // Add size calculation for this variant
                size_arms.push(quote! {
                    #name::#variant_name(_) => 1 + #(#field_sizes)+*,  // 1 byte for opcode + size of each field
                });
            }
            Fields::Named(ref fields) => {
                // Named fields (struct-like)
                let field_names: Vec<_> = fields.named.iter().map(|f| &f.ident).collect();
                let field_types: Vec<_> = fields.named.iter().map(|f| &f.ty).collect();

                opcode_arms.push(quote! {
                    #name::#variant_name { .. } => #opcode_literal
                });

                // Calculate the total size of the fields (arguments)
                let field_sizes = field_types.iter().map(|ty| {
                    quote! {
                        std::mem::size_of::<#ty>()
                    }
                });

                // Create encoding logic for named fields
                let encode_logic = field_names.iter().zip(field_types.iter()).map(|(name, _)| {
                    quote! {
                        bytes.extend(&self.#name.to_le_bytes());
                    }
                });

                // Create decoding logic for named fields
                let decode_logic = field_names.iter().zip(field_types.iter()).map(|(name, ty)| {
                    quote! {
                        let #name = <#ty>::from_le_bytes([
                            bytes[start_idx + 1], bytes[start_idx + 2], bytes[start_idx + 3], bytes[start_idx + 4]
                        ]);
                    }
                });

                encode_arms.push(quote! {
                    #name::#variant_name { #(#field_names),* } => {
                        let mut bytes = vec![#opcode_literal];
                        #(#encode_logic)*
                        bytes
                    }
                });

                decode_arms.push(quote! {
                    #opcode_literal => {
                        #(#decode_logic)*
                        Ok(#name::#variant_name { #(#field_names),* })
                    }
                });

                // Add size calculation for this variant
                size_arms.push(quote! {
                    #name::#variant_name { .. } => 1 + #(#field_sizes)+*,  // 1 byte for opcode + size of each field
                });
            }
        }
    }

    // Generate the final implementation
    let expanded = quote! {
        impl #name {
            pub fn opcode(&self) -> u8 {
                match self {
                    #(#opcode_arms),*
                }
            }

            pub fn encode(&self) -> Vec<u8> {
                match self {
                    #(#encode_arms),*
                }
            }

            pub fn decode(bytes: &[u8]) -> Result<Self, String> {
                let opcode = bytes[0];
                let start_idx = 0; // Update this if needed for more complex instructions
                match opcode {
                    #(#decode_arms),*,
                    _ => Err(format!("Unknown opcode: {}", opcode)),
                }
            }

            pub fn size(&self) -> usize {
                match self {
                    #(#size_arms),*
                }
            }
        }
    };

    // Convert the generated code into a TokenStream and return it
    TokenStream::from(expanded)
}

