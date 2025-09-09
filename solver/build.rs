use std::env;
use std::path::PathBuf;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    
    // Configure Z3 to use the forked version from fuzzy-sat
    let z3_path = PathBuf::from(&manifest_dir).join("fuzzy-sat/fuzzolic-z3");
    let z3_build_path = z3_path.join("build");
    let z3_header_path = z3_path.join("src/api/z3.h");
    
    // Set environment variables for Z3 build
    println!("cargo:rustc-env=Z3_SYS_Z3_HEADER={}", z3_header_path.display());
    println!("cargo:rustc-env=Z3_SYS_Z3_LIB_DIR={}", z3_build_path.display());
    
    // Link search paths for forked Z3
    println!("cargo:rustc-link-search=native={}", z3_build_path.display());
    // Link fuzzy solver static library (libZ3Fuzzy.a)
    let fuzzy_lib_dir = PathBuf::from(&manifest_dir).join("fuzzy-sat");
    println!("cargo:rustc-link-search=native={}", fuzzy_lib_dir.display());
    println!("cargo:rustc-link-lib=static=Z3Fuzzy");
    // Also link libz3 dynamically (provided by fork build directory). It contains custom symbols like Z3_custom_eval_depth.
    println!("cargo:rustc-link-lib=dylib=z3");
    
    // Link against system libraries that were used in the C version
    println!("cargo:rustc-link-lib=dylib=glib-2.0");
    
    // Build our local C bridge to the fuzzy solver API
    let mut cc_build = cc::Build::new();
    cc_build
        .file("src/solver/fuzzy/fuzz_bridge.c")
        // include project root so #include "fuzzy-sat/z3-fuzzy.h" resolves
        .include(&manifest_dir)
        // include Z3 headers for <z3.h>
        .include(z3_path.join("src/api"));
    cc_build.compile("fuzz_bridge");
    
    // Rerun if libraries change
    println!("cargo:rerun-if-changed=fuzzy-sat/libZ3Fuzzy.a");
    println!("cargo:rerun-if-changed=fuzzy-sat/fuzzolic-z3/build/libz3.a");
    println!("cargo:rerun-if-changed=fuzzy-sat/fuzzolic-z3/src/api/z3.h");

    // Generate C header from Rust definitions using cbindgen
    let header_out_dir = PathBuf::from(&manifest_dir).join("include");
    std::fs::create_dir_all(&header_out_dir).ok();
    let header_path = header_out_dir.join("fuzzolic_generated.h");
    let crate_dir = PathBuf::from(&manifest_dir);
    let _ = cbindgen::Builder::new()
        .with_crate(crate_dir)
        .with_config(cbindgen::Config::from_file(PathBuf::from(&manifest_dir).join("cbindgen.toml")).unwrap())
        .with_language(cbindgen::Language::C)
        .with_include_guard("FUZZOLIC_GENERATED_H")
        .generate()
        .expect("Unable to generate C bindings with cbindgen")
        .write_to_file(&header_path);

    // Post-process header to add tracer-compatible QueryArgs16 and Query with anonymous union
    if let Ok(hdr) = std::fs::read_to_string(&header_path) {
        let injection = r#"
/* === Injected to match tracer/tcg/symbolic/symbolic-struct.h === */
typedef struct QueryArgs16 {
  uint16_t index;
  uint16_t count;
  uint16_t index_inv;
  uint16_t count_inv;
} QueryArgs16;

typedef struct Query {
  Expr*     query;
  uintptr_t address;
  union {
    QueryArgs8 args8;
    uintptr_t  args64;
    MODEL_T    model;
    struct {
      uint16_t index;
      uint16_t count;
      uint16_t index_inv;
      uint16_t count_inv;
    } args16;
  };
} Query;
/* === End injected === */
"#;
        // Insert before closing include guard
        if let Some(pos) = hdr.rfind("#endif") {
            let (head, tail) = hdr.split_at(pos);
            let mut new_hdr = String::with_capacity(hdr.len() + injection.len());
            new_hdr.push_str(head);
            new_hdr.push_str(injection);
            new_hdr.push_str(tail);
            let _ = std::fs::write(&header_path, new_hdr);
        }
    }

    // Rerun if Rust definitions change (that impact header)
    println!("cargo:rerun-if-changed=src/expressions/expression.rs");
    println!("cargo:rerun-if-changed=src/expressions/mod.rs");
}
