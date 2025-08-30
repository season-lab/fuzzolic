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
    
    // Only link fuzzy solver if explicitly requested
    // For now, disable fuzzy solver linking to avoid undefined references
    // The fuzzy solver library has missing symbols that need to be resolved
    println!("cargo:warning=Fuzzy solver disabled - requires additional symbol resolution");
    
    // Link against system libraries that were used in the C version
    println!("cargo:rustc-link-lib=dylib=glib-2.0");
    
    // Rerun if libraries change
    println!("cargo:rerun-if-changed=fuzzy-sat/libZ3Fuzzy.a");
    println!("cargo:rerun-if-changed=fuzzy-sat/fuzzolic-z3/build/libz3.a");
    println!("cargo:rerun-if-changed=fuzzy-sat/fuzzolic-z3/src/api/z3.h");
}
