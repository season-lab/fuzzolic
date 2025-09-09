// C-ABI mirror types strictly to drive cbindgen with tracer-compatible names
// Do NOT use these types at runtime in Rust; they are for header generation only.

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct CQueryArgs8 {
    pub arg0: u8,
    pub arg1: u8,
    pub arg2: u8,
    pub arg3: u8,
}

#[allow(non_camel_case_types)]
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub enum CExtendKind {
    ZEXT_8 = 0,
    ZEXT_16 = 1,
    ZEXT_32 = 2,
    SEXT_8 = 3,
    SEXT_16 = 4,
    SEXT_32 = 5,
}
