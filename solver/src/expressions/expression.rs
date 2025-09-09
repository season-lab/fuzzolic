use anyhow::Result;
use std::collections::{HashMap, HashSet};
use serde::{Serialize, Deserialize};

/// OPKIND enum matching exactly the C symbolic-struct.h definition
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum OpKind {
    Reserved = 0,
    IsConst = 1,
    IsSymbolic = 2,
    // Unary
    Neg = 3,
    Not = 4,
    // Binary
    Add = 5,
    Sub = 6,
    Mul = 7,
    Mulu = 8,
    Div = 9,
    Divu = 10,
    Rem = 11,
    Remu = 12,
    And = 13,
    Or = 14,
    Xor = 15,
    Shl = 16,
    Shr = 17,
    Sar = 18,
    Sal = 19,
    Rotl = 20,
    Rotr = 21,
    // Comparison
    Eq = 22,
    Ne = 23,
    Lt = 24,
    Le = 25,
    Ge = 26,
    Gt = 27,
    Ltu = 28,
    Leu = 29,
    Geu = 30,
    Gtu = 31,
    // Extensions
    Zext = 32,
    Sext = 33,
    // Concatenation and extraction
    Concat = 34,
    Concat8L = 35,
    Concat8R = 36,
    Extract8 = 37,
    Extract = 38,
    // Ternary
    Deposit = 39,
    QzExtract = 40,
    QsExtract = 41,
    QzExtract2 = 42,
    // Bit operations
    Ctz = 43,
    Clz = 44,
    Bswap = 45,
    Rcl = 46,
    Andc = 47,
    // Conditional
    Ite = 48,
    IteEqZero = 49,
    IteNeZero = 50,
    Or3 = 51,
    Xor3 = 52,
    // XMM operations
    Pmovmskb = 53,
    CmpEq = 54,
    CmpGt = 55,
    CmpGe = 56,
    CmpLe = 57,
    CmpLt = 58,
    Min = 59,
    Max = 60,
    SignedSaturation = 61,
    UnsignedSaturation = 62,
    Nand = 63,
    // Double operations
    MulHigh = 64,
    MuluHigh = 65,
    // EFLAGS operations (66-86)
    EflagsAllAdd = 66,
    EflagsAllAdcb = 67,
    EflagsAllAdcw = 68,
    EflagsAllAdcl = 69,
    EflagsAllAdcq = 70,
    EflagsAllSub = 71,
    EflagsAllMul = 72,
    EflagsAllSbbb = 73,
    EflagsAllSbbw = 74,
    EflagsAllSbbl = 75,
    EflagsAllSbbq = 76,
    EflagsAllLogic = 77,
    EflagsAllInc = 78,
    EflagsAllDec = 79,
    EflagsAllShl = 80,
    EflagsAllSar = 81,
    EflagsAllBmilg = 82,
    EflagsAllAdcx = 83,
    EflagsAllAdox = 84,
    EflagsAllAdcox = 85,
    EflagsAllRcl = 86,
    // EFLAGS C operations (87-100)
    EflagsCAdd = 87,
    EflagsCAdcb = 88,
    EflagsCAdcw = 89,
    EflagsCAdcl = 90,
    EflagsCAdcq = 91,
    EflagsCSub = 92,
    EflagsCMul = 93,
    EflagsCSbbb = 94,
    EflagsCSbbw = 95,
    EflagsCSbbl = 96,
    EflagsCSbbq = 97,
    EflagsCLogic = 98,
    EflagsCShl = 99,
    EflagsCBmilg = 100,
    // Symbolic operations
    SymbolicPc = 101,
    SymbolicJumpTableAccess = 102,
    MemorySlice = 103,
    MemorySliceAccess = 104,
    MemoryInputSliceAccess = 105,
    SymbolicLoad = 106,
    SymbolicStore = 107,
    MemoryConcretization = 108,
    ConsistencyCheck = 109,
    InputSlice = 110,
    // Movement
    Mov = 111,
    // Model
    Model = 112,
}

impl TryFrom<u8> for OpKind {
    type Error = anyhow::Error;
    
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(OpKind::Reserved),
            1 => Ok(OpKind::IsConst),
            2 => Ok(OpKind::IsSymbolic),
            3 => Ok(OpKind::Neg),
            4 => Ok(OpKind::Not),
            5..=100 => Ok(match value {
                5 => OpKind::Add,
                6 => OpKind::Sub,
                7 => OpKind::Mul,
                8 => OpKind::Mulu,
                9 => OpKind::Div,
                10 => OpKind::Divu,
                11 => OpKind::Rem,
                12 => OpKind::Remu,
                13 => OpKind::And,
                14 => OpKind::Or,
                15 => OpKind::Xor,
                16 => OpKind::Shl,
                17 => OpKind::Shr,
                18 => OpKind::Sar,
                19 => OpKind::Sal,
                20 => OpKind::Rotl,
                21 => OpKind::Rotr,
                22 => OpKind::Eq,
                23 => OpKind::Ne,
                24 => OpKind::Lt,
                25 => OpKind::Le,
                26 => OpKind::Ge,
                27 => OpKind::Gt,
                28 => OpKind::Ltu,
                29 => OpKind::Leu,
                30 => OpKind::Geu,
                31 => OpKind::Gtu,
                32 => OpKind::Zext,
                33 => OpKind::Sext,
                34 => OpKind::Concat,
                35 => OpKind::Concat8L,
                36 => OpKind::Concat8R,
                37 => OpKind::Extract8,
                38 => OpKind::Extract,
                39 => OpKind::Deposit,
                40 => OpKind::QzExtract,
                41 => OpKind::QsExtract,
                42 => OpKind::QzExtract2,
                43 => OpKind::Ctz,
                44 => OpKind::Clz,
                45 => OpKind::Bswap,
                46 => OpKind::Rcl,
                47 => OpKind::Andc,
                48 => OpKind::Ite,
                49 => OpKind::IteEqZero,
                50 => OpKind::IteNeZero,
                51 => OpKind::Or3,
                52 => OpKind::Xor3,
                53 => OpKind::Pmovmskb,
                54 => OpKind::CmpEq,
                55 => OpKind::CmpGt,
                56 => OpKind::CmpGe,
                57 => OpKind::CmpLe,
                58 => OpKind::CmpLt,
                59 => OpKind::Min,
                60 => OpKind::Max,
                61 => OpKind::SignedSaturation,
                62 => OpKind::UnsignedSaturation,
                63 => OpKind::Nand,
                64 => OpKind::MulHigh,
                65 => OpKind::MuluHigh,
                66 => OpKind::EflagsAllAdd,
                67 => OpKind::EflagsAllAdcb,
                68 => OpKind::EflagsAllAdcw,
                69 => OpKind::EflagsAllAdcl,
                70 => OpKind::EflagsAllAdcq,
                71 => OpKind::EflagsAllSub,
                72 => OpKind::EflagsAllMul,
                73 => OpKind::EflagsAllSbbb,
                74 => OpKind::EflagsAllSbbw,
                75 => OpKind::EflagsAllSbbl,
                76 => OpKind::EflagsAllSbbq,
                77 => OpKind::EflagsAllLogic,
                78 => OpKind::EflagsAllInc,
                79 => OpKind::EflagsAllDec,
                80 => OpKind::EflagsAllShl,
                81 => OpKind::EflagsAllSar,
                82 => OpKind::EflagsAllBmilg,
                83 => OpKind::EflagsAllAdcx,
                84 => OpKind::EflagsAllAdox,
                85 => OpKind::EflagsAllAdcox,
                86 => OpKind::EflagsAllRcl,
                87 => OpKind::EflagsCAdd,
                88 => OpKind::EflagsCAdcb,
                89 => OpKind::EflagsCAdcw,
                90 => OpKind::EflagsCAdcl,
                91 => OpKind::EflagsCAdcq,
                92 => OpKind::EflagsCSub,
                93 => OpKind::EflagsCMul,
                94 => OpKind::EflagsCSbbb,
                95 => OpKind::EflagsCSbbw,
                96 => OpKind::EflagsCSbbl,
                97 => OpKind::EflagsCSbbq,
                98 => OpKind::EflagsCLogic,
                99 => OpKind::EflagsCShl,
                100 => OpKind::EflagsCBmilg,
                _ => unreachable!(),
            }),
            101..=112 => Ok(match value {
                101 => OpKind::SymbolicPc,
                102 => OpKind::SymbolicJumpTableAccess,
                103 => OpKind::MemorySlice,
                104 => OpKind::MemorySliceAccess,
                105 => OpKind::MemoryInputSliceAccess,
                106 => OpKind::SymbolicLoad,
                107 => OpKind::SymbolicStore,
                108 => OpKind::MemoryConcretization,
                109 => OpKind::ConsistencyCheck,
                110 => OpKind::InputSlice,
                111 => OpKind::Mov,
                112 => OpKind::Model,
                _ => unreachable!(),
            }),
            _ => anyhow::bail!("Invalid OpKind value: {}", value),
        }
    }
}

/// EXTENDKIND enum matching C definition
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExtendKind {
    Zext8 = 0,
    Zext16 = 1,
    Zext32 = 2,
    Sext8 = 3,
    Sext16 = 4,
    Sext32 = 5,
}

/// MODEL_T enum matching C definition
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModelType {
    Strcmp = 0,
    Strlen = 1,
    Memchr = 2,
    Memcmp = 3,
    Malloc = 4,
    Calloc = 5,
    Realloc = 6,
}

/// C-compatible Expr struct matching symbolic-struct.h exactly
#[repr(C)]
#[derive(Debug, Clone)]
pub struct Expr {
    pub op1: *mut Expr,
    pub op2: *mut Expr,
    pub op3: *mut Expr,
    pub opkind: u8,
    pub op1_is_const: u8,
    pub op2_is_const: u8,
    pub op3_is_const: u8,
}

/// Ergonomic representation of an operand for `Expr`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    /// The operand is encoded as an immediate constant stored in the pointer
    Const(usize),
    /// The operand is a pointer to another `Expr` node
    Node(*mut Expr),
    /// No operand present (null pointer and not a const)
    Empty,
}

impl Operand {
    #[inline]
    pub fn is_const(self) -> bool { matches!(self, Operand::Const(_)) }

    #[inline]
    pub fn as_const(self) -> Option<usize> {
        if let Operand::Const(v) = self { Some(v) } else { None }
    }

    #[inline]
    pub fn as_ptr(self) -> Option<*mut Expr> {
        if let Operand::Node(p) = self { Some(p) } else { None }
    }
}

/// QueryArgs8 struct matching generated C header (4 bytes arg0..arg3)
#[repr(C)]
#[derive(Default, Debug, Clone, Copy)]
pub struct QueryArgs8 {
    pub arg0: u8,
    pub arg1: u8,
    pub arg2: u8,
    pub arg3: u8,
}

/// Query union args matching C definition
#[repr(C)]
pub union QueryArgs {
    pub args8: std::mem::ManuallyDrop<QueryArgs8>,
    pub args64: usize,
    pub args16: QueryArgs16,
    pub model: ModelType,
}

/// QueryArgs16 struct for packed arguments
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct QueryArgs16 {
    pub index: u16,
    pub count: u16,
    pub index_inv: u16,
    pub count_inv: u16,
}

/// Query structure matching C definition
/// Layout mirrors C (symbolic-struct.h):
/// struct Query { Expr* query; uintptr_t address; union { ... } args; };
#[repr(C)]
pub struct Query {
    pub query: *mut Expr,
    pub address: usize,
    pub args: QueryArgs,
}

impl Expr {
    /// Create a new constant expression
    pub fn new_const(value: usize) -> Self {
        Self {
            op1: value as *mut Expr,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsConst as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Create a new symbolic input expression
    pub fn new_symbolic(input_id: usize) -> Self {
        Self {
            op1: input_id as *mut Expr,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: OpKind::IsSymbolic as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Create a new binary expression
    pub fn new_binary(opkind: OpKind, op1: *mut Expr, op2: *mut Expr) -> Self {
        Self {
            op1,
            op2,
            op3: std::ptr::null_mut(),
            opkind: opkind as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }    
    /// Create a new unary expression
    pub fn new_unary(opkind: OpKind, op1: *mut Expr) -> Self {
        Self {
            op1,
            op2: std::ptr::null_mut(),
            op3: std::ptr::null_mut(),
            opkind: opkind as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Create a new ternary expression
    pub fn new_ternary(opkind: OpKind, op1: *mut Expr, op2: *mut Expr, op3: *mut Expr) -> Self {
        Self {
            op1,
            op2,
            op3,
            opkind: opkind as u8,
            op1_is_const: 0,
            op2_is_const: 0,
            op3_is_const: 0,
        }
    }
    
    /// Set operand as constant
    pub fn set_op1_const(&mut self, value: usize) {
        self.op1 = value as *mut Expr;
        self.op1_is_const = 1;
    }
    
    pub fn set_op2_const(&mut self, value: usize) {
        self.op2 = value as *mut Expr;
        self.op2_is_const = 1;
    }
    
    pub fn set_op3_const(&mut self, value: usize) {
        self.op3 = value as *mut Expr;
        self.op3_is_const = 1;
    }
    
    /// Get constant value from operand
    pub fn get_op1_const(&self) -> Option<usize> {
        if self.op1_is_const != 0 {
            Some(self.op1 as usize)
        } else {
            None
        }
    }
    
    pub fn get_op2_const(&self) -> Option<usize> {
        if self.op2_is_const != 0 {
            Some(self.op2 as usize)
        } else {
            None
        }
    }
    
    pub fn get_op3_const(&self) -> Option<usize> {
        if self.op3_is_const != 0 {
            Some(self.op3 as usize)
        } else {
            None
        }
    }
    
    /// Get operand size for operand at given index
    pub fn get_operand_size(&self, operand_index: usize) -> usize {
        match operand_index {
            0 => self.op1 as usize,
            1 => self.op2 as usize, 
            2 => self.op3 as usize,
            _ => 0,
        }
    }

    // =========================
    // Auxiliary ergonomic helpers
    // =========================

    /// Convert raw `opkind` byte to strongly-typed `OpKind`.
    #[inline]
    pub fn try_opkind(&self) -> Result<OpKind> { OpKind::try_from(self.opkind) }

    /// Check if the expression has the specified operation kind.
    #[inline]
    pub fn opkind_is(&self, k: OpKind) -> bool { self.opkind == k as u8 }

    /// Whether this node is a constant (`OpKind::IsConst`) with an embedded value.
    #[inline]
    pub fn is_const_node(&self) -> bool { self.opkind == OpKind::IsConst as u8 && self.op1_is_const != 0 }

    /// Constant value for `IsConst` nodes, if available.
    #[inline]
    pub fn const_value(&self) -> Option<usize> { if self.is_const_node() { Some(self.op1 as usize) } else { None } }

    /// Whether this node represents a symbolic input (`OpKind::IsSymbolic`).
    #[inline]
    pub fn is_symbolic_node(&self) -> bool { self.opkind == OpKind::IsSymbolic as u8 }

    /// Get operand 1 as an ergonomic `Operand` (Const/Node/Empty).
    #[inline]
    pub fn op1_operand(&self) -> Operand {
        if self.op1_is_const != 0 { Operand::Const(self.op1 as usize) }
        else if self.op1.is_null() { Operand::Empty } else { Operand::Node(self.op1) }
    }

    /// Get operand 2 as an ergonomic `Operand` (Const/Node/Empty).
    #[inline]
    pub fn op2_operand(&self) -> Operand {
        if self.op2_is_const != 0 { Operand::Const(self.op2 as usize) }
        else if self.op2.is_null() { Operand::Empty } else { Operand::Node(self.op2) }
    }

    /// Get operand 3 as an ergonomic `Operand` (Const/Node/Empty).
    #[inline]
    pub fn op3_operand(&self) -> Operand {
        if self.op3_is_const != 0 { Operand::Const(self.op3 as usize) }
        else if self.op3.is_null() { Operand::Empty } else { Operand::Node(self.op3) }
    }

    /// Indexed accessor for operands: 0->op1, 1->op2, 2->op3
    #[inline]
    pub fn operand(&self, idx: usize) -> Operand {
        match idx { 0 => self.op1_operand(), 1 => self.op2_operand(), 2 => self.op3_operand(), _ => Operand::Empty }
    }

    /// Borrow operand 1 as `&Expr` if it is a node pointer (non-const and non-null).
    #[inline]
    pub fn op1_ref(&self) -> Option<&Expr> {
        self.op_ref(self.op1_is_const, self.op1)
    }

    /// Borrow operand 2 as `&Expr` if it is a node pointer (non-const and non-null).
    #[inline]
    pub fn op2_ref(&self) -> Option<&Expr> {
        self.op_ref(self.op2_is_const, self.op2)
    }

    /// Borrow operand 3 as `&Expr` if it is a node pointer (non-const and non-null).
    #[inline]
    pub fn op3_ref(&self) -> Option<&Expr> {
        self.op_ref(self.op3_is_const, self.op3)
    }

    /// Internal helper to convert a raw operand pointer into a shared reference safely.
    /// Returns None for const operands or null pointers.
    #[inline]
    fn op_ref<'a>(&'a self, is_const: u8, ptr: *mut Expr) -> Option<&'a Expr> {
        if is_const != 0 || ptr.is_null() { return None; }
        // Guard against immediates encoded without the const flag: only deref
        // pointers that lie within the shared expression pool address space.
        let ptr_val = ptr as usize;
        let pool_base = crate::shared_memory::shared_memory::EXPR_POOL_ADDR as usize;
        if ptr_val < pool_base { return None; }
        // SAFETY: The shared memory producer guarantees that non-const operands
        // are valid pointers to Expr nodes during the solver's processing window.
        // We expose only an immutable borrow to prevent mutation.
        unsafe { Some(&*ptr) }
    }

    /// Central helper: with-borrow API for a raw operand pointer.
    /// Executes `f` with a shared reference to the node if the pointer is non-null and not a const-immediate.
    #[inline]
    pub fn with_operand_ref_from_raw<T, F: FnOnce(&Expr) -> T>(is_const: u8, ptr: *mut Expr, f: F) -> Option<T> {
        if is_const != 0 || ptr.is_null() { return None; }
        // Only deref pointers that are in the shared pool; treat tiny raw values as immediates.
        let ptr_val = ptr as usize;
        let pool_base = crate::shared_memory::shared_memory::EXPR_POOL_ADDR as usize;
        if ptr_val < pool_base { return None; }
        // SAFETY: pointer originates from shared memory; we only take an immutable reference scoped to `f`.
        unsafe { Some(f(&*ptr)) }
    }

    /// Central helper: with-borrow API for a raw node pointer (not a const-immediate).
    /// Executes `f` with a shared reference to the node if the pointer is non-null.
    #[inline]
    pub fn with_ref_from_ptr<T, F: FnOnce(&Expr) -> T>(ptr: *const Expr, f: F) -> Option<T> {
        if ptr.is_null() { return None; }
        // SAFETY: pointer originates from shared memory; immutable reference scoped to `f`.
        unsafe { Some(f(&*ptr)) }
    }

    /// Convenience: set operand 1 as a node pointer and clear its const flag.
    #[inline]
    pub fn set_op1_expr(&mut self, ptr: *mut Expr) { self.op1 = ptr; self.op1_is_const = 0; }

    /// Convenience: set operand 2 as a node pointer and clear its const flag.
    #[inline]
    pub fn set_op2_expr(&mut self, ptr: *mut Expr) { self.op2 = ptr; self.op2_is_const = 0; }

    /// Convenience: set operand 3 as a node pointer and clear its const flag.
    #[inline]
    pub fn set_op3_expr(&mut self, ptr: *mut Expr) { self.op3 = ptr; self.op3_is_const = 0; }

    /// Utility: pack two u32 values into a pointer-sized immediate (used by some encodings, e.g., Extract ranges).
    #[inline]
    pub fn pack_u32_pair_to_ptr(high: u32, low: u32) -> *mut Expr {
        let v = ((high as u64) << 32) | (low as u64);
        v as usize as *mut Expr
    }

    /// Utility: unpack two u32 values from a pointer-sized immediate produced by `pack_u32_pair_to_ptr`.
    #[inline]
    pub fn unpack_u32_pair_from_ptr(ptr: *mut Expr) -> (u32, u32) {
        let v = ptr as usize as u64;
        let high = (v >> 32) as u32;
        let low = (v & 0xFFFF_FFFF) as u32;
        (high, low)
    }
}

/// Expression pool for managing shared expressions
pub struct ExprPool {
    expressions: Vec<Expr>,
    capacity: usize,
}

impl ExprPool {
    pub fn new(capacity: usize) -> Self {
        Self {
            expressions: Vec::with_capacity(capacity),
            capacity,
        }
    }
    
    pub fn add_expr(&mut self, expr: Expr) -> Result<usize> {
        if self.expressions.len() >= self.capacity {
            anyhow::bail!("Expression pool is full");
        }
        
        let id = self.expressions.len();
        self.expressions.push(expr);
        Ok(id)
    }
    
    pub fn get_expr(&self, id: usize) -> Option<&Expr> {
        self.expressions.get(id)
    }
    
    pub fn len(&self) -> usize {
        self.expressions.len()
    }
}

/// Dependency tracking for expressions
#[derive(Debug, Clone)]
pub struct Dependency {
    pub inputs: HashSet<usize>,
    pub expressions: HashSet<usize>,
}

impl Dependency {
    pub fn new() -> Self {
        Self {
            inputs: HashSet::new(),
            expressions: HashSet::new(),
        }
    }
    
    pub fn add_input(&mut self, input_id: usize) {
        self.inputs.insert(input_id);
    }
    
    pub fn add_expression(&mut self, expr_id: usize) {
        self.expressions.insert(expr_id);
    }
    
    pub fn merge(&mut self, other: &Dependency) {
        self.inputs.extend(&other.inputs);
        self.expressions.extend(&other.expressions);
    }
}

/// Dependency graph for tracking expression relationships
pub struct DependencyGraph {
    dependencies: HashMap<usize, Dependency>,
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            dependencies: HashMap::new(),
        }
    }
    
    pub fn add_dependency(&mut self, input_id: usize, expr_id: usize) {
        let dep = self.dependencies.entry(input_id).or_insert_with(Dependency::new);
        dep.add_expression(expr_id);
    }
    
    pub fn get_dependency(&self, input_id: usize) -> Option<&Dependency> {
        self.dependencies.get(&input_id)
    }
    
    pub fn merge_dependencies(&self, inputs: &HashSet<usize>) -> Dependency {
        let mut merged = Dependency::new();
        
        for &input_id in inputs {
            merged.add_input(input_id);
            if let Some(dep) = self.dependencies.get(&input_id) {
                merged.merge(dep);
            }
        }
        
        merged
    }
}

impl Query {
    pub fn new() -> Self {
        Query {
            query: std::ptr::null_mut(),
            address: 0,
            args: QueryArgs { args8: std::mem::ManuallyDrop::new(QueryArgs8::default()) },
        }
    }
    
    pub fn get_index(&self) -> usize {
        self.args64()
    }

    /// Return the underlying expression pointer as an immutable reference if present.
    #[inline]
    pub fn query_expr(&self) -> Option<&Expr> {
        if self.query.is_null() { None } else { unsafe { Some(&*self.query) } }
    }

    /// Read the 64-bit args union view (copy out). Unsafe is encapsulated here.
    #[inline]
    pub fn args64(&self) -> usize {
        unsafe { self.args.args64 }
    }

    /// Overwrite the args union with a 64-bit value.
    #[inline]
    pub fn set_args64(&mut self, v: usize) {
        self.args = QueryArgs { args64: v };
    }

    /// Read the 8x u8 args as a copy. Safe wrapper around union read.
    #[inline]
    pub fn args8_copy(&self) -> QueryArgs8 {
        // SAFETY: read a copy of the ManuallyDrop-wrapped value without moving/dropping the original
        let md: std::mem::ManuallyDrop<QueryArgs8> = unsafe { std::ptr::read(&self.args.args8) };
        std::mem::ManuallyDrop::into_inner(md)
    }

    /// Read the args16 view (idx,count,idx_inv,count_inv) as a copy
    #[inline]
    pub fn args16_copy(&self) -> QueryArgs16 {
        // SAFETY: QueryArgs is a union; args16 is POD and we read a copy
        unsafe { std::ptr::read(&self.args.args16) }
    }

    /// Set the 8x u8 args; wraps the union write safely.
    #[inline]
    pub fn set_args8(&mut self, a: QueryArgs8) {
        self.args = QueryArgs { args8: std::mem::ManuallyDrop::new(a) };
    }

    /// Read the model discriminator from the union.
    #[inline]
    pub fn model(&self) -> ModelType {
        unsafe { self.args.model }
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}
