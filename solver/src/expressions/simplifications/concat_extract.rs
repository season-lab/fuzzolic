use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use crate::expressions::arena::tls_alloc_opt;
use super::{SimplificationRule, infer_size};

/// Pack k adjacent 8-bit slices over the same structural base
pub struct ConcatExtractPackGeneralRule;

impl SimplificationRule for ConcatExtractPackGeneralRule {
    fn name(&self) -> &str { "ConcatExtractPackGeneral" }
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        use crate::expressions::expression::OpKind as K;
        if !expr.opkind_is(K::Concat) { return Ok(expr.clone()); }

        fn flatten_concat<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
            if e.opkind_is(K::Concat) {
                if let Some(l) = e.safe_op1_ref() { flatten_concat(l, out); }
                if let Some(r) = e.safe_op2_ref() { flatten_concat(r, out); }
            } else {
                out.push(e);
            }
        }
        fn structural_eq(a: &Expr, b: &Expr, depth: usize) -> bool {
            if std::ptr::eq(a, b) { return true; }
            if depth > 64 { return false; }
            if a.opkind != b.opkind || a.op1_is_const != b.op1_is_const || a.op2_is_const != b.op2_is_const || a.op3_is_const != b.op3_is_const { return false; }
            // Compare immediates directly
            if a.op1_is_const != 0 && a.op1 != b.op1 { return false; }
            if a.op2_is_const != 0 && a.op2 != b.op2 { return false; }
            if a.op3_is_const != 0 && a.op3 != b.op3 { return false; }
            // Recurse on node children
            let ok1 = match (a.safe_op1_ref(), b.safe_op1_ref()) { (Some(x), Some(y)) => structural_eq(x, y, depth+1), (None, None) => true, _ => false };
            if !ok1 { return false; }
            let ok2 = match (a.safe_op2_ref(), b.safe_op2_ref()) { (Some(x), Some(y)) => structural_eq(x, y, depth+1), (None, None) => true, _ => false };
            if !ok2 { return false; }
            let ok3 = match (a.safe_op3_ref(), b.safe_op3_ref()) { (Some(x), Some(y)) => structural_eq(x, y, depth+1), (None, None) => true, _ => false };
            ok3
        }

        let mut items: Vec<&Expr> = Vec::new();
        flatten_concat(expr, &mut items);
        if items.len() < 2 { return Ok(expr.clone()); }

        // Convert each item into (base_expr, high, low) if it's Extract or Extract8 with 8-bit width
        let mut triplets: Vec<(&Expr, u32, u32)> = Vec::with_capacity(items.len());
        for (i, it) in items.iter().enumerate() {
            if it.opkind_is(K::Extract8) {
                let base = if let Some(b) = it.safe_op1_ref() { b } else { return Ok(expr.clone()); };
                let idx = it.op2 as u32; // immediate index
                let low = idx * 8; let high = low + 7;
                triplets.push((base, high, low));
            } else if it.opkind_is(K::Extract) {
                let base = if let Some(b) = it.safe_op1_ref() { b } else { return Ok(expr.clone()); };
                let (high, low) = Expr::unpack_u32_pair_from_ptr(it.op2);
                if high + 1 != low + 8 { return Ok(expr.clone()); } // only accept 8-bit chunks
                triplets.push((base, high, low));
            } else {
                return Ok(expr.clone());
            }
            // Validate alignment
            if (triplets[i].2 % 8) != 0 { return Ok(expr.clone()); }
        }

        // All bases must be structurally equal
        let base0 = triplets[0].0;
        for (b, _, _) in &triplets {
            if !structural_eq(base0, b, 0) { return Ok(expr.clone()); }
        }

        // Check they form a contiguous descending sequence: leftmost has highest byte
        // E.g., bytes [n-1, n-2, ..., 0]
        triplets.sort_by(|a,b| b.1.cmp(&a.1)); // sort descending by high
        // After sort, verify consecutive
        for w in triplets.windows(2) {
            let (_, h1, l1) = w[0];
            let (_, h2, l2) = w[1];
            if l1 != l2 + 8 || h1 != h2 + 8 { return Ok(expr.clone()); }
        }

        let low = triplets.last().unwrap().2;
        let high = triplets.first().unwrap().1;
        // Build Extract(base0, high:low) or identity if full width
        if let Some(w) = infer_size(base0) {
            if low == 0 && high + 1 == w { return Ok(base0.clone()); }
        }
        let packed = Expr::pack_u32_pair_to_ptr(high, low);
        Ok(Expr { op1: base0 as *const Expr as *mut Expr, op2: packed, op3: std::ptr::null_mut(), opkind: K::Extract as u8, op1_is_const: 0, op2_is_const: 1, op3_is_const: 0 })
    }

    fn priority(&self) -> u32 { 133 }
}

/// Pack runs of adjacent 8-bit Extract/Extract8 items over the same base within a Concat
/// into a single wider Extract, preserving order and allowing other items between runs.
pub struct ConcatExtractPackRunsRule;

impl SimplificationRule for ConcatExtractPackRunsRule {
    fn name(&self) -> &str { "ConcatExtractPackRuns" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        use crate::expressions::expression::OpKind as K;
        if !expr.opkind_is(K::Concat) { return Ok(expr.clone()); }

        // Flatten concat tree in-order
        fn flatten_concat<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
            if e.opkind_is(K::Concat) {
                if let Some(l) = e.safe_op1_ref() { flatten_concat(l, out); }
                if let Some(r) = e.safe_op2_ref() { flatten_concat(r, out); }
            } else {
                out.push(e);
            }
        }
        // Structural equality with bounded depth to avoid cycles
        fn structural_eq(a: &Expr, b: &Expr, depth: usize) -> bool {
            if std::ptr::eq(a, b) { return true; }
            if depth > 64 { return false; }
            if a.opkind != b.opkind { return false; }
            if a.op1_is_const != b.op1_is_const || a.op2_is_const != b.op2_is_const || a.op3_is_const != b.op3_is_const { return false; }
            if a.op1_is_const != 0 && a.op1 != b.op1 { return false; }
            if a.op2_is_const != 0 && a.op2 != b.op2 { return false; }
            if a.op3_is_const != 0 && a.op3 != b.op3 { return false; }
            let ok1 = match (a.safe_op1_ref(), b.safe_op1_ref()) { (Some(x), Some(y)) => structural_eq(x, y, depth+1), (None, None) => true, _ => false };
            if !ok1 { return false; }
            let ok2 = match (a.safe_op2_ref(), b.safe_op2_ref()) { (Some(x), Some(y)) => structural_eq(x, y, depth+1), (None, None) => true, _ => false };
            if !ok2 { return false; }
            let ok3 = match (a.safe_op3_ref(), b.safe_op3_ref()) { (Some(x), Some(y)) => structural_eq(x, y, depth+1), (None, None) => true, _ => false };
            ok3
        }

        let mut items = Vec::new();
        flatten_concat(expr, &mut items);
        if items.len() < 2 { return Ok(expr.clone()); }

        // Find runs of adjacent 8-bit extracts over the same base
        let mut changed = false;
        let mut result_items = Vec::new();
        let mut i = 0;

        while i < items.len() {
            let item = items[i];
            
            // Try to start a run from this position
            if let Some((base, high, low)) = extract_8bit_info(item) {
                let mut run = vec![(base, high, low)];
                let mut j = i + 1;
                
                // Extend the run as far as possible
                while j < items.len() {
                    if let Some((next_base, next_high, next_low)) = extract_8bit_info(items[j]) {
                        if structural_eq(base, next_base, 0) {
                            run.push((next_base, next_high, next_low));
                            j += 1;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                
                if run.len() >= 2 {
                    // Sort by high bit descending to check for contiguity
                    run.sort_by(|a, b| b.1.cmp(&a.1));
                    
                    // Check if they form a contiguous descending sequence
                    let mut is_contiguous = true;
                    for w in run.windows(2) {
                        let (_, h1, l1) = w[0];
                        let (_, h2, l2) = w[1];
                        if l1 != l2 + 8 || h1 != h2 + 8 {
                            is_contiguous = false;
                            break;
                        }
                    }
                    
                    if is_contiguous {
                        // Pack the run into a single extract
                        let run_high = run[0].1;
                        let run_low = run.last().unwrap().2;
                        
                        // Check if this is a full-width identity
                        if let Some(w) = infer_size(base) {
                            if run_low == 0 && run_high + 1 == w {
                                result_items.push(base);
                                changed = true;
                                i = j;
                                continue;
                            }
                        }
                        
                        // Create packed extract
                        let packed = Expr::pack_u32_pair_to_ptr(run_high, run_low);
                        let packed_extract = Expr {
                            op1: base as *const Expr as *mut Expr,
                            op2: packed,
                            op3: std::ptr::null_mut(),
                            opkind: K::Extract as u8,
                            op1_is_const: 0,
                            op2_is_const: 1,
                            op3_is_const: 0,
                        };
                        let packed_ptr = tls_alloc_opt(packed_extract);
                        if let Some(ptr) = packed_ptr {
                            result_items.push(unsafe { &*ptr });
                        }
                        changed = true;
                        i = j;
                        continue;
                    }
                }
            }
            
            // No run found, keep the original item
            result_items.push(item);
            i += 1;
        }

        if !changed {
            return Ok(expr.clone());
        }

        // Rebuild concat from result_items
        if result_items.is_empty() {
            return Ok(expr.clone());
        }
        if result_items.len() == 1 {
            return Ok(result_items[0].clone());
        }

        // Build right-associative concat tree
        let mut result = result_items.pop().unwrap().clone();
        while let Some(item) = result_items.pop() {
            let result_clone = result.clone();
            let result_ptr = tls_alloc_opt(result_clone);
            if let Some(ptr) = result_ptr {
                result = Expr {
                    op1: item as *const Expr as *mut Expr,
                    op2: ptr,
                    op3: std::ptr::null_mut(),
                    opkind: K::Concat as u8,
                    op1_is_const: 0,
                    op2_is_const: 0,
                    op3_is_const: 0,
                };
            } else {
                break;
            }
        }

        Ok(result)
    }

    fn priority(&self) -> u32 { 134 }
}

// Helper function to extract 8-bit extract information
fn extract_8bit_info(expr: &Expr) -> Option<(&Expr, u32, u32)> {
    use crate::expressions::expression::OpKind as K;
    if expr.opkind_is(K::Extract8) {
        if let Some(base) = expr.safe_op1_ref() {
            let idx = expr.op2 as u32;
            let low = idx * 8;
            let high = low + 7;
            Some((base, high, low))
        } else {
            None
        }
    } else if expr.opkind_is(K::Extract) {
        if let Some(base) = expr.safe_op1_ref() {
            let (high, low) = Expr::unpack_u32_pair_from_ptr(expr.op2);
            if (high - low + 1) == 8 && (low % 8) == 0 {
                Some((base, high, low))
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// Specialized rule to collapse nested concat-extract patterns like your Z3 assertion
/// Targets: Concat(Extract(base), Extract(base), Extract(base), Extract(base)) -> base (when full width)
pub struct NestedConcatExtractCollapseRule;

impl SimplificationRule for NestedConcatExtractCollapseRule {
    fn name(&self) -> &str { "NestedConcatExtractCollapse" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Concat) && !expr.opkind_is(OpKind::Concat8R) { return Ok(expr.clone()); }
        
        log::info!("NestedConcatExtractCollapseRule: checking expr opkind={:?}", expr.opkind);
        log::info!("NestedConcatExtractCollapseRule: Processing concat expression");

        // Flatten the entire concat tree
        fn flatten_concat<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
            if e.opkind_is(OpKind::Concat) || e.opkind_is(OpKind::Concat8R) {
                if let Some(l) = e.safe_op1_ref() { flatten_concat(l, out); }
                if let Some(r) = e.safe_op2_ref() { flatten_concat(r, out); }
            } else {
                out.push(e);
            }
        }

        // Deep structural equality check
        fn deep_structural_eq(a: &Expr, b: &Expr, depth: usize) -> bool {
            if depth > 20 { return false; } // Prevent infinite recursion
            if std::ptr::eq(a, b) { return true; }
            if a.opkind != b.opkind { return false; }
            if a.op1_is_const != b.op1_is_const { return false; }
            if a.op2_is_const != b.op2_is_const { return false; }
            if a.op3_is_const != b.op3_is_const { return false; }

            // Compare operands based on const flags and opkind validity
            if a.op1_is_const != 0 {
                if a.op1 != b.op1 { return false; }
            } else if a.has_valid_op1() && b.has_valid_op1() {
                if let (Some(a_op1), Some(b_op1)) = (a.safe_op1_ref(), b.safe_op1_ref()) {
                    if !deep_structural_eq(a_op1, b_op1, depth + 1) {
                        return false;
                    }
                } else {
                    return false;
                }
            } else if a.has_valid_op1() != b.has_valid_op1() {
                return false;
            }

            if a.op2_is_const != 0 {
                if a.op2 != b.op2 { return false; }
            } else if a.has_valid_op2() && b.has_valid_op2() {
                if let (Some(a_op2), Some(b_op2)) = (a.safe_op2_ref(), b.safe_op2_ref()) {
                    if !deep_structural_eq(a_op2, b_op2, depth + 1) {
                        return false;
                    }
                } else {
                    return false;
                }
            } else if a.has_valid_op2() != b.has_valid_op2() {
                return false;
            }

            if a.op3_is_const != 0 {
                if a.op3 != b.op3 { return false; }
            } else if a.has_valid_op3() && b.has_valid_op3() {
                if let (Some(a_op3), Some(b_op3)) = (a.safe_op3_ref(), b.safe_op3_ref()) {
                    if !deep_structural_eq(a_op3, b_op3, depth + 1) {
                        return false;
                    }
                } else {
                    return false;
                }
            } else if a.has_valid_op3() != b.has_valid_op3() {
                return false;
            }
            true
        }

        let mut items = Vec::new();
        flatten_concat(expr, &mut items);
        
        log::debug!("NestedConcatExtractCollapseRule: Found {} flattened items", items.len());
        
        // Look for patterns of 4 consecutive byte extracts from the same base
        if items.len() == 4 {
            log::debug!("NestedConcatExtractCollapseRule: Checking 4-item pattern");
            let mut extracts = Vec::new();
            for item in &items {
                if item.opkind_is(OpKind::Extract) {
                    if let Some(base) = item.safe_op1_ref() {
                        let (high, low) = Expr::unpack_u32_pair_from_ptr(item.op2);
                        if (high - low + 1) == 8 && (low % 8) == 0 { // 8-bit aligned extract
                            extracts.push((base, high, low));
                        } else {
                            return Ok(expr.clone());
                        }
                    } else {
                        return Ok(expr.clone());
                    }
                } else {
                    return Ok(expr.clone());
                }
            }

            // All must have same base (deep structural comparison)
            let base0 = extracts[0].0;
            for (base, _, _) in &extracts {
                if !deep_structural_eq(base0, base, 0) {
                    return Ok(expr.clone());
                }
            }

            // Check if they form consecutive descending bytes: [31:24], [23:16], [15:8], [7:0]
            let expected = [(31, 24), (23, 16), (15, 8), (7, 0)];
            for (i, (_, high, low)) in extracts.iter().enumerate() {
                if (*high, *low) != expected[i] {
                    return Ok(expr.clone());
                }
            }

            // If base is 32-bit, return it directly; otherwise extract [31:0]
            if let Some(w) = infer_size(base0) {
                if w == 32 {
                    return Ok(base0.clone());
                }
            }
            
            // Create Extract(base0, 31:0)
            let packed = Expr::pack_u32_pair_to_ptr(31, 0);
            return Ok(Expr {
                op1: base0 as *const Expr as *mut Expr,
                op2: packed,
                op3: std::ptr::null_mut(),
                opkind: OpKind::Extract as u8,
                op1_is_const: 0,
                op2_is_const: 1,
                op3_is_const: 0,
            });
        }

        Ok(expr.clone())
    }

    fn priority(&self) -> u32 { 140 } // High priority to run early
}

/// Rule specifically for the Z3 assertion pattern: nested extracts from identical bases
pub struct IdenticalBaseExtractCollapseRule;

impl SimplificationRule for IdenticalBaseExtractCollapseRule {
    fn name(&self) -> &str { "IdenticalBaseExtractCollapse" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        log::debug!("IdenticalBaseExtractCollapseRule: Checking expr opkind={:?}", expr.opkind);
        
        // Only process concat expressions
        if !expr.opkind_is(OpKind::Concat) && !expr.opkind_is(OpKind::Concat8R) {
            return Ok(expr.clone());
        }

        // Try to collapse the four-byte extract pattern
        if let Some(simplified) = self.try_collapse_four_byte_extracts(expr) {
            log::info!("IdenticalBaseExtractCollapseRule: Successfully simplified expression");
            Ok(simplified)
        } else {
            Ok(expr.clone())
        }
    }

    fn priority(&self) -> u32 { 145 } // Very high priority
}

impl IdenticalBaseExtractCollapseRule {
    fn try_collapse_four_byte_extracts(&self, expr: &Expr) -> Option<Expr> {
        log::info!("IdenticalBaseExtractCollapseRule: Checking for 4-byte extract pattern");
        // Pattern: concat(concat(concat(e1, e2), e3), e4)
        let (left, e4) = (expr.safe_op1_ref()?, expr.safe_op2_ref()?);
        log::info!("IdenticalBaseExtractCollapseRule: Got left and e4, checking if left is concat");
        if !left.opkind_is(OpKind::Concat) && !left.opkind_is(OpKind::Concat8R) { 
            log::info!("IdenticalBaseExtractCollapseRule: Left is not concat, returning None");
            return None; 
        }

        let (left2, e3) = (left.safe_op1_ref()?, left.safe_op2_ref()?);
        log::info!("IdenticalBaseExtractCollapseRule: Got left2 and e3, checking if left2 is concat");
        if !left2.opkind_is(OpKind::Concat) && !left2.opkind_is(OpKind::Concat8R) { 
            log::info!("IdenticalBaseExtractCollapseRule: Left2 is not concat, returning None");
            return None; 
        }

        let (e1, e2) = (left2.safe_op1_ref()?, left2.safe_op2_ref()?);

        // All must be extracts (either Extract or Extract8)
        log::info!("IdenticalBaseExtractCollapseRule: Checking if all 4 elements are extracts: e1={:?}, e2={:?}, e3={:?}, e4={:?}", e1.opkind, e2.opkind, e3.opkind, e4.opkind);
        let is_extract = |e: &Expr| e.opkind_is(OpKind::Extract) || e.opkind_is(OpKind::Extract8);
        if !is_extract(e1) || !is_extract(e2) || !is_extract(e3) || !is_extract(e4) {
            log::info!("IdenticalBaseExtractCollapseRule: Not all elements are extracts, returning None");
            return None;
        }

        log::info!("IdenticalBaseExtractCollapseRule: All elements are extracts, getting ranges");
        
        // Get extract ranges - handle Extract8 vs Extract differently
        let (h1, l1) = if e1.opkind_is(OpKind::Extract8) {
            let byte_idx = e1.op2 as u32;
            (byte_idx, byte_idx) // For Extract8, both high and low are the byte index
        } else if e1.opkind_is(OpKind::Extract) {
            Expr::unpack_u32_pair_from_ptr(e1.op2)
        } else {
            return None;
        };
        
        let (h2, l2) = if e2.opkind_is(OpKind::Extract8) {
            let byte_idx = e2.op2 as u32;
            (byte_idx, byte_idx)
        } else if e2.opkind_is(OpKind::Extract) {
            Expr::unpack_u32_pair_from_ptr(e2.op2)
        } else {
            return None;
        };
        
        let (h3, l3) = if e3.opkind_is(OpKind::Extract8) {
            let byte_idx = e3.op2 as u32;
            (byte_idx, byte_idx)
        } else if e3.opkind_is(OpKind::Extract) {
            Expr::unpack_u32_pair_from_ptr(e3.op2)
        } else {
            return None;
        };
        
        let (h4, l4) = if e4.opkind_is(OpKind::Extract8) {
            let byte_idx = e4.op2 as u32;
            (byte_idx, byte_idx)
        } else if e4.opkind_is(OpKind::Extract) {
            Expr::unpack_u32_pair_from_ptr(e4.op2)
        } else {
            return None;
        };

        log::info!("IdenticalBaseExtractCollapseRule: Extract ranges - e1:[{}:{}], e2:[{}:{}], e3:[{}:{}], e4:[{}:{}]", h1, l1, h2, l2, h3, l3, h4, l4);

        // Check if they form the expected byte pattern 
        // For Extract8: byte indices [3], [2], [1], [0] (consecutive bytes from high to low)
        // For Extract: [31:24], [23:16], [15:8], [7:0] (bit ranges)
        let matches_extract8_pattern = (h1, l1) == (3, 3) && (h2, l2) == (2, 2) && (h3, l3) == (1, 1) && (h4, l4) == (0, 0);
        let matches_extract_pattern = (h1, l1) == (31, 24) && (h2, l2) == (23, 16) && (h3, l3) == (15, 8) && (h4, l4) == (7, 0);
        
        if !matches_extract8_pattern && !matches_extract_pattern {
            log::info!("IdenticalBaseExtractCollapseRule: Extract ranges don't match expected pattern, returning None");
            return None;
        }
        
        log::info!("IdenticalBaseExtractCollapseRule: Extract ranges match expected pattern!");

        // Get the bases - only if op1 is not const
        let base1 = e1.safe_op1_ref()?;
        let base2 = e2.safe_op1_ref()?;
        let base3 = e3.safe_op1_ref()?;
        let base4 = e4.safe_op1_ref()?;

        // Check if all bases are structurally identical (deep comparison)
        if !self.deep_equal(base1, base2) || !self.deep_equal(base1, base3) || !self.deep_equal(base1, base4) {
            return None;
        }

        log::info!("IdenticalBaseExtractCollapseRule: Found matching 4-byte extract pattern");
        log::info!("IdenticalBaseExtractCollapseRule: Base expression opkind={:?}, op1=0x{:x}, op1_is_const={}", 
                  base1.opkind, base1.op1 as usize, base1.op1_is_const);

        // The pattern concat(extract[0:3], extract[0:2], extract[0:1], extract[0:0]) 
        // is equivalent to the base expression itself (extracting all 4 bytes)
        // Just return a clone of the base expression
        log::info!("IdenticalBaseExtractCollapseRule: Returning base expression directly");
        Some(base1.clone())
    }

    fn deep_equal(&self, a: &Expr, b: &Expr) -> bool {
        self.deep_equal_impl(a, b, 0)
    }

    fn deep_equal_impl(&self, a: &Expr, b: &Expr, depth: usize) -> bool {
        if depth > 25 { return false; } // Prevent infinite recursion
        if std::ptr::eq(a, b) { return true; }
        if a.opkind != b.opkind { return false; }
        if a.op1_is_const != b.op1_is_const { return false; }
        if a.op2_is_const != b.op2_is_const { return false; }
        if a.op3_is_const != b.op3_is_const { return false; }

        // Compare operands based on const flags and opkind validity
        if a.op1_is_const != 0 {
            if a.op1 != b.op1 { return false; }
        } else if a.has_valid_op1() && b.has_valid_op1() {
            if let (Some(a_op1), Some(b_op1)) = (a.safe_op1_ref(), b.safe_op1_ref()) {
                if !self.deep_equal_impl(a_op1, b_op1, depth + 1) {
                    return false;
                }
            } else {
                return false;
            }
        } else if a.has_valid_op1() != b.has_valid_op1() {
            return false;
        }

        if a.op2_is_const != 0 {
            if a.op2 != b.op2 { return false; }
        } else if a.has_valid_op2() && b.has_valid_op2() {
            if let (Some(a_op2), Some(b_op2)) = (a.safe_op2_ref(), b.safe_op2_ref()) {
                if !self.deep_equal_impl(a_op2, b_op2, depth + 1) {
                    return false;
                }
            } else {
                return false;
            }
        } else if a.has_valid_op2() != b.has_valid_op2() {
            return false;
        }

        if a.op3_is_const != 0 {
            if a.op3 != b.op3 { return false; }
        } else if a.has_valid_op3() && b.has_valid_op3() {
            if let (Some(a_op3), Some(b_op3)) = (a.safe_op3_ref(), b.safe_op3_ref()) {
                if !self.deep_equal_impl(a_op3, b_op3, depth + 1) {
                    return false;
                }
            } else {
                return false;
            }
        } else if a.has_valid_op3() != b.has_valid_op3() {
            return false;
        }

        true
    }
}

pub struct RecursiveConcatExtractSimplifyRule;

impl SimplificationRule for RecursiveConcatExtractSimplifyRule {
    fn name(&self) -> &str { "RecursiveConcatExtractSimplify" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        log::info!("RecursiveConcatExtractSimplifyRule: checking expr opkind={:?}", expr.opkind);
        if !expr.opkind_is(OpKind::Concat) && !expr.opkind_is(OpKind::Concat8R) { return Ok(expr.clone()); }
        
        log::info!("RecursiveConcatExtractSimplifyRule: Processing concat expression");

        // Check if this is a concat of 4 extracts from the same nested base
        if let (Some(left), Some(right)) = (expr.safe_op1_ref(), expr.safe_op2_ref()) {
            // Try to match pattern: concat(concat(concat(e1, e2), e3), e4)
            if left.opkind_is(OpKind::Concat) || left.opkind_is(OpKind::Concat8R) {
                if let (Some(ll), Some(lr)) = (left.safe_op1_ref(), left.safe_op2_ref()) {
                    if ll.opkind_is(OpKind::Concat) || ll.opkind_is(OpKind::Concat8R) {
                        if let (Some(lll), Some(llr)) = (ll.safe_op1_ref(), ll.safe_op2_ref()) {
                            // We have concat(concat(concat(lll, llr), lr), right)
                            // Check if all 4 are extracts: lll, llr, lr, right
                            let candidates = [lll, llr, lr, right];
                            let mut extract_info = Vec::new();
                            
                            for candidate in &candidates {
                                if candidate.opkind_is(OpKind::Extract) {
                                    if let Some(base) = candidate.safe_op1_ref() {
                                        let (high, low) = Expr::unpack_u32_pair_from_ptr(candidate.op2);
                                        if (high - low + 1) == 8 && (low % 8) == 0 {
                                            extract_info.push((base, high, low));
                                        } else {
                                            return Ok(expr.clone());
                                        }
                                    } else {
                                        return Ok(expr.clone());
                                    }
                                } else {
                                    return Ok(expr.clone());
                                }
                            }
                            
                            // Check if all extracts are from structurally equivalent bases
                            let base0 = extract_info[0].0;
                            for (base, _, _) in &extract_info {
                                if !self.deep_structural_eq(base0, base, 0) {
                                    return Ok(expr.clone());
                                }
                            }
                            
                            // Check if they form the expected byte pattern [31:24], [23:16], [15:8], [7:0]
                            let expected = [(31, 24), (23, 16), (15, 8), (7, 0)];
                            for (i, (_, high, low)) in extract_info.iter().enumerate() {
                                if (*high, *low) != expected[i] {
                                    return Ok(expr.clone());
                                }
                            }
                            
                            // Success! Replace with the base or extract [31:0] from base
                            if let Some(w) = infer_size(base0) {
                                if w == 32 {
                                    return Ok(base0.clone());
                                }
                            }
                            
                            let packed = Expr::pack_u32_pair_to_ptr(31, 0);
                            return Ok(Expr {
                                op1: base0 as *const Expr as *mut Expr,
                                op2: packed,
                                op3: std::ptr::null_mut(),
                                opkind: OpKind::Extract as u8,
                                op1_is_const: 0,
                                op2_is_const: 1,
                                op3_is_const: 0,
                            });
                        }
                    }
                }
            }
        }

        Ok(expr.clone())
    }

    fn priority(&self) -> u32 { 141 } // Higher priority than the general rule
}

impl RecursiveConcatExtractSimplifyRule {
    // Helper method for deep structural equality
    fn deep_structural_eq(&self, a: &Expr, b: &Expr, depth: usize) -> bool {
        if depth > 20 { return false; }
        if std::ptr::eq(a, b) { return true; }
        if a.opkind != b.opkind { return false; }
        if a.op1_is_const != b.op1_is_const || a.op2_is_const != b.op2_is_const || a.op3_is_const != b.op3_is_const { return false; }
        
        if a.op1_is_const != 0 && a.op1 != b.op1 { return false; }
        if a.op2_is_const != 0 && a.op2 != b.op2 { return false; }
        if a.op3_is_const != 0 && a.op3 != b.op3 { return false; }
        
        let op1_eq = match (a.safe_op1_ref(), b.safe_op1_ref()) {
            (Some(ax), Some(bx)) => self.deep_structural_eq(ax, bx, depth + 1),
            (None, None) => true,
            _ => false,
        };
        if !op1_eq { return false; }
        
        let op2_eq = match (a.safe_op2_ref(), b.safe_op2_ref()) {
            (Some(ax), Some(bx)) => self.deep_structural_eq(ax, bx, depth + 1),
            (None, None) => true,
            _ => false,
        };
        if !op2_eq { return false; }
        
        let op3_eq = match (a.safe_op3_ref(), b.safe_op3_ref()) {
            (Some(ax), Some(bx)) => self.deep_structural_eq(ax, bx, depth + 1),
            (None, None) => true,
            _ => false,
        };
        op3_eq
    }
}

/// Extract over packed byte concat rule
pub struct ExtractOverPackedByteConcatRule;

impl SimplificationRule for ExtractOverPackedByteConcatRule {
    fn name(&self) -> &str { "ExtractOverPackedByteConcat" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        use crate::expressions::expression::OpKind as K;
        if !expr.opkind_is(K::Extract) { return Ok(expr.clone()); }

        let concat = if let Some(c) = expr.safe_op1_ref() { c } else { return Ok(expr.clone()); };
        if !concat.opkind_is(K::Concat) { return Ok(expr.clone()); }

        let (extract_high, extract_low) = Expr::unpack_u32_pair_from_ptr(expr.op2);

        // Flatten concat and check if all items are 8-bit extracts from same base
        fn flatten_concat<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
            if e.opkind_is(K::Concat) {
                if let Some(l) = e.safe_op1_ref() { flatten_concat(l, out); }
                if let Some(r) = e.safe_op2_ref() { flatten_concat(r, out); }
            } else {
                out.push(e);
            }
        }

        let mut items = Vec::new();
        flatten_concat(concat, &mut items);

        if items.is_empty() { return Ok(expr.clone()); }

        // Check if all items are 8-bit extracts from the same base
        let mut base_opt = None;
        let mut byte_ranges = Vec::new();

        for item in &items {
            if let Some((base, high, low)) = extract_8bit_info(item) {
                if let Some(existing_base) = base_opt {
                    if !std::ptr::eq(base, existing_base) {
                        return Ok(expr.clone()); // Different bases
                    }
                } else {
                    base_opt = Some(base);
                }
                byte_ranges.push((high, low));
            } else {
                return Ok(expr.clone()); // Not an 8-bit extract
            }
        }

        let base = base_opt.unwrap();

        // Check if byte ranges are contiguous and descending
        let mut sorted_ranges = byte_ranges.clone();
        sorted_ranges.sort_by(|a, b| b.0.cmp(&a.0)); // Sort by high bit descending

        for w in sorted_ranges.windows(2) {
            let (h1, l1) = w[0];
            let (h2, l2) = w[1];
            if l1 != l2 + 8 || h1 != h2 + 8 {
                return Ok(expr.clone()); // Not contiguous
            }
        }

        // Calculate the range of the concat
        let concat_high = sorted_ranges[0].0;
        let concat_low = sorted_ranges.last().unwrap().1;

        // Map extract indices to the original base
        if extract_high > (concat_high - concat_low) || extract_low > (concat_high - concat_low) {
            return Ok(expr.clone()); // Extract out of bounds
        }

        let mapped_high = concat_low + extract_high;
        let mapped_low = concat_low + extract_low;

        // Create new extract on the original base
        let packed = Expr::pack_u32_pair_to_ptr(mapped_high, mapped_low);
        Ok(Expr {
            op1: base as *const Expr as *mut Expr,
            op2: packed,
            op3: std::ptr::null_mut(),
            opkind: K::Extract as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        })
    }

    fn priority(&self) -> u32 { 135 }
}

/// Concatenation optimization rule
pub struct ConcatenationOptimizationRule;

impl SimplificationRule for ConcatenationOptimizationRule {
    fn name(&self) -> &str { "ConcatenationOptimization" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Concat) {
            return Ok(expr.clone());
        }
        
        // Basic concat optimizations can be added here
        // For now, just return the original expression
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 130 }
}

/// Advanced concatenation rule
pub struct ConcatenationAdvancedRule;

impl SimplificationRule for ConcatenationAdvancedRule {
    fn name(&self) -> &str { "ConcatenationAdvanced" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        if !expr.opkind_is(OpKind::Concat) {
            return Ok(expr.clone());
        }
        
        // Advanced concat optimizations can be added here
        // For now, just return the original expression
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 135 }
}

/// Extract8 packing rule for concat
pub struct ConcatExtract8PackRule;

impl SimplificationRule for ConcatExtract8PackRule {
    fn name(&self) -> &str { "ConcatExtract8Pack" }
    
    fn apply(&self, expr: &Expr) -> Result<Expr> {
        use crate::expressions::expression::OpKind as K;
        if !expr.opkind_is(K::Concat) { return Ok(expr.clone()); }

        // This is a simplified version - the full implementation would be similar
        // to ConcatExtractPackRunsRule but specifically for Extract8
        Ok(expr.clone())
    }
    
    fn priority(&self) -> u32 { 132 }
}
