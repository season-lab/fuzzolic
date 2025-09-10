use anyhow::Result;
use crate::expressions::expression::{Expr, OpKind};
use super::SimplificationRule;

/// Extract-of-concat collapse rule - handles patterns like extract(concat(a,b,c,d), [31:24]) -> a
pub struct ExtractConcatCollapseRule;

impl SimplificationRule for ExtractConcatCollapseRule {
    fn name(&self) -> &str { "ExtractConcatCollapse" }

    fn apply(&self, expr: &Expr) -> Result<Expr> {
        // Handle Extract and Extract8 operations
        if !expr.opkind_is(OpKind::Extract) && !expr.opkind_is(OpKind::Extract8) {
            log::debug!("ExtractConcatCollapseRule: Skipping non-Extract expression with opkind={:?} ({})", expr.opkind, expr.opkind as u8);
            return Ok(expr.clone());
        }
        
        log::debug!("ExtractConcatCollapseRule: Processing Extract/Extract8 expression with opkind={:?}", expr.opkind);
        
        // Get the operand being extracted from
        let operand = if let Some(op) = expr.safe_op1_ref() {
            op
        } else {
            return Ok(expr.clone());
        };
        
        // Only handle extracts from concat operations
        if !operand.opkind_is(OpKind::Concat) && !operand.opkind_is(OpKind::Concat8R) {
            return Ok(expr.clone());
        }
        
        // Get extract range - handle both Extract and Extract8
        let (high, low) = if expr.opkind_is(OpKind::Extract8) {
            // For Extract8, op2 contains the byte index directly
            let byte_idx = expr.op2 as u32;
            (byte_idx * 8 + 7, byte_idx * 8)
        } else {
            // For Extract, op2 contains packed high:low range
            Expr::unpack_u32_pair_from_ptr(expr.op2)
        };
        
        // Special case: handle the specific pattern ((_ extract 31 24) (concat (concat (concat input_3 input_2) input_1) input_0))
        // This should simplify to input_3 for bits 31:24, input_2 for bits 23:16, etc.
        if self.try_simplify_byte_extract_from_input_concat(expr, operand, high, low).is_some() {
            return self.try_simplify_byte_extract_from_input_concat(expr, operand, high, low)
                .map(|result| {
                    log::debug!("ExtractConcatCollapseRule: Simplified byte extract {}:{} to direct input", high, low);
                    result
                })
                .ok_or_else(|| anyhow::anyhow!("Failed to simplify byte extract"));
        }
        
        // Flatten the concat tree to get all operands
        let mut operands = Vec::new();
        self.flatten_concat(operand, &mut operands);
        
        log::debug!("ExtractConcatCollapseRule: Flattened {} operands, extracting bits {}:{}", 
                   operands.len(), high, low);
        
        // Check if this is a byte-aligned extract that maps to specific operands
        if (high + 1 - low) % 8 == 0 && low % 8 == 0 {
            let byte_low = low / 8;
            let byte_high = high / 8;
            let num_bytes = byte_high - byte_low + 1;
            
            log::debug!("ExtractConcatCollapseRule: Byte-aligned extract, bytes {}:{} ({} bytes)", 
                       byte_high, byte_low, num_bytes);
            
            // If extracting exactly one byte and it maps to a single operand
            if num_bytes == 1 && byte_low < operands.len() as u32 {
                let operand_idx = (operands.len() as u32 - 1 - byte_low) as usize;
                if operand_idx < operands.len() {
                    log::debug!("ExtractConcatCollapseRule: Collapsing to single operand at index {}", operand_idx);
                    return Ok(operands[operand_idx].clone());
                }
            }
            
            // If extracting multiple contiguous bytes
            if num_bytes > 1 && byte_low + num_bytes <= operands.len() as u32 {
                let start_idx = (operands.len() as u32 - byte_low - num_bytes) as usize;
                let end_idx = (operands.len() as u32 - byte_low) as usize;
                
                if start_idx < operands.len() && end_idx <= operands.len() {
                    let selected_operands: Vec<&Expr> = operands[start_idx..end_idx].iter().copied().collect();
                    log::debug!("ExtractConcatCollapseRule: Collapsing to {} operands", selected_operands.len());
                    return Ok(self.build_concat_chain(&selected_operands));
                }
            }
        }
        
        Ok(expr.clone())
    }

    fn priority(&self) -> u32 { 145 } // High priority to apply early
}

impl ExtractConcatCollapseRule {
    /// Try to simplify byte extracts from input concat patterns
    /// Pattern: ((_ extract 31 24) (concat (concat (concat input_3 input_2) input_1) input_0)) -> input_3
    fn try_simplify_byte_extract_from_input_concat(&self, _expr: &Expr, operand: &Expr, high: u32, low: u32) -> Option<Expr> {
        // Check if this is a byte-aligned extract
        if (high + 1 - low) != 8 || low % 8 != 0 {
            return None;
        }
        
        let byte_index = low / 8;
        
        // Flatten the concat to get all operands
        let mut operands = Vec::new();
        self.flatten_concat(operand, &mut operands);
        
        // Check if we have exactly 4 operands (input_3, input_2, input_1, input_0)
        if operands.len() == 4 {
            // For a 32-bit value with 4 byte inputs:
            // Bits 31:24 -> input_3 (index 0 in flattened MSB-first order)
            // Bits 23:16 -> input_2 (index 1)
            // Bits 15:8  -> input_1 (index 2)  
            // Bits 7:0   -> input_0 (index 3)
            let operand_idx = match byte_index {
                0 => 3, // Bits 7:0 -> input_0
                1 => 2, // Bits 15:8 -> input_1
                2 => 1, // Bits 23:16 -> input_2
                3 => 0, // Bits 31:24 -> input_3
                _ => return None,
            };
            
            if operand_idx < operands.len() {
                log::debug!("ExtractConcatCollapseRule: Byte extract {}:{} maps to input operand at index {}", high, low, operand_idx);
                return Some(operands[operand_idx].clone());
            }
        }
        
        None
    }

    /// Flatten a concat tree into a vector of operands (MSB first)
    fn flatten_concat<'a>(&self, expr: &'a Expr, operands: &mut Vec<&'a Expr>) {
        if expr.opkind_is(OpKind::Concat) || expr.opkind_is(OpKind::Concat8R) {
            // For concat, left operand is MSB, right operand is LSB
            if let Some(left) = expr.safe_op1_ref() {
                self.flatten_concat(left, operands);
            }
            if let Some(right) = expr.safe_op2_ref() {
                self.flatten_concat(right, operands);
            }
        } else {
            // Check if this is a symbolic input (leaf node)
            if expr.opkind_is(OpKind::IsSymbolic) {
                log::debug!("ExtractConcatCollapseRule: Found symbolic input at operand position {}", operands.len());
            }
            operands.push(expr);
        }
    }
    
    /// Build a concat chain from a slice of operands
    fn build_concat_chain(&self, operands: &[&Expr]) -> Expr {
        if operands.len() == 1 {
            return operands[0].clone();
        }
        
        let mut result = operands[0].clone();
        for &operand in &operands[1..] {
            result = Expr {
                op1: &result as *const Expr as *mut Expr,
                op2: operand as *const Expr as *mut Expr,
                op3: std::ptr::null_mut(),
                opkind: OpKind::Concat as u8,
                op1_is_const: 0,
                op2_is_const: 0,
                op3_is_const: 0,
            };
        }
        result
    }
}
