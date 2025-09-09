use crate::shared_memory::shared_memory::{SharedExprPool, QueryQueue};
use crate::expressions::expression::{Expr, OpKind, QueryType, Query, QueryArgs, QueryArgs8};
use std::ptr;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shared_memory_query_processing() {
        // Test query queue operations
        let mut queue = QueryQueue::new(1024, 256).expect("Failed to create query queue");
        
        // Create a test query
        let test_expr = Expr {
            op1: ptr::null_mut(),
            op2: ptr::null_mut(), 
            op3: ptr::null_mut(),
            opkind: OpKind::IsConst as u8,
            op1_is_const: 1,
            op2_is_const: 0,
            op3_is_const: 0,
        };
        
        let query = Query {
            address: 0,
            query: &test_expr as *const Expr as *mut Expr,
            args: QueryArgs { args8: std::mem::ManuallyDrop::new(QueryArgs8 { 
                arg0: 42,
                arg1: 0,
                arg2: 0,
                arg3: 0,
                arg4: 0,
                arg5: 0,
                arg6: 0,
                arg7: 0,
            })},
            query_type: QueryType::Branch,
        };
        
        // Test adding query
        queue.add_query(query).expect("Failed to add query");
        
        // Test retrieving query
        if let Some(retrieved_query) = queue.next_query() {
            unsafe {
                let args8: &QueryArgs8 = &*(&retrieved_query.args.args8 as *const _ as *const QueryArgs8);
                assert_eq!(args8.arg0, 42);
            }
        } else {
            panic!("Failed to retrieve query");
        }
        
        // Test queue statistics
        let stats = queue.get_stats();
        assert_eq!(stats.length, 0); // Should be empty after processing
        assert!(!stats.is_empty || stats.length == 0); // Should be consistent
    }
    
    #[test]
    fn test_shared_expr_pool_operations() {
        let mut pool = SharedExprPool::new(4096, 1024).expect("Failed to create expression pool");
        
        // Test adding expressions
        let expr1 = Expr {
            op1: ptr::null_mut(),
            op2: ptr::null_mut(),
            op3: ptr::null_mut(), 
            opkind: OpKind::Add as u8,
            op1_is_const: 0,
            op2_is_const: 1,
            op3_is_const: 0,
        };
        
        let expr_id = pool.add_expr(expr1).expect("Failed to add expression");
        assert_eq!(expr_id, 0);
        
        // Test retrieving expressions
        let retrieved = pool.get_expr(expr_id).expect("Failed to get expression");
        assert_eq!(retrieved.opkind, OpKind::Add as u8);
        assert_eq!(retrieved.op2_is_const, 1);
        
        // Basic sanity: pool should contain exactly one expression now
        assert_eq!(pool.len(), 1);
    }
    
    #[test]
    fn test_query_queue_batch_processing() {
        let mut queue = QueryQueue::new(1024, 256).expect("Failed to create query queue");
        
        // Add multiple queries
        for i in 0..5 {
            let test_expr = Expr {
                op1: ptr::null_mut(),
                op2: ptr::null_mut(),
                op3: ptr::null_mut(),
                opkind: OpKind::IsConst as u8,
                op1_is_const: 1,
                op2_is_const: 0,
                op3_is_const: 0,
            };
            
            let query = Query {
                address: 0,
                query: &test_expr as *const Expr as *mut Expr,
                args: QueryArgs { args8: std::mem::ManuallyDrop::new(QueryArgs8 { 
                    arg0: i as u8,
                    arg1: 0,
                    arg2: 0,
                    arg3: 0,
                    arg4: 0,
                    arg5: 0,
                    arg6: 0,
                    arg7: 0,
                })},
                query_type: QueryType::Branch,
            };
            
            queue.add_query(query).expect("Failed to add query");
        }
        
        // Process all queries
        let mut processed_count = 0;
        while let Some(query) = queue.next_query() {
            unsafe {
                let args8: &QueryArgs8 = &*(&query.args.args8 as *const _ as *const QueryArgs8);
                assert_eq!(args8.arg0 as usize, processed_count);
            }
            processed_count += 1;
        }
        
        assert_eq!(processed_count, 5);
        
        let stats = queue.get_stats();
        assert_eq!(stats.length, 0); // Should be empty after processing all
    }
    
    #[test]
    fn test_query_queue_timeout_behavior() {
        let mut queue = QueryQueue::new(1024, 256).expect("Failed to create query queue");
        
        // Test waiting for query with timeout when queue is empty
        let start = std::time::Instant::now();
        let result = queue.wait_for_query(100);
        let elapsed = start.elapsed();
        
        assert!(result.is_none());
        assert!(elapsed >= std::time::Duration::from_millis(90)); // Allow some tolerance
        assert!(elapsed <= std::time::Duration::from_millis(150));
    }
}
