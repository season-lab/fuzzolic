use crate::expression::{Expr, Query};
use crate::config::Config;
use anyhow::Result;
use std::ptr;
use std::sync::atomic::{fence, Ordering};
use log::{info, debug, error};
use libc::{shmget, shmat, shmdt, IPC_CREAT};

/// Statistics for monitoring queue performance
#[derive(Debug, Clone)]
pub struct QueueStats {
    pub capacity: usize,
    pub length: usize,
    pub read_index: usize,
    pub write_index: usize,
    pub is_empty: bool,
    pub is_full: bool,
}

// Constants from symbolic-struct.h
pub const EXPR_POOL_CAPACITY: usize = 1024 * 1024 * 8;
pub const EXPR_QUERY_CAPACITY: usize = 1024 * 1024;
pub const EXPR_POOL_ADDR: *const libc::c_void = 0x7f05c8cc7000 as *const libc::c_void;
pub const FINAL_QUERY: *const libc::c_void = 0xDEAD as *const libc::c_void;
pub const SHM_READY: u32 = 0xDEADBEEF;
pub const SHM_DONE: *const libc::c_void = 0xABCDABCD as *const libc::c_void;

/// Shared expression pool implementation matching C version
pub struct SharedExprPool {
    pool: *mut Expr,
    capacity: usize,
    current_index: usize,
    #[allow(dead_code)]
    _shm_id: i32,
}

// SAFETY: SharedExprPool manages shared memory that can be safely accessed across threads
// The underlying shared memory is protected by system-level synchronization
unsafe impl Send for SharedExprPool {}
unsafe impl Sync for SharedExprPool {}

impl SharedExprPool {
    pub fn new(shm_key: u64, capacity: usize) -> Result<Self> {
        let size = capacity * std::mem::size_of::<Expr>();
        
        // Create or attach to shared memory segment
        let shm_id = unsafe {
            shmget(shm_key as i32, size, IPC_CREAT | 0o666)
        };
        
        if shm_id == -1 {
            anyhow::bail!("Failed to create shared memory segment for expression pool");
        }
        
        // Attach to shared memory
        let pool = unsafe {
            shmat(shm_id, EXPR_POOL_ADDR, 0) as *mut Expr
        };
        
        if pool == (-1isize) as *mut Expr {
            anyhow::bail!("Failed to attach to shared memory segment");
        }
        
        info!("Attached to expression pool shared memory (key: {}, size: {} bytes)", shm_key, size);
        
        Ok(SharedExprPool {
            pool,
            capacity,
            current_index: 0,
            _shm_id: shm_id,
        })
    }
    
    pub fn add_expr(&mut self, expr: Expr) -> Result<usize> {
        if self.current_index >= self.capacity {
            anyhow::bail!("Expression pool is full");
        }
        
        unsafe {
            ptr::write(self.pool.add(self.current_index), expr);
        }
        
        let index = self.current_index;
        self.current_index += 1;
        
        debug!("Added expression at index {}", index);
        Ok(index)
    }
    
    pub fn get_expr(&self, index: usize) -> Option<&Expr> {
        if index < self.current_index {
            unsafe {
                Some(&*self.pool.add(index))
            }
        } else {
            None
        }
    }
    
    pub fn get_expr_mut(&mut self, index: usize) -> Option<&mut Expr> {
        if index < self.current_index {
            unsafe {
                Some(&mut *self.pool.add(index))
            }
        } else {
            None
        }
    }
    
    pub fn len(&self) -> usize {
        self.current_index
    }
    
    pub fn capacity(&self) -> usize {
        self.capacity
    }
    
    pub fn as_slice(&self) -> &[Expr] {
        unsafe {
            std::slice::from_raw_parts(self.pool, self.current_index)
        }
    }
}

impl Drop for SharedExprPool {
    fn drop(&mut self) {
        unsafe {
            if shmdt(self.pool as *const libc::c_void) == -1 {
                error!("Failed to detach from expression pool shared memory");
            }
        }
    }
}

/// Query queue implementation matching C version
pub struct QueryQueue {
    queue: *mut Query,
    capacity: usize,
    read_index: usize,
    write_index: usize,
    #[allow(dead_code)]
    _shm_id: i32,
}

// SAFETY: QueryQueue manages shared memory that can be safely accessed across threads
// The underlying shared memory is protected by system-level synchronization
unsafe impl Send for QueryQueue {}
unsafe impl Sync for QueryQueue {}

impl QueryQueue {
    pub fn new(shm_key: u64, capacity: usize) -> Result<Self> {
        let size = capacity * std::mem::size_of::<Query>();
        
        // Create or attach to shared memory segment
        let shm_id = unsafe {
            shmget(shm_key as i32, size, IPC_CREAT | 0o666)
        };
        
        if shm_id == -1 {
            anyhow::bail!("Failed to create shared memory segment for query queue");
        }
        
        // Attach to shared memory
        let queue = unsafe {
            shmat(shm_id, ptr::null(), 0) as *mut Query
        };
        
        if queue == ptr::null_mut() || queue as isize == -1 {
            anyhow::bail!("Failed to attach to query queue shared memory");
        }
        
        info!("Attached to query queue shared memory (key: {}, size: {} bytes)", shm_key, size);
        
        Ok(QueryQueue {
            queue,
            capacity,
            read_index: 0,
            write_index: 0,
            _shm_id: shm_id,
        })
    }
    
    /// Pop a query from the queue
    pub fn pop_query(&mut self) -> Option<Query> {
        if self.read_index >= self.capacity {
            return None;
        }
        
        unsafe {
            let query_ptr = self.queue.add(self.read_index);
            if (&(*query_ptr).args.args8).arg1 == 0 {
                return None;
            }
            
            let query = Query {
                query_type: (*query_ptr).query_type,
                args: std::ptr::read(&(*query_ptr).args),
            };
            self.read_index += 1;
            Some(query)
        }
    }
    
    /// Push a query to the queue
    pub fn push_query(&mut self, query: Query) -> Result<()> {
        if self.write_index >= self.capacity {
            anyhow::bail!("Query queue is full");
        }
        
        unsafe {
            let query_ptr = self.queue.add(self.write_index);
            *query_ptr = query;
        }
        
        self.write_index += 1;
        Ok(())
    }
    
    pub fn add_query(&mut self, query: Query) -> Result<()> {
        let next_write = (self.write_index + 1) % self.capacity;
        
        if next_write == self.read_index {
            anyhow::bail!("Query queue is full");
        }
        
        let query_type = query.query_type;
        unsafe {
            ptr::write(self.queue.add(self.write_index), query);
        }
        
        self.write_index = next_write;
        debug!("Added query at index {} (type: {:?})", self.write_index, query_type);
        Ok(())
    }
    
    pub fn next_query(&mut self) -> Option<Query> {
        if self.read_index == self.write_index {
            return None; // Queue is empty
        }
        
        let query = unsafe {
            ptr::read(self.queue.add(self.read_index))
        };
        
        self.read_index = (self.read_index + 1) % self.capacity;
        debug!("Retrieved query from index {} (type: {:?})", self.read_index, query.query_type);
        Some(query)
    }
    
    pub fn len(&self) -> usize {
        if self.write_index >= self.read_index {
            self.write_index - self.read_index
        } else {
            self.capacity - self.read_index + self.write_index
        }
    }
    
    pub fn is_empty(&self) -> bool {
        self.read_index == self.write_index
    }
    
    /// Get queue statistics for monitoring
    pub fn get_stats(&self) -> QueueStats {
        QueueStats {
            capacity: self.capacity,
            length: self.len(),
            read_index: self.read_index,
            write_index: self.write_index,
            is_empty: self.is_empty(),
            is_full: self.is_full(),
        }
    }
    
    /// Wait for a query with timeout
    pub fn wait_for_query(&mut self, timeout_ms: u64) -> Option<Query> {
        use std::time::{Duration, Instant};
        
        let start = Instant::now();
        let timeout = Duration::from_millis(timeout_ms);
        
        while start.elapsed() < timeout {
            if let Some(query) = self.next_query() {
                return Some(query);
            }
            std::thread::sleep(Duration::from_micros(100)); // Short sleep to avoid busy waiting
        }
        
        None
    }
    
    /// Batch process multiple queries
    pub fn process_batch<F>(&mut self, mut processor: F, max_batch_size: usize) -> Result<usize>
    where
        F: FnMut(Query) -> Result<()>,
    {
        let mut processed = 0;
        
        while processed < max_batch_size {
            match self.next_query() {
                Some(query) => {
                    processor(query)?;
                    processed += 1;
                }
                None => break,
            }
        }
        
        Ok(processed)
    }

    pub fn is_full(&self) -> bool {
        (self.write_index + 1) % self.capacity == self.read_index
    }
    
    pub fn dequeue(&mut self) -> Result<Option<Query>> {
        if self.is_empty() {
            return Ok(None);
        }
        
        let query = unsafe { self.queue.add(self.read_index).read() };
        self.read_index = (self.read_index + 1) % self.capacity;
        
        Ok(Some(query))
    }
}

impl Drop for QueryQueue {
    fn drop(&mut self) {
        unsafe {
            if shmdt(self.queue as *const libc::c_void) == -1 {
                error!("Failed to detach from query queue shared memory");
            }
        }
    }
}

/// Shared memory manager matching C implementation
pub struct SharedMemoryManager {
    expr_pool: SharedExprPool,
    query_queue: QueryQueue,
}

impl SharedMemoryManager {
    pub fn new(config: &Config) -> Result<Self> {
        info!("Initializing shared memory manager with C-compatible layout");
        
        let expr_pool = SharedExprPool::new(
            config.expr_pool_shm_key, 
            EXPR_POOL_CAPACITY
        )?;
        
        let query_queue = QueryQueue::new(
            config.query_shm_key,
            EXPR_QUERY_CAPACITY
        )?;
        
        Ok(Self {
            expr_pool,
            query_queue,
        })
    }
    
    pub fn expr_pool(&mut self) -> &mut SharedExprPool {
        &mut self.expr_pool
    }
    
    pub fn query_queue(&mut self) -> &mut QueryQueue {
        &mut self.query_queue
    }
    
    pub fn get_next_query(&mut self) -> Result<Option<Query>> {
        self.query_queue.dequeue()
    }
    
    pub fn expr_pool_ref(&self) -> &SharedExprPool {
        &self.expr_pool
    }
    
    pub fn query_queue_ref(&self) -> &QueryQueue {
        &self.query_queue
    }
}

/// Memory barrier macro equivalent
#[inline(always)]
pub fn memory_barrier() {
    fence(Ordering::SeqCst);
}
