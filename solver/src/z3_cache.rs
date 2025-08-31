use z3::{ast::Dynamic, Context};
use std::collections::HashMap;
use log::debug;

/// Z3 expression cache for optimization and memoization
pub struct Z3Cache {
    /// Cache for expression string representations to avoid redundant creation
    expr_cache: HashMap<usize, String>,
    /// Cache for optimized expression string representations
    opt_cache: HashMap<usize, String>,
}

impl Z3Cache {
    pub fn new(_ctx: &Context) -> Self {
        Self {
            expr_cache: HashMap::new(),
            opt_cache: HashMap::new(),
        }
    }

    /// Cache Z3 expression with generated key
    pub fn cache_expr(&mut self, expr: &Dynamic) -> usize {
        // Use expression string representation as hash for cache key
        let key = self.generate_expr_key(expr);
        if !self.expr_cache.contains_key(&key) {
            let expr_str = expr.to_string();
            self.expr_cache.insert(key, expr_str);
            debug!("Cached Z3 expression with key: {}", key);
        }
        key
    }

    /// Get cached expression string by key
    pub fn get_expr(&self, key: usize) -> Option<&String> {
        self.expr_cache.get(&key)
    }

    /// Store expression string in cache
    pub fn store_expr(&mut self, key: usize, expr_str: String) {
        self.expr_cache.insert(key, expr_str);
        debug!("Stored expression string with key: {}", key);
    }

    /// Get optimized expression string by key
    pub fn get_optimized(&self, key: usize) -> Option<&String> {
        self.opt_cache.get(&key)
    }

    /// Store optimized expression string in cache
    pub fn store_optimized(&mut self, key: usize, expr_str: String) {
        self.opt_cache.insert(key, expr_str);
        debug!("Stored optimized expression string with key: {}", key);
    }

    /// Clear all caches
    pub fn clear(&mut self) {
        self.expr_cache.clear();
        self.opt_cache.clear();
        debug!("Cleared Z3 expression caches");
    }

    /// Generate a cache key from expression
    fn generate_expr_key(&self, expr: &Dynamic) -> usize {
        // Use the string representation hash as a simple key
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let expr_str = expr.to_string();
        let mut hasher = DefaultHasher::new();
        expr_str.hash(&mut hasher);
        hasher.finish() as usize
    }

    /// Get cache statistics
    pub fn stats(&self) -> CacheStats {
        CacheStats {
            expr_cache_size: self.expr_cache.len(),
            opt_cache_size: self.opt_cache.len(),
        }
    }
}

unsafe impl Send for Z3Cache {}
unsafe impl Sync for Z3Cache {}

#[derive(Debug, Clone)]
pub struct CacheStats {
    pub expr_cache_size: usize,
    pub opt_cache_size: usize,
}

impl std::fmt::Display for CacheStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Z3 Cache: {} expressions, {} optimized", 
               self.expr_cache_size, self.opt_cache_size)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use z3::*;

    #[test]
    fn test_z3_cache_basic() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut cache = Z3Cache::new(&ctx);

        let bv = ast::BV::new_const(&ctx, "test", 32);
        let key = cache.generate_expr_key(&bv.clone().into());
        
        cache.store_expr(key, bv.to_string());
        assert!(cache.get_expr(key).is_some());
        
        let stats = cache.stats();
        assert_eq!(stats.expr_cache_size, 1);
        assert_eq!(stats.opt_cache_size, 0);
    }

}
