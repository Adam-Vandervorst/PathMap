use crate::PathMap;

#[derive(Debug, Clone, Default)]
pub struct NodeWeight {
    pub local_count: u64,
}

#[derive(Clone)]
pub struct WeightedTriemap<V: Clone + Send + Sync + Unpin> {
    inner: PathMap<NodeWeight>,
    _phantom: std::marker::PhantomData<V>,
}

impl<V: Clone + Send + Sync + Unpin> WeightedTriemap<V> {
    pub fn new() -> Self {
        Self {
            inner: PathMap::new(),
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn increment_count(&mut self, path: &[u8]) {
        let current_weight = self.inner.get_val_at(path)
            .map(|w| w.clone())
            .unwrap_or_default();
        
        let new_weight = NodeWeight {
            local_count: current_weight.local_count + 1,
        };
        
        self.inner.set_val_at(path, new_weight);
    }

    pub fn get_weight(&self, path: &[u8]) -> Option<NodeWeight> {
        self.inner.get_val_at(path).cloned()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl<V: Clone + Send + Sync + Unpin> Default for WeightedTriemap<V> {
    fn default() -> Self {
        Self::new()
    }
}
