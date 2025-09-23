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

    pub fn new_with_k(_k: usize) -> Self {
        Self::new()
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

    pub fn get_weight_copy(&self, path: &[u8]) -> Option<NodeWeight> {
        self.inner.get_val_at(path).cloned()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn extract_subtrees(input: &str) -> Vec<String> {
        let mut subtrees = Vec::new();
        let mut depth = 0;
        let mut start = 0;
        let mut in_string = false;
        let mut escape_next = false;
        
        let chars: Vec<char> = input.chars().collect();
        
        for (i, &c) in chars.iter().enumerate() {
            if escape_next {
                escape_next = false;
                continue;
            }
            
            match c {
                '\\' if in_string => escape_next = true,
                '"' => in_string = !in_string,
                '(' if !in_string => {
                    if depth == 0 {
                        start = i;
                    }
                    depth += 1;
                }
                ')' if !in_string => {
                    depth -= 1;
                    if depth == 0 {
                        let subtree = chars[start..=i].iter().collect::<String>();
                        subtrees.push(subtree);
                    }
                }
                _ => {}
            }
        }
        
        subtrees
    }
}

impl<V: Clone + Send + Sync + Unpin> Default for WeightedTriemap<V> {
    fn default() -> Self {
        Self::new()
    }
}
