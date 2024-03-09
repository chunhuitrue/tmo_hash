use hashbrown::HashMap;
use core::fmt;
use std::{
    hash::Hash,
    mem, ptr::{NonNull, self},
    borrow::Borrow,
};
use std::collections::VecDeque;
use crate::Iter;

struct KeyRef<K> {
    k: *const K
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { (*self.k).eq(&*other.k) }
    }
}

impl<K: Eq> Eq for KeyRef<K> {}

impl<K> Borrow<K> for KeyRef<K> {
    fn borrow(&self) -> &K {
        unsafe { &*self.k}
    }
}

#[derive(Debug)]
pub(crate) struct Node<K, V> {
    pub(crate) key: mem::MaybeUninit<K>,
    pub(crate) value: mem::MaybeUninit<V>,
    pub(crate) prev: *mut Node<K, V>,
    pub(crate) next: *mut Node<K, V>,
}

impl<K, V> Node<K, V> {
    fn new_dummy() -> Self {
        Node {
            key: mem::MaybeUninit::uninit(),
            value: mem::MaybeUninit::uninit(),
            prev: ptr::null_mut(),
            next: ptr::null_mut()
        }
    }

    fn init_dummy(&mut self, key: K, val: V) {
        unsafe {
            self.key.as_mut_ptr().write(key);
            self.value.as_mut_ptr().write(val);
        }
    }
}

pub struct TmoHash<K, V>
where K: Eq + Hash 
{
    hash: HashMap<KeyRef<K>, NonNull<Node<K, V>>>,
    capacity: usize,
    head: *mut Node<K, V>,      // 可能最老的节点，新的节点都在tail，那老的节点会逐渐剩下到head上
    tail: *mut Node<K, V>,
    pool: VecDeque<Box<Node<K, V>>>,
}

impl<K, V> TmoHash<K, V>
where K: Eq + Hash
{
    /// # Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo: TmoHash<String, usize> = TmoHash::new(10);
    /// tmo.clear();    
    /// ```     
    pub fn new(capacity: usize) -> TmoHash<K, V> {
        let mut tmo = TmoHash {
            hash: HashMap::with_capacity(capacity),
            capacity,
            head: Box::into_raw(Box::new(Node::new_dummy())),
            tail: Box::into_raw(Box::new(Node::new_dummy())),
            pool: VecDeque::new()
        };
        unsafe {
            (*tmo.head).next = tmo.tail;
            (*tmo.tail).prev = tmo.head;
        }
        for _ in 0..capacity  {
            let dummy = Box::new(Node::<K, V>::new_dummy());            
            tmo.pool.push_front(dummy);
        }
        tmo
    }

    /// 插入一个k v对儿，如果已经存在，会替代。
    /// 返回插入value的引用
    /// 因为限于在流表场景下使用，所以在insert之前，用户需要确保节点不存在，也就是不要产生替代的情况
    /// # Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// assert_eq!(Some(&"a"), tmo.insert(1, "a"));
    /// assert!(tmo.contains_key(&1));
    /// assert!(!tmo.contains_key(&2));
    /// tmo.clear();    
    /// ```
    pub fn insert(&mut self, key: K, val: V) -> Option<&V>{
        if self.capacity == 0 || self.is_full() || self.pool.is_empty() {
            return None;
        }

        let mut node = self.pool.pop_front().unwrap();
        node.init_dummy(key, val);
        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(node));
            let new_ptr = new.as_ptr();            
            let keyref = (*new_ptr).key.as_ptr();
            self.attach(new_ptr);
            self.hash.insert(KeyRef { k: keyref }, new);
            Some(&*(*new_ptr).value.as_mut_ptr())
        }
    }
    
    /// 插入一个k v对儿，如果已经存在，会替代。
    /// 返回插入value的可变引用
    /// 因为限于在流表场景下使用，所以在insert之前，用户需要确保节点不存在，也就是不要产生替代的情况
    /// # Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// assert_eq!(Some(&mut "a"), tmo.insert_mut(1, "a"));
    /// assert!(tmo.contains_key(&1));
    /// assert!(!tmo.contains_key(&2));
    /// tmo.clear();    
    /// ```
    pub fn insert_mut(&mut self, key: K, val: V) -> Option<&mut V>{
        if self.capacity == 0 || self.is_full() || self.pool.is_empty() {
            return None;
        }

        let mut node = self.pool.pop_front().unwrap();
        node.init_dummy(key, val);
        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(node));            
            let new_ptr = new.as_ptr();            
            let keyref = (*new_ptr).key.as_ptr();
            self.attach(new_ptr);
            self.hash.insert(KeyRef { k: keyref }, new);
            Some(&mut *(*new_ptr).value.as_mut_ptr())
        }
    }
    
    /// 删除一个key
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// tmo.insert(3, "c");
    /// tmo.remove(&2);
    /// assert!(tmo.contains_key(&1));
    /// assert!(tmo.contains_key(&3));
    /// assert!(!tmo.contains_key(&2));
    /// tmo.clear();    
    /// ```
    pub fn remove(&mut self, k: &K) {
        if let Some(node) = self.hash.remove(k) {
            let mut node = unsafe { Box::from_raw(node.as_ptr()) };
            self.detach(&mut *node);
            self.pool.push_front(node);
        }
    }
    
    /// 根据key，判断是否存在节点
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// assert!(tmo.contains_key(&1));
    /// assert!(tmo.contains_key(&2));
    /// assert!(!tmo.contains_key(&3));
    /// tmo.clear();    
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        self.hash.contains_key(key)
    }

    /// 返回最大容量
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo: TmoHash<usize, String> = TmoHash::new(10);
    /// assert_eq!(tmo.capacity(), 10);
    /// tmo.clear();    
    /// ```
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// 返回已有数据的个数
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// assert_eq!(tmo.len(), 0);
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// assert_eq!(tmo.len(), 2);
    /// tmo.clear();    
    /// ```
    pub fn len(&self) -> usize {
        self.hash.len()
    }

    /// 返回是否为空
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// assert!(tmo.is_empty());
    /// tmo.insert(1, "a");
    /// assert!(!tmo.is_empty());
    /// tmo.clear();    
    /// ```
    pub fn is_empty(&self) -> bool {
        self.hash.is_empty()
    }

    /// 返回是否已满
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo: TmoHash<usize, usize> = TmoHash::new(10);
    /// assert!(!tmo.is_full());
    /// for i in 0..10 {
    ///     tmo.insert(i, i);
    /// }
    /// assert!(tmo.is_full());
    /// tmo.clear();    
    /// ```
    pub fn is_full(&self) -> bool {
        self.hash.len() >= self.capacity
    }

    /// 清空tmohash
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// tmo.clear();
    /// assert_eq!(tmo.len(), 0);
    /// assert!(tmo.is_empty());
    /// assert_eq!(tmo.capacity(), 10);
    /// tmo.clear();    
    /// ```
    pub fn clear(&mut self) {
        while self.pop().is_some() {}
        self.pool.clear();
    }

    /// 弹出head节点。可能是最老的
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// tmo.insert(3, "c");
    /// assert_eq!(Some((1, "a")), tmo.pop());
    /// assert_eq!(tmo.len(), 2);
    /// assert!(!tmo.contains_key(&1));
    /// tmo.clear();    
    /// ```
    pub fn pop(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            return None;
        }

        let node = self.remove_old()?;
        let node = *node;
        let Node { key, value, .. } = node;
        unsafe { Some((key.assume_init(), value.assume_init())) }
    }

    /// 根据key，查询返回value的引用。因为是不变引用，说明没有更新，所以不需要重新移动到链表尾部
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// tmo.insert(3, "c");
    /// assert_eq!(Some((&"a")), tmo.get(&1));
    /// assert_eq!(Some((&"b")), tmo.get(&2));
    /// assert_eq!(Some((&"c")), tmo.get(&3));
    /// assert_ne!(Some((&"d")), tmo.get(&4));
    /// tmo.clear();    
    /// ```
    pub fn get(&self, k: &K) -> Option<&V> {
        if let Some(node) = self.hash.get(k) {
            let node_ptr = node.as_ptr();
            Some(unsafe { &*(*node_ptr).value.as_ptr() })
        } else {
            None
        }
    }
    
    /// 根据key，查询返回value的可变引用
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// tmo.insert(3, "c");
    /// let node = tmo.get_mut(&1).unwrap();
    /// *node = &"d";
    /// assert_eq!(Some((&"d")), tmo.get(&1));
    /// tmo.clear();    
    /// ```
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        if let Some(node) = self.hash.get(k) {
            let node_ptr = node.as_ptr();
            self.detach(node_ptr);
            self.attach(node_ptr);
            Some(unsafe { &mut *(*node_ptr).value.as_mut_ptr() })
        } else {
            None
        }
    }

    /// 查看最老一端的node
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// assert_eq!(None, tmo.peek());
    /// tmo.insert(1, "a");
    /// tmo.insert(2, "b");
    /// assert_eq!(Some((&1, &"a")), tmo.peek());
    /// assert!(tmo.contains_key(&1));
    /// tmo.clear();    
    /// ```
    pub fn peek(&self) -> Option<(&K, &V)> {
        if self.is_empty() {
            None
        } else {
            unsafe {
                let ref_key = &(*(*(*self.head).next).key.as_ptr());
                let ref_val = &(*(*(*self.head).next).value.as_ptr());
                Some((ref_key, ref_val))
            }
        }
    }

    /// 从最老的node开始迭代
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert("a", 1);
    /// tmo.insert("b", 2);
    /// tmo.insert("c", 3);
    /// let sum = tmo.iter().map(|x| x.1).sum();
    /// assert_eq!(6, sum);
    /// tmo.clear();    
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            done: 0,
            len: self.len(),
            next: unsafe { (*self.head).next },
            phantom: std::marker::PhantomData
        }
    }

    /// 从最老的一端开始遍历，根据闭包返回确定是否保留此节点
    /// 闭包为true 删除，为fals 不删除，保留
    ///
    /// 遇到第一个不满足条件的就返回。用于老化tmo场景。
    /// 从最老开始，一直删除到不满足闭包条件的第一个node为止。并不遍历所有节点。只从最老开始遍历到第一个不需要老化为止。
    /// 这样，既能尽快删除了所有需要老化的节点，也不会遍历过多
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert("a", 1);
    /// tmo.insert("b", 2);
    /// tmo.insert("c", 3);
    /// tmo.insert("d", 10);
    /// tmo.insert("e", 11);
    /// tmo.insert("f", 12);
    /// tmo.insert("g", 4);
    /// tmo.timeout(|&_k, &v| v < 10);
    /// assert_eq!(4, tmo.len());
    /// assert!(!tmo.contains_key(&"a"));
    /// assert!(!tmo.contains_key(&"b"));
    /// assert!(!tmo.contains_key(&"c"));
    /// assert!(tmo.contains_key(&"g"));
    /// tmo.clear();    
    /// ```
    pub fn timeout<F>(&mut self, fun: F)
    where F: Fn(&K, &V) -> bool
    {
        if self.is_empty() {
            return;
        }

        while let Some((key, val)) = self.peek() {
            if fun(key, val) {
                unsafe {        // 和remove一样，删除head的第一个node，因为peek就是head的第一个node
                    let prev = (*self.head).next;
                    if prev != self.head {
                        let old_key = KeyRef { k: &(*(*(*self.head).next).key.as_ptr()) };
                        let old_node = self.hash.remove(&old_key).unwrap();
                        let node_ptr = old_node.as_ptr();
                        self.detach(node_ptr);
                        let _ =  Some(Box::from_raw(node_ptr));
                    }
                }
            } else {
                return;
            }
        }
    }
    
    // remove 最老的一端的第一个node
    fn remove_old(&mut self) -> Option<Box<Node<K, V>>> {
        unsafe {
            let prev = (*self.head).next;
            if prev != self.head {
                let old_key = KeyRef { k: &(*(*(*self.head).next).key.as_ptr()) };
                let old_node = self.hash.remove(&old_key).unwrap();
                let node_ptr = old_node.as_ptr();
                self.detach(node_ptr);
                Some(Box::from_raw(node_ptr))
            } else {
                None
            }
        }
    }
    
    /// 新结点添加到尾部，头部是老的，尾部是新的 
    fn attach(&mut self, node: *mut Node<K, V>) {
        unsafe {
            (*node).prev = (*self.tail).prev;
            (*node).next = self.tail;
            (*self.tail).prev = node;
            (*(*node).prev).next = node;
        }
    }

    fn detach(&mut self, node: *mut Node<K, V>) {    
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    /// 返回内存池中当前剩余node的数量
    ///
    /// #Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let mut tmo = TmoHash::new(10);
    /// tmo.insert("a", 1);
    /// tmo.insert("b", 2);
    /// assert_eq!(8, tmo.pool_len());
    /// ```    
    pub fn pool_len(&self) -> usize {
        self.pool.len()
    }
}

impl<K, V> Drop for TmoHash<K, V>
where K: Hash + Eq
{
    fn drop(&mut self) {
        self.clear();
        unsafe {
            let _ = Box::from_raw(self.head);
            let _ = Box::from_raw(self.tail);
        }
    }
}

unsafe impl<K: Send, V: Send> Send for TmoHash<K, V> where K: Eq + Hash {}
unsafe impl<K: Sync, V: Sync> Sync for TmoHash<K, V> where K: Eq + Hash {}

impl<K, V> fmt::Debug for TmoHash<K, V>
where
    K: fmt::Debug + Hash + Eq,
    V: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TmoHash [")?;
        if self.is_empty() {
            return write!(f, "]");
        } else {
            write!(f, " ")?;
        }
        let mut comma = false;
        let iter = self.iter();
        for kv in iter {
            if comma {
                write!(f, ", ")?;
            } else {
                comma = true;
            }
            write!(f, "({:?}, {:?})", kv.0, kv.1)?;
        }
        write!(f, " ]")
    }
}

/// display
///
/// # Examples
///
/// ```
/// use tmohash::TmoHash;
///
/// let mut tmo = TmoHash::new(10);
/// tmo.insert(1, "a");
/// tmo.insert(2, "b");
/// tmo.insert(3, "c");
/// assert_eq!("[1: a, 2: b, 3: c]", format!("{}", tmo));
/// tmo.clear();
/// ```
impl<K, V> fmt::Display for TmoHash<K, V>
where
    K: fmt::Display + Hash + Eq + Clone,
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let items = self.iter()
            .map(|x| format!("{}: {}", x.0, x.1))
            .collect::<Vec<String>>();
        write!(f, "[{}]", items.join(", "))        
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_debug() {
        let mut tmo = TmoHash::new(10);
        tmo.insert(1, "a");
        tmo.insert(2, "b");
        tmo.insert(3, "c");
        assert_eq!("TmoHash [ (1, \"a\"), (2, \"b\"), (3, \"c\") ]", format!("{:?}", tmo));
        tmo.clear();
    }

    #[test]
    fn test_display() {
        let mut tmo: TmoHash<usize, &str> = TmoHash::new(10);
        assert_eq!("[]", format!("{}", tmo));
        
        tmo.insert(1, "a");
        tmo.insert(2, "b");
        tmo.insert(3, "c");
        assert_eq!("[1: a, 2: b, 3: c]", format!("{}", tmo));
        tmo.clear();        
    }
    
    #[test]
    fn test_iter_debug() {
        let mut tmo = TmoHash::new(10);
        tmo.insert(1, "a");
        tmo.insert(2, "b");
        tmo.insert(3, "c");

        let mut iter = tmo.iter();
        iter.next();
        assert_eq!("Iter [1/3 next: 2]", format!("{:?}", iter));

        iter.next();
        iter.next();
        assert_eq!("Iter [3/3]", format!("{:?}", iter));
        tmo.clear();        
    }

    #[test]
    fn test_iter_display() {
        let mut tmo = TmoHash::new(10);
        tmo.insert(1, "a");
        tmo.insert(2, "b");
        tmo.insert(3, "c");

        let mut iter = tmo.iter();
        iter.next();
        assert_eq!("Iter [1/3 next: 2]", format!("{}", iter));

        iter.next();
        iter.next();
        assert_eq!("Iter [3/3]", format!("{}", iter));
        tmo.clear();        
    }

    #[test]
    fn test_pool() {
        let mut tmo = TmoHash::new(10);
        assert_eq!(10, tmo.pool_len());
        
        tmo.insert(1, "a");
        assert_eq!(9, tmo.pool_len());
        tmo.insert(2, "b");
        assert_eq!(8, tmo.pool_len());
        tmo.insert(3, "c");
        assert_eq!(7, tmo.pool_len());

        tmo.remove(&1);
        assert_eq!(8, tmo.pool_len());
        tmo.remove(&2);
        assert_eq!(9, tmo.pool_len());
        tmo.remove(&3);
        assert_eq!(10, tmo.pool_len());
        
        tmo.clear()
    }
}
