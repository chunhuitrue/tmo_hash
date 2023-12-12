use hashbrown::HashMap;
use std::{hash::{Hash}, mem, ptr::{NonNull, self}, borrow::Borrow};

struct KeyRef<K> {
    k: *const K
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K>  {
    fn eq(&self, other: &Self) -> bool {
        unsafe { (*self.k).eq(&*other.k) }
    }
}

impl<K: Eq> Eq for KeyRef<K>  {}

impl<K> Borrow<K> for KeyRef<K> {
    fn borrow(&self) -> &K {
        unsafe { &*self.k}
    }
}

struct Node<K, V> {
    key: mem::MaybeUninit<K>,
    value: mem::MaybeUninit<V>,
    prev: *mut Node<K, V>,
    next: *mut Node<K, V>,
}

impl<K, V> Node<K, V> {
    fn new(key: K, val: V) -> Self {
        Node {
            key: mem::MaybeUninit::new(key),
            value: mem::MaybeUninit::new(val),
            prev: ptr::null_mut(),
            next: ptr::null_mut()
        }
    }

    fn new_dummy() -> Self {
        Node {
            key: mem::MaybeUninit::uninit(),
            value: mem::MaybeUninit::uninit(),
            prev: ptr::null_mut(),
            next: ptr::null_mut()
        }
    }
}

pub struct TmoHash<K, V>
where K: Eq + Hash 
{
    hash: HashMap<KeyRef<K>, NonNull<Node<K, V>>>,
    capacity: usize,
    head: *mut Node<K, V>,
    tail: *mut Node<K, V>,
}

impl<K, V> TmoHash<K, V>
where K: Eq + Hash
{

    /// # Example
    ///
    /// ```
    /// use tmohash::TmoHash;
    ///
    /// let tmo: TmoHash<String, usize> = TmoHash::new(10);
    /// ```     
    pub fn new(capacity: usize) -> TmoHash<K, V> {
        let tmo = TmoHash {
            hash: HashMap::with_capacity(capacity),
            capacity,
            head: Box::into_raw(Box::new(Node::new_dummy())),
            tail: Box::into_raw(Box::new(Node::new_dummy())),
        };
        unsafe {
            (*tmo.head).next = tmo.tail;
            (*tmo.tail).prev = tmo.head;
        }
        tmo
    }
    
    /// 插入一个k v对儿。
    /// 如果已经存在，会替代。
    /// 因为限于在流表场景下使用，所以在insert之前，用户需要确保节点不存在，也就是不要产生替代的情况 
    pub fn insert(&mut self, key: K, val: V) -> Result<(), TmoError>{
        if self.is_empty() || self.is_full() {
           return Err(TmoError::InsertErr);
        }

        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(key, val))));
            let new_ptr = new.as_ptr();            
            let keyref = (*new_ptr).key.as_ptr();
            self.attach(new_ptr);
            self.hash.insert(KeyRef { k: keyref }, new);
        }
        Ok(())
    }

    // 删除一个key
    pub fn delete(&mut self, k: &K) {
        if let Some(node) = self.hash.remove(k) {
            let mut node = unsafe { *Box::from_raw(node.as_ptr()) };
            self.detach(&mut node);
            let Node { key: _, value: _, ..} = node;
        }
    }
    
    // todo 查找
    
    /// 根据key，判断是否存在节点
    pub fn contains_key(&self, key: &K) -> bool {
        self.hash.contains_key(key)
    }
    
    pub fn capacity(&self) -> usize {
        self.capacity
    }
    
    pub fn len(&self) -> usize {
        self.hash.len()
    }

    pub fn is_empty(&self) -> bool {
        self.hash.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.hash.len() >= self.capacity
    }

    pub fn pop_old(&mut self) -> Option<(K, V)>{
        // if self.is_empty() {
        //     return None;
        // }
        
        todo!()
    }
    
    pub fn clear(&mut self) {
        while self.pop_old().is_some() {}
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
}

unsafe impl<K: Send, V: Send> Send for TmoHash<K, V> where K: Eq + Hash {}
unsafe impl<K: Sync, V: Sync> Sync for TmoHash<K, V> where K: Eq + Hash {}


pub enum TmoError {
    InsertErr
}

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
