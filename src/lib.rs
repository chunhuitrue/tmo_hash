use hashbrown::HashMap;
use std::{hash::{Hash}, mem, ptr::NonNull, borrow::Borrow};

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

type Link <K, V> = Option<NonNull<Node<K, V>>>;

struct Node<K, V> {
    key: mem::MaybeUninit<K>,
    value: mem::MaybeUninit<V>,
    prev: Link<K, V>,
    next: Link<K, V>,
}

impl<K, V> Node<K, V> {
    fn new(key: K, val: V) -> Self {
        Node { key: mem::MaybeUninit::new(key), value: mem::MaybeUninit::new(val), prev: None, next: None }
    }
}

pub struct TmoHash<K, V>
where K: Eq + Hash 
{
    hash: HashMap<KeyRef<K>, NonNull<Node<K, V>>>,
    capacity: usize,
    head: Link<K, V>,
    tail: Link<K, V>
}

impl<K, V> TmoHash<K, V>
where K: Eq + Hash
{
    pub fn new(capacity: usize) -> TmoHash<K, V> {
        TmoHash {
            hash: HashMap::with_capacity(capacity),
            capacity,
            head: None,
            tail: None
        }
    }

    // todo 提供一个接口。如果存在，就返回node，不存在就插入。或者插入失败。方便使用
    
    /// 根据key，判断是否存在节点
    pub fn contains_key(&self, key: &K) -> bool {
        self.hash.contains_key(key)
    }
    
    /// 插入一个k v对儿。
    /// 如果已经存在，会替代。
    /// 因为限于在流表场景下使用，所以在inser之前，用户需要确保节点不存在，也就是不要产生替代的情况 
    pub fn insert(&mut self, key: K, val: V) -> Result<(), TmoError>{
        if self.is_empty() || self.is_full() {
           return Err(TmoError::InsertErr);
        }

        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(key, val))));
            self.attach(&new);
            let node_ptr: *mut Node<K, V> = new.as_ptr();
            let keyref = (*node_ptr).key.as_ptr();
            self.hash.insert(KeyRef { k: keyref }, new);
        }
        Ok(())
    }

    fn attach(&mut self, _node: &NonNull<Node<K, V>>) {
        todo!()
    }

    fn detach(&mut self, _node: &NonNull<Node<K, V>>) {
        todo!()
    }
    
    pub fn del_old(&mut self) -> Option<(K, V)>{
        todo!()
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

    pub fn clear(&mut self) {
        while self.del_old().is_some() {}
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
