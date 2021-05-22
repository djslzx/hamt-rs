#[derive(Debug)]
pub struct List<E> {
    head: Link<E>
}

#[derive(Debug)]
struct Node<E> {
    elt: E,
    next: Link<E>
}

type Link<E> = Option<Box<Node<E>>>;

impl<E> List<E> {
    pub fn new() -> Self {
        List { head: None }
    }
    pub fn push(&mut self, elt: E) {
        let node = Node {
            elt,
            next: self.head.take(),
        };
        self.head = Some(Box::new(node));
    }
    pub fn pop(&mut self) -> Option<E> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.elt
        })
    }
    pub fn peek(&self) -> Option<&E> {
        self.head.as_ref().map(|node| &node.elt)
    }
    pub fn peek_mut(&mut self) -> Option<&mut E> {
        self.head.as_mut().map(|node| &mut node.elt)
    }
}

impl<E> Drop for List<E> {
    fn drop(&mut self) {
        let mut link = self.head.take();
        while let Some(mut boxed) = link {
            link = boxed.next.take();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push() {
        let mut list = List::new();
        list.push('c');
        list.push('b');
        list.push('a');
        println!("list={:?}", list);
    }

    #[test]
    fn test_pop() {
        let mut list = List::new();
        list.push('a');
        assert_eq!(list.pop(), Some('a'));
        list.push('a');
        list.push('b');
        assert_eq!(list.pop(), Some('b'));
    }

    #[test]
    fn test_peek() {
        let mut list = List::new();
        list.push('a');
        assert_eq!(list.peek(), Some(&'a'));
    }

    #[test]
    fn test_peek_mut() {
        let mut list = List::new();
        list.push('a');
        list.peek_mut().map(|val| *val = 'b');
        assert_eq!(list.peek(), Some(&'b'));
    }
}