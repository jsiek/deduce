# Binary Trees with In-order Iterators (Part 1)

This is the fifth blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

In this blog post we study binary trees, that is, trees in which each
node has at most two children. We study the in-order tree traversal,
as that will become important when we study binary search trees.
Furthermore, we implement tree iterators that keep track of a location
within the tree and can move forward with respect to the in-order
traversal. We shall prove that our implementation of tree iterators
is correct in Part 2 of this blog post.

## Binary Trees

We begin by defining a `union` for binary trees:

```{.deduce #Tree}
union Tree<E> {
  EmptyTree
  TreeNode(Tree<E>, E, Tree<E>)
}
```

For example, we can represent the following binary tree 

![Diagram of a Binary Tree](https://www.dropbox.com/scl/fi/0jp518lh06ym8fcnlw7jg/BinaryTree07.png?rlkey=8g8beeabeqakb3c9kk6z3vrja&st=cj3qj2s8&raw=1)

with a bunch of tree nodes like so:

```{.deduce #BinaryTree05}
define T0 = TreeNode(EmptyTree, 0, EmptyTree)
define T2 = TreeNode(EmptyTree, 2, EmptyTree)
define T1 = TreeNode(T0, 1, T2)
define T4 = TreeNode(EmptyTree, 4, EmptyTree)
define T5 = TreeNode(T4, 5, EmptyTree)
define T7 = TreeNode(EmptyTree, 7, EmptyTree)
define T6 = TreeNode(T5, 6, T7)
define T3 = TreeNode(T1, 3, T6)
```

We define the height of a tree with the following recursive function.

```{.deduce #height}
function height<E>(Tree<E>) -> Nat {
  height(EmptyTree) = 0
  height(TreeNode(L, x, R)) = suc(max(height(L), height(R)))
}
```

The example tree has height `4`.

```{.deduce #test_height}
assert height(T3) = 4
```

We count the number of nodes in a binary tree with the `num_nodes`
function.

```{.deduce #num_nodes}
function num_nodes<E>(Tree<E>) -> Nat {
  num_nodes(EmptyTree) = 0
  num_nodes(TreeNode(L, x, R)) = suc(num_nodes(L) + num_nodes(R))
}
```

The example tree has `8` nodes.

```{.deduce #test_num_nodes}
assert num_nodes(T3) = 8
```

## In-order Tree Traversal

Now for the main event of this blog post, the in-order tree traversal.
The idea of this traversal is that for each node in the tree, we
follow this recipe:

1. process the left subtree
2. process the current node
3. process the right subtree

What it means to process a node can be different for different
instantiations of the in-order traversal. But to make things concrete,
we study an in-order traversal that produces a list. So here is our
definition of the `in_order` function.

```{.deduce #in_order}
function in_order<E>(Tree<E>) -> List<E> {
  in_order(EmptyTree) = empty
  in_order(TreeNode(L, x, R)) = in_order(L) ++ node(x, in_order(R))
}
```

The result of `in_order` for `T3` is the list `0,1,2,3,4,5,6,7`.
As you can see, we chose the data values in `T3` to match their position 
within the in-order traversal.

```{.deduce #test_in_order}
assert in_order(T3) = interval(8, 0)
```

## In-order Tree Iterators

A tree iterator keeps track of a position with a tree.  Our goal is to
create a data structure to represent a tree iterator and also to
implement the following operations on iterators, which we describe in
the following paragraph.

```
ti2tree : < E > fn TreeIter<E> -> Tree<E>
ti_first : < E > fn Tree<E>,E,Tree<E> -> TreeIter<E>
ti_get : < E > fn TreeIter<E> -> E
ti_next : < E > fn TreeIter<E> -> TreeIter<E>
ti_index : < E > fn(TreeIter<E>) -> Nat
```

* The `ti2tree` operator returns the tree that the iterator is traversing.

* The `ti_first` operator returns an iterator pointing to the first
  node (with respect to the in-order traversal) of a non-empty tree.  We
  represent non-empty trees with three things: the left subtree, the
  data in the root node, and the right subtree.

* The `ti_get` operator returns the data of the node at the current position.

* The `ti_next` operator moves the iterator forward by one position.

* The `ti_index` operator returns the position of the iterator as a natural number.

Here is an example of creating an iterator for `T3` and moving it forward.

```{.deduce #test_first_get}
define iter0 = ti_first(T1, 3, T6)
assert ti_get(iter0) = 0
assert ti_index(iter0) = 0

define iter3 = ti_next(ti_next(ti_next(iter0)))
assert ti_get(iter3) = 3
assert ti_index(iter3) = 3

define iter7 = ti_next(ti_next(ti_next(ti_next(iter3))))
assert ti_get(iter7) = 7
assert ti_index(iter7) = 7
```

### Iterator Representation

We represent a position in the tree by recording a path of
left-or-right decisions. For example, to represent the position of
node `4` of the example tree, we record the path `R,L,L` (`R` for
right and `L` for left).

![Diagram of the iterator at position 4](https://www.dropbox.com/scl/fi/3kpijipyfufv71sks0maf/Iter4.png?rlkey=qt33fb2h9mhymbs6vo2i4oqd8&raw=1)

When we come to implement the `ti_next` operation, we will sometimes
need to climb the tree. For example, to get from `4` to `5`.  To make
that easier, we will store the path in reverse. So the path to node
`4` will be stored as `L,L,R`.

It would seem natural to store an iterator's path separately from the
tree, but doing so would complicate many of the upcoming proofs
because only certain paths make sense for certain trees.  Instead, we
combine the path and the tree into a single data structure called a
*zipper* (Huet, The Zipper, Journal of Functional Programming,
Vol 7. Issue 5, 1997). The idea is to attach extra data to the left
and right decisions and to store the subtree at the current position.
So we define a `union` named `Direction` with constructors for left
and right, and we define a union named `TreeIter` that contains a path
and the non-empty tree at the current position.

```{.deduce #TreeIter}
union Direction<E> {
  LeftD(E, Tree<E>)
  RightD(Tree<E>, E)
}

union TreeIter<E> {
  TrItr(List<Direction<E>>, Tree<E>, E, Tree<E>)
}
```

### The `ti2tree` Operation

Of the tree iterator operations, we will first implement `ti2tree`
because it will help to explain this zipper-style representation.  We
start by defining the auxiliary function `plug_tree`, which
reconstructs a tree from a path and the subtree at the specified
position. The `plug_tree` function is defined by recursion on the
path, so it moves upward in the tree with each recursive call.
Consider the case for `LeftD(x, R)` below.  To plug tree `t` into the
path `node(LeftD(x, R), path')`, we used the extra data stored in
`LeftD(x, R)` to create `TreeNode(t, x, R)` which we then pass to the
recursive call, to plug the new tree node into the rest of the path.

```{.deduce #plug_tree}
function plug_tree<E>(List<Direction<E>>, Tree<E>) -> Tree<E> {
  plug_tree(empty, t) = t
  plug_tree(node(f, path'), t) =
    switch f {
      case LeftD(x, R) {
        plug_tree(path', TreeNode(t, x, R))
      }
      case RightD(L, x) {
        plug_tree(path', TreeNode(L, x, t))
      }
    }
}
```

The `ti2tree` operator simply invokes `plug_tree`.

```{.deduce #ti2tree}
function ti2tree<E>(TreeIter<E>) -> Tree<E> {
  ti2tree(TrItr(path, L, x, R)) = plug_tree(path, TreeNode(L, x, R))
}
```

Creating an iterator from a tree using `ti_first` and then applying
`ti2tree` produces the original tree. Furthermore, moving an iterator
does not change the tree that it is traversing, so `ti2tree` returns
`T3` for iterators `iter0`, `iter3`, and `iter7`.

```{.deduce #test_ti2tree}
assert ti2tree(iter0) = T3
assert ti2tree(iter3) = T3
assert ti2tree(iter7) = T3
```

### The `ti_first` Operation

Recall that the `ti_first` operation returns an iterator pointing to
the first node (with respect to the in-order traversal) of a non-empty
tree. For example, applying `ti_first` to `T3` should give us node
`0`.  The idea to implement `ti_first` is simple: we walk down the
tree going left at each step, until we get to a leaf. 

To implement `ti_first` we define the auxiliary function `first_path`
that takes a non-empty tree and the path-so-far and proceeds going to
the left down the tree. (The `first_path` function will also come
in handy when implementing `ti_next`.)

```{.deduce #first_path}
function first_path<E>(Tree<E>, E, Tree<E>, List<Direction<E>>) -> TreeIter<E> {
  first_path(EmptyTree, x, R, path) = TrItr(path, EmptyTree, x, R)
  first_path(TreeNode(LL, y, LR), x, R, path) = first_path(LL, y, LR, node(LeftD(x, R), path))
}
```

We implement `ti_first` simply as a call to `first_path` where the
path-so-far is `empty`.

```{.deduce #ti_first}
define ti_first : < E > fn Tree<E>,E,Tree<E> -> TreeIter<E>
    = generic E { λ L,x,R { first_path(L, x, R, empty) } }

```

As promised above, applying `ti_first` to `T3` gives us node `0`.

```{.deduce #test_ti_first}
assert ti_get(ti_first(T1, 3, T6)) = 0
```

### The `ti_get` Operation

Recall that the `ti_get` operator should return the data of the node
at the current position. This is straightforward to implement because
that data is stored directly in the tree iterator.

```{.deduce #ti_get}
function ti_get<E>(TreeIter<E>) -> E {
  ti_get(TrItr(path, L, x, R)) = x
}
```

### The `ti_next` Operation

Recall that the `ti_next` operator moves the iterator forward by one
position with respect to the in-order traversal. This operation is
non-trivial to implement. Consider again our example tree.

![Diagram of a Binary Tree](https://www.dropbox.com/scl/fi/0jp518lh06ym8fcnlw7jg/BinaryTree07.png?rlkey=8g8beeabeqakb3c9kk6z3vrja&st=cj3qj2s8&raw=1)

Suppose the current node is `2`. Then the next node is `3`, which
requires climbing a fair ways up the tree. On the other hand, if the
current node is `3`, then the next node is `4`, way back down the
tree. So there are two different scenarios that we need to handle.

1. If the current node has a right child, then the next node is the
   *first* node of the right child's subtree (with respect to in-order
   traversal). For example, node `3` has right child `6`, and the
   first node of that subtree is `4`.

2. If the current node does not have a right child, then the next node
   is the ancestor after the first left branch. For example, node `2`
   does not have a right child, so we go up the tree. We go up to `1`
   via a right branch and then up to `3` via a left branch, so `3` is
   the next node of `2`.

For (1) we already have `first_path`, so we just need an auxiliary
function for (2), which we call `next_up`. This function takes a path
and the current non-empty subtree and returns the iterator for the
next position. If the direction is `RightD`, we keep going up the
tree.  If the direction is `LeftD(x, R)`, we stop and return an
iterator for the parent node `x`.

```{.deduce #next_up}
function next_up<E>(List<Direction<E>>, Tree<E>, E, Tree<E>) -> TreeIter<E> {
  next_up(empty, A, z, B) = TrItr(empty, A, z, B)
  next_up(node(f, path'), A, z, B) =
    switch f {
      case RightD(L, x) {
        next_up(path', L, x, TreeNode(A, z, B))
      }
      case LeftD(x, R) {
        TrItr(path', TreeNode(A, z, B), x, R)
      }
    }
}
```

Now that we have both `next_up` and `first_path`, we implement
`ti_next` by checking whether the right child `R` is empty. If it is,
we invoke `next_up`, and if not, we invoke `first_path`.

```{.deduce #ti_next}
function ti_next<E>(TreeIter<E>) -> TreeIter<E> {
  ti_next(TrItr(path, L, x, R)) =
    switch R {
      case EmptyTree {
        next_up(path, L, x, R)
      }
      case TreeNode(RL, y, RR) {
        first_path(RL, y, RR, node(RightD(L, x), path))
      }
    }
}
```

To see `ti_next` in action, in the following we go from position `2`
up to position `3` and then back down to position `4.`

```{.deduce #test_ti_next}
define iter2 = ti_next(ti_next(iter0))
assert ti_get(iter2) = 2

define iter3_ = ti_next(iter2)
assert ti_get(iter3_) = 3

define iter4 = ti_next(iter3_)
assert ti_get(iter4) = 4
```

### The `ti_index` Operation

Recall that the `ti_index` operator returns the position of the
iterator as a natural number. More specifically, `ti_index` returns
the position of the current node with respect to the in the in-order
traversal. The following demonstrates this invariant on `iter0` and
`iter7.`

```{.deduce #test_ti_index}
define L0 = in_order(ti2tree(iter0))
define i0 = ti_index(iter0)
assert ti_get(iter0) = nth(L0, 42)(i0)

define L7 = in_order(ti2tree(iter7))
define i7 = ti_index(iter7)
assert ti_get(iter7) = nth(L7, 42)(i7)
```

The idea for implementing `ti_index` is that we'll count how many
nodes are in the portion of the tree that comes before the current
position. We define an auxiliary function that constructs this portion
of the tree, calling it `ti_take` because it is reminiscent of the
`take(n, ls)` function in `List.pf`, which returns the prefix of list
`ls` of length `n`. Furthermore, we use a second auxiliary function
named `take_path` that applies this idea to the path of the iterator.
So to implement the `take_path` function, we throw away the subtrees
to the right of the path (by removing `LeftD(x, R)`) and we keep the
subtrees to the left of the path (by keeping `Right(L, x)`).

```{.deduce #take_path}
function take_path<E>(List<Direction<E>>) -> List<Direction<E>> {
  take_path(empty) = empty
  take_path(node(f, path')) =
    switch f {
      case RightD(L, x) {
        node(RightD(L,x), take_path(path'))
      }
      case LeftD(x, R) {
        take_path(path')
      }
    }
}
```

We implement `ti_take` by applying `take_path` to the path of the
iterator, and then plug the left subtree `L` into the result.  (The
node `x` and subtree `R` are not before node `x` with respect to
in-order traversal.)

```{.deduce #ti_take}
function ti_take<E>(TreeIter<E>) -> Tree<E> {
  ti_take(TrItr(path, L, x, R)) = plug_tree(take_path(path), L)
}
```

Finally, we implement `ti_index` by counting the number of nodes
in the tree returned by `ti_take`.

```{.deduce #ti_index}
define ti_index : < E > fn(TreeIter<E>) -> Nat = 
    generic E { λ iter { num_nodes(ti_take(iter))} }
```

### Exercise: Implement and test the `ti_prev` Operation

The `ti_prev` operation (for previous) moves the iterator backward by
one position with respect to in-order traversal.

```
ti_prev : < E > fn TreeIter<E> -> TreeIter<E>
```

Implement and test the `ti_prev` operation.


## Conclusion

This completes the implementation of the 5 tree iterator operations.
In Part 2 of this blog post, we will prove that these operations are correct.


<!--
```{.deduce file=BinaryTree.pf} 
import Nat
import List

<<Tree>>
<<height>>
<<num_nodes>>
<<in_order>>

<<TreeIter>>
<<plug_tree>>
<<ti2tree>>
<<first_path>>
<<ti_first>>
<<ti_get>>
<<next_up>>
<<ti_next>>
<<take_path>>
<<ti_take>>
<<ti_index>>
```

```{.deduce file=BinaryTreeTest.pf} 
import Nat
import List
import BinaryTree

<<BinaryTree05>>
<<test_height>>
<<test_num_nodes>>
<<test_in_order>>
<<test_first_get>>
<<test_ti2tree>>
<<test_ti_first>>
<<test_ti_next>>
<<test_ti_index>>
```
-->

<!--  LocalWords:  EmptyTree TreeNode BinaryTree suc num ti fn iter
 -->
<!--  LocalWords:  TreeIter Huet LeftD RightD TrItr LL LR RL RR ls 
 -->
<!--  LocalWords:  pf BinaryTreeTest
 -->
