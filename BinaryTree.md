# Binary Trees with In-order Iterators

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
traversal.

## Binary Trees

We begin by defining a `union` for binary trees:

```{.deduce #Tree}
union Tree<E> {
  EmptyTree
  TreeNode(Tree<E>, E, Tree<E>)
}
```

For example, we can represent the following binary tree 

![Diagram of a Binary Tree](./BinaryTree07.png)

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
  in_order(TreeNode(L, x, R)) = append(in_order(L), node(x, in_order(R)))
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
ti_first : < E > fn Tree<E>,E,Tree<E> -> TreeIter<E>
ti_get : < E > fn TreeIter<E> -> E
ti_next : < E > fn TreeIter<E> -> TreeIter<E>
ti_index : < E > fn(TreeIter<E>) -> Nat
```

* The `ti_first` operator returns an itereator pointing to the first
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
assert ti_index(iter0) = 3

define iter7 = ti_next(ti_next(ti_next(ti_next(iter3))))
assert ti_get(iter7) = 7
assert ti_index(iter7) = 7
```



<!--
```{.deduce file=BinaryTree.pf} 
import Nat
import List

<<Tree>>
<<height>>
<<num_nodes>>
<<in_order>>

union Direction<E> {
  RightD(Tree<E>, E)
  LeftD(E,Tree<E>)
}

union TreeIter<E> {
  TrItr(List<Direction<E>>, Tree<E>, E, Tree<E>)
}

function ti2tree<E>(TreeIter<E>) -> Tree<E> {
  ti2tree(TrItr(ctx, L, x, R)) = plug_tree(ctx, TreeNode(L, x, R))
}

function ti_get<E>(TreeIter<E>) -> E {
  ti_get(TrItr(ctx, L, x, R)) = x
}

function first_ctx<E>(Tree<E>, E, Tree<E>, List<Direction<E>>) -> TreeIter<E> {
  first_ctx(EmptyTree, x, R, ctx) = TrItr(ctx, EmptyTree, x, R)
  first_ctx(TreeNode(LL, y, LR), x, R, ctx) = first_ctx(LL, y, LR, node(LeftD(x, R), ctx))
}

define ti_first : < E > fn Tree<E>,E,Tree<E> -> TreeIter<E>
    = λ L,x,R { first_ctx(L, x, R, empty) }

function next_up<E>(List<Direction<E>>, Tree<E>, E, Tree<E>) -> TreeIter<E> {
  next_up(empty, A, z, B) = TrItr(empty, A, z, B)
  next_up(node(f, ctx'), A, z, B) =
    switch f {
      case RightD(L, x) {
        next_up(ctx', L, x, TreeNode(A, z, B))
      }
      case LeftD(x, R) {
        TrItr(ctx', TreeNode(A, z, B), x, R)
      }
    }
}

function ti_next<E>(TreeIter<E>) -> TreeIter<E> {
  ti_next(TrItr(ctx, L, x, R)) =
    switch R {
      case EmptyTree {
        next_up(ctx, L, x, R)
      }
      case TreeNode(RL, y, RR) {
        first_ctx(RL, y, RR, node(RightD(L, x), ctx))
      }
    }
}

function plug_tree<E>(List<Direction<E>>, Tree<E>) -> Tree<E> {
  plug_tree(empty, t) = t
  plug_tree(node(f, ctx'), t) =
    switch f {
      case RightD(L, x) {
        plug_tree(ctx', TreeNode(L, x, t))
      }
      case LeftD(x, R) {
        plug_tree(ctx', TreeNode(t, x, R))
      }
    }
}

function take_ctx<E>(List<Direction<E>>) -> List<Direction<E>> {
  take_ctx(empty) = empty
  take_ctx(node(f, ctx')) =
    switch f {
      case RightD(L, x) {
        node(RightD(L,x), take_ctx(ctx'))
      }
      case LeftD(x, R) {
        take_ctx(ctx')
      }
    }
}

function drop_ctx<E>(List<Direction<E>>) -> List<Direction<E>> {
  drop_ctx(empty) = empty
  drop_ctx(node(f, ctx')) =
    switch f {
      case RightD(L, x) {
        drop_ctx(ctx')
      }
      case LeftD(x, R) {
        node(LeftD(x, R), drop_ctx(ctx'))
      }
    }
}

function ti_take<E>(TreeIter<E>) -> Tree<E> {
  ti_take(TrItr(ctx, L, x, R)) = plug_tree(take_ctx(ctx), L)
}

define ti_index : < E > fn(TreeIter<E>) -> Nat = λ z { num_nodes(ti_take(z))}

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
```
-->
