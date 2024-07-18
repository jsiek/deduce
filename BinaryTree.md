# Binary Trees with Iterators

This is the fifth blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

In this blog post we study binary trees, that is, trees in which each
node has at most two children. We study the in-order tree traversal,
as that will become important when we study binary search trees.
Furthermore, we develop tree iterators that keep track of a location
within the tree and can move forward with respect to the in-order
traversal.

We begin by defining a `union` for binary trees:

```{.deduce #Tree}
union Tree<E> {
  EmptyTree
  TreeNode(Tree<E>, E, Tree<E>)
}
```

For example, we can represent the following binary tree 

![Diagram of a Binary Tree](./BinaryTree05.png)

with a bunch of tree nodes like so:

```{.deduce #BinaryTree05}
define T0 = TreeNode(EmptyTree, 0, EmptyTree)
define T2 = TreeNode(EmptyTree, 2, EmptyTree)
define T1 = TreeNode(T0, 1, T2)
define T5 = TreeNode(EmptyTree, 5, EmptyTree)
define T4 = TreeNode(EmptyTree, 4, T5)
define T3 = TreeNode(T1, 3, T4)
```

We define the height of a tree with the following recursive function.

```{.deduce #height}
function height<E>(Tree<E>) -> Nat {
  height(EmptyTree) = 0
  height(TreeNode(L, x, R)) = suc(max(height(L), height(R)))
}
```

The example tree has height `3`.

```{.deduce #test_height}
assert height(T3) = 3
```

We count the number of nodes in a binary tree with the `num_nodes`
function.

```{.deduce #num_nodes}
function num_nodes<E>(Tree<E>) -> Nat {
  num_nodes(EmptyTree) = 0
  num_nodes(TreeNode(L, x, R)) = suc(num_nodes(L) + num_nodes(R))
}
```

The example tree has `6` nodes.

```{.deduce #test_num_nodes}
assert num_nodes(T3) = 6
```



<!--
```{.deduce file=BinaryTree.pf} 
import Nat

<<Tree>>
<<height>>
<<num_nodes>>
```

```{.deduce file=BinaryTreeTest.pf} 
import Nat
import BinaryTree

<<BinaryTree05>>
<<test_height>>
<<test_num_nodes>>
```
-->
