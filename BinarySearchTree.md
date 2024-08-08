# Binary Search Trees

This is the seventh blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

This post continues on the theme of binary trees, that is trees in
which each node has at most two children. The focus of this post is to
develop a correct binary search tree data structure. That is, we are
going to implement a data structure that supports searching for a
value based on its associated key. The data structure will also
support inserting new values. We will store the keys and their values
in a binary tree and implement `search` and `insert` operations.
These operations are efficient (logarithmic time) when the binary tree
is balanced, but we will save how to balance trees for a later blog
post.

The main idea of a binary search tree comes from the notion of binary
search on a sequence, that is, keep the sequennce in sorted-order and
when searching for a key, start in the middle and go left by half of
the subsequence if the key you're looking for is less than the one at
the current position; go right by half of the subsequence if the key
is greater than the one at the current position. Of course, if they
are equal, then you've found what you're looking for. Thus, binary
search is just like looking up the definition of a word in a
dictionary. The word is your key and the dictionary is sorted
alphabetically. You can start in the middle and compare your word to
those on the current page, then flip to the left or right depending on
whether your word is lower or higher in the alphabet.

The binary search tree adapts the idea of binary search from a
sequence to a tree.  Each node in the tree stores a key and its
value. The left subtree of the node contain keys that are less than
the node and the right subtree contain keys that are greater than the
node. Thus, when searching for a key, one can compare it to the
current node and then either go left or right depending on whether the
key is less-than or greater-than the current node.

Consider the following diagram of a binary search tree. For
simplicity, we will use numbers for both the keys and the values.
In this diagram the key is listed before the colon and the value
is after the colon. For example, this tree contains 

* key `10` associated with value `32`, 
* key `13` associated with value `63`,
* etc.

![Diagram of a Binary Search Tree](./BinarySearchTree1.png)

specification




```{.deduce #all_nodes}
function all_nodes<E>(Tree<E>, fn E -> bool) -> bool {
  all_keys(EmptyTree, P) = true
  all_keys(TreeNode(L, x, R), P) = all_nodes(L, P) and P(x) and all_nodes(R, P)
}
```

```{.deduce #is_BST}
function is_BST(Tree<Pair<Nat,Nat>>) -> bool {
  is_BST(EmptyTree) = true
  is_BST(TreeNode(L, kv, R)) = 
      define k = first(kv) define v = second(kv)
      all_nodes(L, λl{ first(l) < k }) and all_nodes(R, λr{ first(r) > k })
      and is_BST(L) and is_BST(R)
}
```

```
```

<!--
```{.deduce file=BinarySearchTree.pf} 

import BinaryTree

<<all_nodes>>
<<is_BST>>

```

```{.deduce file=BinarySearchTreeTest.pf} 


```
-->


