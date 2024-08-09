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
support inserting new values. 

This interface can also be implemented in a simple but less efficient
way, using a function to map keys to values. With this approach, the
search operation is just function call.  The `Maps.pf` file defines
two operations to for building such maps. The `empty_map` operation
returns a function that maps every input to `none`.

```{.deduce #empty_map_5}
assert @empty_map<Nat,Nat>(5) = none
```

The `update(f, k, v)` operation returns a function that associates the
key `k` with `v` but otherwise behaves like the given function `f`.
Here is an example use of `update`.

```{.deduce #update_empty_4}
define m2 = update(@empty_map<Nat,Nat>, 4, just(99))
assert m2(4) = just(99)
assert m2(5) = none
```


We will store the keys and their values in a binary tree and implement
`BST_search` and `BST_insert` operations.  These operations are
efficient (logarithmic time) when the binary tree is balanced, but we
will save how to balance trees for a later blog post.

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

The following code builds this binary search tree
using the `Tree` union type defined in the
[Binary Tree](https://siek.blogspot.com/2024/07/binary-trees-with-in-order-iterators.html) 
blog post and the `Pair` type from the `Pair.pf` file.

```{.deduce #BST1}
define mt = @EmptyTree<Pair<Nat,Nat>>
define BST_1 = TreeNode(mt, pair(1, 53), mt)
define BST_9 = TreeNode(mt, pair(9, 42), mt)
define BST_6 = TreeNode(BST_1, pair(6, 85), BST_9)
define BST_11 = TreeNode(mt, pair(11, 99), mt)
define BST_13 = TreeNode(BST_11, pair(13, 69), mt)
define BST_19 = TreeNode(mt, pair(19, 74), mt)
define BST_14 = TreeNode(BST_13, pair(14, 27), BST_19)
define BST_10 = TreeNode(BST_6, pair(10, 32), BST_14)
```

There are three operations in the binary search tree interface and
here are their **specifications**.

* The `EmptyTree` constructor from the `Tree` union type, which builds
  a binary search tree that does not contain any key-value
  associations.
  
* `BST_search : fn Tree<Pair<Nat,Nat>>, Nat -> Option<Nat>`

  The operation `BST_search(T, k)` returns `just(v)` if `v` is the
  value associated with key `k` in tree `T`, and otherwise returns
  `none`.

* `BST_insert : fn Tree<Pair<Nat,Nat>>, Nat, Nat -> Tree<Pair<Nat,Nat>>` 

  The operation `BST_insert(T, k, v)` produces a new tree that
  associates value `v` with key `k` and for all other keys,
  associates keys with the values according to tree `T`.


## Write the `BST_search` and `BST_insert` functions

The `BST_search` function is recursive over the `Tree` parameter.
If the tree is empty, the result is `none`. Otherwise, 
we compare the key `k` with the key in the current node `x`.
If they are equal, return the value in the current node;
if `k` is less-than, recursively search the left subtree;
if `k` is greater-than, recursively search the right subtree.

```{.deduce #BST_search}
function BST_search(Tree<Pair<Nat,Nat>>) -> fn Nat -> Option<Nat> {
  BST_search(EmptyTree) = λk{ none }
  BST_search(TreeNode(L, x, R)) = λk{
    if k = first(x) then
      just(second(x))
    else if k < first(x) then
      BST_search(L)(k)
    else
      BST_search(R)(k)
  }
}
```

The `BST_insert` function follows a similar control structure:
recursive over the `Tree` parameter followed by an `if`-`then`-`else`
based on the key `k` and the key of the current node.
However, `BST_insert` returns a new tree that contains the
specified key and value. When the key `k` is already in the tree,
`BST_insert` overrides the current value with the new value,
as implied by the specification above.

```{.deduce #BST_insert}
function BST_insert(Tree<Pair<Nat,Nat>>, Nat, Nat) -> Tree<Pair<Nat,Nat>> {
  BST_insert(EmptyTree, k, v) = TreeNode(EmptyTree, pair(k, v), EmptyTree)
  BST_insert(TreeNode(L, x, R), k, v) =
    if k = first(x) then
      TreeNode(L, pair(k, v), R)
    else if k < first(x) then
      TreeNode(BST_insert(L, k, v), x, R)
    else
      TreeNode(L, x, BST_insert(R, k, v))
}
```

## Test

We test the correctness of the `EmptyTree`, `BST_search`, and
`BST_insert` operations by making sure they behave according to their
specification. Starting with `EmptyTree`, the result of `BST_search`
with any key should be `none`.

```{.deduce #testBSTSearch1}
assert BST_search(EmptyTree)(5) = none
```

After inserting key `10` with value `32`, the result of `BST_search`
on `10` should be `32`. For other keys, such as `5`, the result 
should be the same as for `EmptyTree`.

```{.deduce #testBSTSearch2}
define BST_a = BST_insert(EmptyTree, 10, 32)
assert BST_search(BST_a)(10) = just(32)
assert BST_search(BST_a)(5) = none
```

The story is similar for inserting key `6` with value `85`.

```{.deduce #testBSTSearch3}
define BST_b = BST_insert(BST_a, 6, 85)
assert BST_search(BST_b)(6) = just(85)
assert BST_search(BST_b)(10) = just(32)
assert BST_search(BST_b)(5) = none
```

If we insert with the same key `6` but a different value `59`,
the result of `BST_search` for `6` should be the new value `59`.
For other keys, the result of `BST_search` remains the same.

```{.deduce #testBSTSearch4}
define BST_c = BST_insert(BST_b, 6, 59)
assert BST_search(BST_c)(6) = just(59)
assert BST_search(BST_c)(10) = just(32)
assert BST_search(BST_c)(5) = none
```

## Prove

Starting with `EmptyTree`, we prove that applying `BST_search`
produces an empty map.

```{.deduce #BST_search_EmptyTree}
theorem BST_search_EmptyTree: 
  BST_search(EmptyTree) = λk{none}
proof
  extensionality
  arbitrary k:Nat
  conclude BST_search(EmptyTree)(k) = none
      by definition BST_search
end
```

```{.deduce #BST_search_insert_update}
theorem BST_search_insert_udpate:
  BST_search(BST_insert(T, k, v), j) = update(BST_search(T), k, just(v))
proof
  ?
end
```


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


<!--
```{.deduce file=BinarySearchTree.pf} 

import BinaryTree
import Maps

<<all_nodes>>
<<is_BST>>
<<BST_search>>
<<BST_insert>>

<<BST_search_EmptyTree>>
```

```{.deduce file=BinarySearchTreeTest.pf} 
import BinarySearchTree
import Maps

<<empty_map_5>>
<<update_empty_4>>

<<BST1>>
<<testBSTSearch1>>
<<testBSTSearch2>>
<<testBSTSearch3>>
<<testBSTSearch4>>

```
-->


