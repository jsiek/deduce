# Binary Search Trees

This is the seventh blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

## The Search Interface

This post continues on the theme of binary trees, that is, trees in
which each node has at most two children. The focus of this post is
implement the Search interface using binary trees.
The *Search* interface includes operations to 
(1) create an empty data structure,
(2) search for a value based on its associated key, and
(3) insert a new key-value association.

## Function Implmentation of Search

The Search interface can also be implemented in a simple but less
efficient way, using a function to map keys to values. With this
approach, the operation to search for a value is just function call.
The `Maps.pf` file defines the `empty_map` operation, which returns a
function that maps every input to `none`.

```{.deduce #empty_map_5}
assert @empty_map<Nat,Nat>(5) = none
```

The `Maps.pf` file also defined the `update(f, k, v)` operation, which
returns a function that associates the key `k` with `v` but otherwise
behaves like the given function `f`.  Here is an example use of
`update`.

```{.deduce #update_empty_4}
define m2 = update(@empty_map<Nat,Nat>, 4, just(99))
assert m2(4) = just(99)
assert m2(5) = none
```

We will use this function implementation of the Search interface to
specify the correctness of the binary tree implementation of Search.

## Binary Tree Implementation of Search

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
  
* `BST_search : fn Tree<Pair<Nat,Nat>> -> (fn Nat -> Option<Nat>)`

  The operation `BST_search(T)` returns a function that maps each key
  to its associated value.

* `BST_insert : fn Tree<Pair<Nat,Nat>>, Nat, Nat -> Tree<Pair<Nat,Nat>>` 

  The operation `BST_insert(T, k, v)` produces a new tree that
  associates value `v` with key `k` and for all other keys, associates
  keys with the values according to tree `T`. In other words,
  `BST_insert(T, k, v) = update(BST_search(T), k, v)`.


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
theorem BST_search_insert_udpate: all T:Tree<Pair<Nat,Nat>>. all k:Nat, v:Nat.
  BST_search(BST_insert(T, k, v)) = update(BST_search(T), k, just(v))
proof
  induction Tree<Pair<Nat,Nat>>
  case EmptyTree {
    arbitrary k:Nat, v:Nat
    extensionality
    arbitrary i:Nat
    suffices (if i = k then just(v) else (if i < k then @none<Nat> else @none<Nat>)) 
           = (if i = k then just(v) else @none<Nat>)
        with definition {BST_insert, BST_search, BST_search, first, second, update}
    switch i = k {
      case true { . }
      case false {
        switch i < k {
          case true { . }
          case false { . }
        }
      }
    }
  }
  case TreeNode(L, x, R) suppose IH_L, IH_R {
    arbitrary k:Nat, v:Nat
    extensionality
    arbitrary i:Nat
    suffices BST_search(BST_insert(TreeNode(L, x, R), k, v))(i) 
           = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
      by .
    switch k = first(x) for BST_insert {
      case true suppose k_fx_true {
        have k_eq_fx: k = first(x) by rewrite k_fx_true
        suffices BST_search(TreeNode(L, pair(k, v), R))(i) 
               = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)   by .
        cases trichotomy[i][k]
        case i_less_k: i < k {
          have not_i_eq_k: not (i = k)   by apply less_not_equal to i_less_k
          equations
                BST_search(TreeNode(L, pair(k, v), R))(i) 
              = BST_search(L)(i)
                    by _definition {BST_search, first}
                       rewrite not_i_eq_k | i_less_k
          ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
                    by _definition {update,BST_search}
                       rewrite symmetric k_eq_fx | not_i_eq_k | i_less_k
        }
        case i_eq_k: i = k {
          suffices BST_search(TreeNode(L, pair(k, v), R))(k)
                  = update(BST_search(TreeNode(L, x, R)), k, just(v))(k)
                  with rewrite i_eq_k
          equations
            BST_search(TreeNode(L, pair(k, v), R))(k)
              = just(v)          by definition {BST_search, first, second}
          ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(k)
                                 by definition {BST_search, update}
        }
        case k_less_i: k < i {
          ?
        }
      }
      case false suppose k_fx_false {
        ?
      }
    }
    
    /*
    cases trichotomy[i][k]
    case i_less_k: i < k {
      sorry
    }
    case i_eq_k: i = k {
      _rewrite i_eq_k
      switch k = first(x) for BST_search, update {
        case true {
          conclude BST_search(BST_insert(TreeNode(L, x, R), k, v))(k) = just(v)
            by ? 
        }
        case false {
          ?
        }
      }
    }
    case k_less_i: k < i {
      ?
    }
    */
    /*
    switch k = first(x) for BST_insert {
      case true suppose k_fx_true {
         switch i = k {
           case true suppose ik_true {
             have i_k: i = k by rewrite ik_true
             suffices BST_search(TreeNode(L, pair(k, v), R))(k) 
                    = update(BST_search(TreeNode(L, x, R)), k, just(v))(k)
                 with rewrite i_k
             equations 
                    BST_search(TreeNode(L, pair(k, v), R))(k) 
                 = just(v)          by definition {BST_search, first, second}
             ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(k)
                                    by definition {BST_search,update}
           }
           case false {
             switch i < k {
               case true suppose i_k_true {
               
                 suffices BST_search(TreeNode(L, pair(k, v), R))(i) 
                          = update(BST_search(TreeNode(L, x, R)), k, just(v))(i) by .
                 ?
               }
               case false {
                 ?
               }
             }
           }
         }
      }
      case false suppose k_fx_false {
        ?
      }
    }
    */
  }
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
<<BST_search_insert_update>>
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


