# Balanced Binary Search Trees

This is the eigth blog post in a
[series](https://siek.blogspot.com/2024/06/data-structures-and-algorithms-correctly.html)
about developing correct implementations of basic data structures and
algorithms using the [Deduce](https://github.com/jsiek/deduce)
language and proof checker.

This post builds on the last post about [Binary Search
Trees](https://siek.blogspot.com/2024/08/binary-search-trees-correctly.html).
The focus of this post make sure that the binary trees stay balanced
as we insert key-value associations so that both the search and insert
operation take only logarithmic time. The algorithm that we shall use
for balancing is the one invented by Adelson-Velsky and Landis (AVL),
just because it is one of the more straightforward methods for
balancing.

A binary tree is **balanced** so long as the height of the tree is
less-or-equal to the log of the number of nodes in the tree. This is a
highly permissive notion of balance; it is just what is needed to make
sure that search and insert are fast.

Different balancing algorithms choose to enforce balance in different
ways. They typically maintain a particular invariant on the shape of
the tree, and the chosen invariant implies that the tree is balanced.
The AVL tree invariant is that two siblings only differ in height by
at most 1. Here are four examples of AVL trees:

![Diagram of several AVL trees](https://www.dropbox.com/scl/fi/wh06d9vvdb2b5rkxuebsx/AVLTrees.png?rlkey=6nhmiffmprvgwzvftohwkivqs&raw=1)

Here are three trees that do not satisfy the AVL invariant:

![Diagram of several trees that are not AVL](https://www.dropbox.com/scl/fi/89gyxe2ve6bytmzgml51w/AVLTreeNot.png?rlkey=1vwzdnfgzt61qw8r2zvgo5s7m&raw=1)

The main idea of the AVL algorithm is that we can change the height of
some nodes in the tree without disturbing the ordering of the keys by
means of the following left and right rotations. In the below diagram,
each triangle represents a subtree while the circles represent a
single tree node as usual.

![Diagram of left and right rotation](https://www.dropbox.com/scl/fi/lob6iu0xc8zyg51tlvfqg/Rotate.png?rlkey=de7qa94a2ganr4dustmm30axn&raw=1)

Notice that a right rotation decreases the height of the node labeled
`y` and increases the height of the node labeled `x`.  The left
rotation does the opposite. Also notice that the rotations do not
change the ordering of the tree with respect to an in-order traversal.
The tree on the left has an in-order traversal of `A,x,B,y,C` and so
does the tree on right right. Thus, the search operation will yield
the same results for the two trees.

```{.deduce #rotate_right}
define rotate_right : fn Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>, 
                         Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>,
                         Tree<Pair<Nat,Nat>> -> Tree<Pair<Nat,Nat>>
       = λ A,x,B,y,C {
         TreeNode(A, x, TreeNode(B, y, C))
       }
```

```{.deduce #test_rotate_right}
assert rotate_right(EmptyTree, pair(1,55), EmptyTree, pair(2,37), EmptyTree)
  = TreeNode(EmptyTree, pair(1,55), TreeNode(EmptyTree, pair(2,37), EmptyTree))
```

```{.deduce #rotate_left}
define rotate_left : fn Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>, 
                         Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>,
                         Tree<Pair<Nat,Nat>> -> Tree<Pair<Nat,Nat>>
       = λ A,x,B,y,C {
         TreeNode(TreeNode(A, x, B), y, C)
       }
```

```{.deduce #test_rotate_left}
assert rotate_left(EmptyTree, pair(1,55), EmptyTree, pair(2,37), EmptyTree)
  = TreeNode(TreeNode(EmptyTree, pair(1,55), EmptyTree), pair(2,37), EmptyTree)
```

```{.deduce #rotate_right_on}
define rotate_right_on : fn Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>, 
                         Tree<Pair<Nat,Nat>>) -> Tree<Pair<Nat,Nat>>
   = λ AxB, y, C {
       switch AxB {
         case EmptyTree { EmptyTree } // can't happen
         case TreeNode(A, x, B) {
           rotate_right(A, x, B, y, C)
         }
       }
   }
```

```{.deduce #rotate_left_on}
define rotate_left_on : fn Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>, 
                         Tree<Pair<Nat,Nat>>) -> Tree<Pair<Nat,Nat>>
   = λ A, x, ByC {
       switch ByC {
         case EmptyTree { EmptyTree } // can't happen
         case TreeNode(B, y, C) {
           rotate_left(A, x, B, y, C)
         }
       }
   }
```


```{.deduce #balance}
function balance(Tree<Pair<Nat,Nat>>) -> Tree<Pair<Nat,Nat>> {
  balance(EmptyTree) = EmptyTree
  balance(TreeNode(L, x, R)) =
    if 1 + height(L) < height(R) then
      switch R {
        case EmptyTree { EmptyTree } // can't happen
        case TreeNode(RL, y, RR) {
          if height(RL) ≤ height(RR) then
            rotate_left(L, x, RL, y, RR)
          else
            rotate_left_on(L, x, rotate_right_on(RL, y, RR))
        }
      }
    else
      
}
```




```{.deduce #search_rotate}
theorem search_rotate_right: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>.
  if first(x) < first(y)
  then  BST_search(TreeNode(TreeNode(A, x, B), y, C))
      = BST_search(TreeNode(A, x, TreeNode(B, y, C)))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>
  suppose fx_less_fy
  have not_fx_eq_fy: not (first(x) = first(y))
    by apply less_not_equal to fx_less_fy
  extensionality
  arbitrary i:Nat
  cases trichotomy[i][first(y)]
  case i_less_fy: i < first(y) {
    have not_i_eq_fy: not (i = first(y))
      by apply less_not_equal to i_less_fy
    cases trichotomy[i][first(x)]
    case i_less_fx: i < first(x) {
      have not_i_eq_fx: not (i = first(x))
        by apply less_not_equal to i_less_fx
      equations
            BST_search(TreeNode(TreeNode(A, x, B), y, C))(i)
          = BST_search(A)(i)
            by definition {BST_search,BST_search}
               and rewrite not_i_eq_fy | i_less_fy | not_i_eq_fx | i_less_fx
      ... = BST_search(TreeNode(A, x, TreeNode(B, y, C)))(i)
            by definition {BST_search,BST_search}
               and rewrite not_i_eq_fy | i_less_fy | not_i_eq_fx | i_less_fx
    }
    case i_eq_fx: i = first(x) {
      equations
            BST_search(TreeNode(TreeNode(A, x, B), y, C))(i)
          = just(second(x))
            by definition {BST_search,BST_search}
               and rewrite not_i_eq_fy | i_less_fy | i_eq_fx
      ... = BST_search(TreeNode(A, x, TreeNode(B, y, C)))(i)
            by definition {BST_search,BST_search}
               and rewrite not_i_eq_fy | i_less_fy | i_eq_fx
    }
    case i_greater_fx: first(x) < i {
      have not_i_eq_fx: not (i = first(x))
        by suppose i_eq_fx
           apply (apply less_not_equal to i_greater_fx) to symmetric i_eq_fx
      have not_i_less_fx: not (i < first(x))
        by apply less_implies_not_greater to i_greater_fx
      equations
            BST_search(TreeNode(TreeNode(A, x, B), y, C))(i)
          = BST_search(B)(i)
            by definition {BST_search,BST_search}
               and rewrite not_i_eq_fy | i_less_fy | not_i_eq_fx | not_i_less_fx
      ... = BST_search(TreeNode(A, x, TreeNode(B, y, C)))(i)
            by definition {BST_search,BST_search}
               and rewrite not_i_eq_fy | i_less_fy | not_i_eq_fx | not_i_less_fx
    }
  }
  case i_eq_fy: i = first(y) {
    have i_greater_fx: first(x) < i
      by rewrite symmetric i_eq_fy in fx_less_fy
    have not_i_eq_fx: not (i = first(x))
      by suppose i_eq_fx
         apply (apply less_not_equal to i_greater_fx) to symmetric i_eq_fx
    have not_i_less_fx: not (i < first(x))
      by apply less_implies_not_greater to i_greater_fx
    equations
          BST_search(TreeNode(TreeNode(A, x, B), y, C))(i)
        = just(second(y))
          by definition {BST_search,BST_search}
             and rewrite i_eq_fy | not_i_eq_fx | not_i_less_fx
    ... = BST_search(TreeNode(A, x, TreeNode(B, y, C)))(i)
          by definition {BST_search,BST_search}
             and rewrite not_i_eq_fx | not_i_less_fx | i_eq_fy
  }
  case i_greater_fy: first(y) < i {
    have not_i_eq_fy: not (i = first(y))
      by suppose i_eq_fy
         apply (apply less_not_equal to i_greater_fy) to symmetric i_eq_fy
    have not_i_less_fy: not (i < first(y))
      by apply less_implies_not_greater to i_greater_fy
    have i_greater_fx: first(x) < i
      by apply less_trans to (fx_less_fy, i_greater_fy)
    have not_i_eq_fx: not (i = first(x))
      by suppose i_eq_fx
         apply (apply less_not_equal to i_greater_fx) to symmetric i_eq_fx
    have not_i_less_fx: not (i < first(x))
      by apply less_implies_not_greater to i_greater_fx
    equations
          BST_search(TreeNode(TreeNode(A, x, B), y, C))(i)
        = BST_search(C)(i)
          by definition {BST_search,BST_search}
             and rewrite not_i_eq_fy | not_i_less_fy
    ... = BST_search(TreeNode(A, x, TreeNode(B, y, C)))(i)
          by definition {BST_search,BST_search}
          and rewrite not_i_eq_fy | not_i_less_fy | not_i_eq_fx | not_i_less_fx
  }
end
```

<!--
```{.deduce file=BalancedBST.pf} 

import Maps
import BinaryTree
import BinarySearchTree

<<BST_type>>
<<rotate_right>>
<<rotate_left>>

<<search_rotate>>

```
-->

<!--
```{.deduce file=BalancedBSTTest.pf} 
import Maps
import BinaryTree
import BinarySearchTree
import BalancedBST

<<test_rotate_right>>
<<test_rotate_left>>

```
-->
