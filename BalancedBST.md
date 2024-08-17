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

## Write

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
                         Tree<Pair<Nat,Nat>> -> Tree<Pair<Nat,Nat>>
   = λ AxB, y, C {
       switch AxB {
         case EmptyTree { TreeNode(EmptyTree, y, C) }
         case TreeNode(A, x, B) {
           rotate_right(A, x, B, y, C)
         }
       }
   }
```

```{.deduce #rotate_left_on}
define rotate_left_on : fn Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>, 
                         Tree<Pair<Nat,Nat>> -> Tree<Pair<Nat,Nat>>
   = λ A, x, ByC {
       switch ByC {
         case EmptyTree { TreeNode(A, x, EmptyTree) }
         case TreeNode(B, y, C) {
           rotate_left(A, x, B, y, C)
         }
       }
   }
```


```{.deduce #balance}
define balance : fn Tree<Pair<Nat,Nat>>, Pair<Nat,Nat>, 
                    Tree<Pair<Nat,Nat>> -> Tree<Pair<Nat,Nat>>
  = λ L, x, R {
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
    else if 1 + height(R) < height(L) then
      switch L {
        case EmptyTree { EmptyTree } // can't happen
        case TreeNode(LL, z, LR) {
          if height(LR) ≤ height(LL) then
            rotate_right(LL, z, LR, x, R)
          else
            rotate_right_on(rotate_left_on(LL, z, LR), x, R)
        }
      }
    else // already balanced
      TreeNode(L, x, R)
    }
```

```{.deduce #AVL_insert}
function AVL_insert(Tree<Pair<Nat,Nat>>, Nat, Nat) -> Tree<Pair<Nat,Nat>> {
  AVL_insert(EmptyTree, k, v) = TreeNode(EmptyTree, pair(k, v), EmptyTree)
  AVL_insert(TreeNode(L, x, R), k, v) =
    if k = first(x) then
      TreeNode(L, pair(k, v), R)
    else if k < first(x) then
      balance(AVL_insert(L, k, v), x, R)
    else
      balance(L, x, AVL_insert(R, k, v))
}
```


## Test


## Prove

```{.deduce #search_rotate}
theorem search_rotate: 
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

```{.deduce #search_rotate_right}
theorem search_rotate_right: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>.
  if first(x) < first(y)
  then  BST_search(TreeNode(TreeNode(A, x, B), y, C))
      = BST_search(rotate_right(A, x, B, y, C))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>
  suppose prem
  suffices BST_search(TreeNode(TreeNode(A, x, B), y, C))
         = BST_search(TreeNode(A, x, TreeNode(B, y, C)))
    with definition rotate_right
  apply search_rotate[A,x,B,y,C] to prem
end
```

```{.deduce #search_rotate_left}
theorem search_rotate_left: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>.
  if first(x) < first(y)
  then  BST_search(rotate_left(A, x, B, y, C))
      = BST_search(TreeNode(A, x, TreeNode(B, y, C)))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>
  suppose prem
  suffices BST_search(TreeNode(TreeNode(A, x, B), y, C))
         = BST_search(TreeNode(A, x, TreeNode(B, y, C)))
    with definition rotate_left
  apply search_rotate[A,x,B,y,C] to prem
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
  is_BST(TreeNode(L, x, R)) = 
      all_nodes(L, λl{ first(l) < first(x) }) 
      and all_nodes(R, λr{ first(x) < first(r) })
      and is_BST(L) 
      and is_BST(R)
}
```

```{.deduce #search_rotate_right_on}
theorem search_rotate_right_on: 
  all AxB:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(AxB, y, C))
  and 0 < height(AxB)
  then  BST_search(TreeNode(AxB, y, C))
      = BST_search(rotate_right_on(AxB, y, C))
proof
  arbitrary AxB:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>
  suppose prem
  switch AxB {
    case EmptyTree suppose AxB_empty {
      conclude false
        by definition {operator<, operator≤, height} in 
           rewrite AxB_empty in prem
    }
    case TreeNode(A, x, B) suppose AxB_node {
      have fx_less_fy: first(x) < first(y)
        by definition {is_BST, is_BST, all_nodes} in rewrite AxB_node in prem
      suffices BST_search(TreeNode(TreeNode(A, x, B), y, C)) 
             = BST_search(rotate_right(A, x, B, y, C))
          with definition rotate_right_on
      apply search_rotate_right[A,x,B,y,C] to fx_less_fy
    }
  }
end
```

```{.deduce #search_rotate_left_on}
theorem search_rotate_left_on: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      ByC:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(A, x, ByC))
  and 0 < height(ByC)
  then  BST_search(rotate_left_on(A, x, ByC))
      = BST_search(TreeNode(A, x, ByC))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      ByC:Tree<Pair<Nat,Nat>>
  suppose prem
  switch ByC {
    case EmptyTree suppose ByC_empty {
      conclude false
        by definition {operator<, operator≤, height} in 
           rewrite ByC_empty in prem
    }
    case TreeNode(B, y, C) suppose ByC_node {
      have fx_less_fy: first(x) < first(y)
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      suffices BST_search(rotate_left(A, x, B, y, C)) 
             = BST_search(TreeNode(A, x, TreeNode(B, y, C)))
          with definition rotate_left_on
      apply search_rotate_left[A,x,B,y,C] to fx_less_fy
    }
  }
end
```

```{.deduce #search_node}
define search_node : fn (fn Nat -> Option<Nat>), Pair<Nat,Nat>, (fn Nat -> Option<Nat>) -> (fn Nat -> Option<Nat>)
   = λ L, x, R {
       λ k {
        if k = first(x) then
          just(second(x))
        else if k < first(x) then
          L(k)
        else
          R(k)
       }
     }
```

```{.deduce #search_compositional}
theorem search_compositional: all L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>.
  BST_search(TreeNode(L, x, R)) = search_node(BST_search(L), x, BST_search(R))
proof
  arbitrary L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>
  definition {search_node, BST_search}
end
```

```{.deduce #rotate_right_on_height}
theorem rotate_right_on_height: all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>.
  if 0 < height(A)
  then 0 < height(rotate_right_on(A, x, B))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>
  suppose hA_pos
  switch A for rotate_right_on {
    case EmptyTree suppose A_empty {
      conclude false
        by definition {height, operator<, operator≤} in rewrite A_empty in hA_pos
    }
    case TreeNode(AL, y, AR) suppose A_node {
      conclude 0 < height(rotate_right(AL, y, AR, x, B))
          by definition {rotate_right, height, height, operator<, operator≤, operator≤}
    }
  }
end
```

```{.deduce #rotate_left_on_height}
theorem rotate_left_on_height: all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>.
  if 0 < height(B)
  then 0 < height(rotate_left_on(A, x, B))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>
  suppose hB_pos
  switch B for rotate_left_on {
    case EmptyTree suppose B_empty {
      conclude false
        by definition {height, operator<, operator≤} in rewrite B_empty in hB_pos
    }
    case TreeNode(BL, y, BR) suppose B_node {
      conclude 0 < height(rotate_left(A, x, BL, y, BR))
          by definition {rotate_left, height, height, operator<, operator≤, operator≤}
    }
  }
end
```

```{.deduce #all_nodes_rotate_right_on}
theorem all_nodes_rotate_right_on: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, 
      P:fn Pair<Nat,Nat>->bool.
  all_nodes(rotate_right_on(A, x, B), P)
  = all_nodes(TreeNode(A, x, B), P)
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, P:fn Pair<Nat,Nat>->bool
  _definition rotate_right_on
  switch A {
    case EmptyTree {
      .
    }
    case TreeNode(L, y, R) {
      definition {rotate_right, all_nodes, all_nodes}
    }
  }
end
```

```{.deduce #all_nodes_rotate_left_on}
theorem all_nodes_rotate_left_on: all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, P:fn Pair<Nat,Nat>->bool.
  all_nodes(rotate_left_on(A, x, B), P)
  = all_nodes(TreeNode(A, x, B), P)
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, P:fn Pair<Nat,Nat>->bool
  _definition rotate_left_on
  switch B {
    case EmptyTree {
      .
    }
    case TreeNode(L, y, R) {
      definition {rotate_left, all_nodes, all_nodes}
    }
  }
end
```

```{.deduce #all_nodes_implies}
theorem all_nodes_implies: all T:type. all A:Tree<T>.
  all P: fn T -> bool, Q: fn T -> bool.
  if all_nodes(A,P) and (all z:T. if P(z) then Q(z))
  then all_nodes(A,Q)
proof
  arbitrary T:type
  induction Tree<T>
  case EmptyTree {
    arbitrary P: fn T -> bool, Q: fn T -> bool
    suppose prem
    definition all_nodes
  }
  case TreeNode(L, x, R) suppose IH_L, IH_R {
    arbitrary P: fn T -> bool, Q: fn T -> bool
    suppose prem
    suffices all_nodes(L, Q) and Q(x) and all_nodes(R, Q)
        with definition all_nodes
    have Px: P(x) by definition all_nodes in prem
    have Qx: Q(x) by apply (conjunct 1 of prem)[x] to Px
    have R_P: all_nodes(R, P) by definition all_nodes in prem
    have L_P: all_nodes(L, P) by definition all_nodes in prem
    have R_Q: all_nodes(R, Q) by apply IH_R[P,Q] to (R_P, prem)
    have L_Q: all_nodes(L, Q) by apply IH_L[P,Q] to (L_P, prem)
    L_Q, Qx, R_Q
  }
end
```

```{.deduce #is_BST_rotate_left}
theorem is_BST_rotate_left: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(A, x, TreeNode(B, y, C)))
  then is_BST(rotate_left(A, x, B, y, C))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>
  suppose BST_AxByC
  suffices all_nodes(A, λl{first(l) < first(y)}) 
       and first(x) < first(y) 
       and all_nodes(B, λl{first(l) < first(y)}) 
       and all_nodes(C, λr{first(y) < first(r)}) 
       and all_nodes(A, λl{first(l) < first(x)}) 
       and all_nodes(B, λr{first(x) < first(r)}) 
       and is_BST(A) 
       and is_BST(B) 
       and is_BST(C)
              with definition {rotate_left, is_BST, is_BST, all_nodes}
  have x_less_y: first(x) < first(y) 
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  have A_less_x: all_nodes(A, λl{first(l) < first(x)}) 
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  have A_less_y: all_nodes(A, λl{first(l) < first(y)}) by
       define belowY = λl{first(l) < first(y)} : fn Pair<Nat,Nat> -> bool 
       define belowX = λl{first(l) < first(x)} : fn Pair<Nat,Nat> -> bool
       have belowX_implies_belowY: (all z:Pair<Nat,Nat>. if belowX(z) then belowY(z))
         by arbitrary z:Pair<Nat,Nat>
            suppose z_belowX
            have z_l_x: first(z) < first(x)  by definition belowX in z_belowX
            suffices first(z) < first(y)  with definition belowY
            apply less_trans to z_l_x, x_less_y
       apply all_nodes_implies<Pair<Nat,Nat>>[A][belowX, belowY]
       to (A_less_x, belowX_implies_belowY)
  have B_less_y: all_nodes(B, λl{first(l) < first(y)}) 
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  have y_less_C: all_nodes(C, λr{first(y) < first(r)}) 
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  have x_less_B: all_nodes(B, λr{first(x) < first(r)}) 
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  have BST_A: is_BST(A)
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  have BST_B: is_BST(B)
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  have BST_C: is_BST(C)
    by definition {is_BST, is_BST, all_nodes} in BST_AxByC
  A_less_y, x_less_y, B_less_y, y_less_C, A_less_x, x_less_B, BST_A, BST_B, BST_C
end
```

```{.deduce #is_BST_rotate_right}
theorem is_BST_rotate_right: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(TreeNode(A, x, B), y, C))
  then is_BST(rotate_right(A, x, B, y, C))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      B:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, 
      C:Tree<Pair<Nat,Nat>>
  suppose prem

  suffices all_nodes(A, λl{first(l) < first(x)}) 
       and all_nodes(B, λr{first(x) < first(r)}) 
       and first(x) < first(y) 
       and all_nodes(C, λr{first(x) < first(r)}) 
       and is_BST(A) 
       and all_nodes(B, λl{first(l) < first(y)}) 
       and all_nodes(C, λr{first(y) < first(r)}) 
       and is_BST(B) 
       and is_BST(C)
              with definition {rotate_right, is_BST, is_BST, all_nodes}
  have A_less_x: all_nodes(A, λl{first(l) < first(x)})
    by definition {is_BST, is_BST} in prem
  have x_less_B: all_nodes(B, λr{first(x) < first(r)}) 
    by definition {is_BST, is_BST} in prem
  have fx_less_fy: first(x) < first(y) 
    by definition {is_BST, is_BST, all_nodes} in prem
  have BST_A: is_BST(A) 
    by definition {is_BST, is_BST} in prem
  have B_less_y: all_nodes(B, λl{first(l) < first(y)}) 
    by definition {is_BST, is_BST, all_nodes} in prem
  have y_less_C: all_nodes(C, λr{first(y) < first(r)}) 
    by definition {is_BST, is_BST} in prem
  have x_less_C: all_nodes(C, λr{first(x) < first(r)}) 
    by define aboveY = λr{first(y) < first(r)} : fn Pair<Nat,Nat> -> bool 
       define aboveX = λr{first(x) < first(r)} : fn Pair<Nat,Nat> -> bool 
       have above_y_implies_above_x: (all z:Pair<Nat,Nat>. if aboveY(z) then aboveX(z))
          by arbitrary z:Pair<Nat,Nat>
             suppose z_aboveY
             have y_less_z: first(y) < first(z)  by definition aboveY in z_aboveY
             suffices first(x) < first(z)  with definition aboveX
             apply less_trans to fx_less_fy, y_less_z
       apply all_nodes_implies< Pair<Nat,Nat> >[C][aboveY, aboveX]
       to (y_less_C, above_y_implies_above_x)
  have BST_B: is_BST(B)
    by definition {is_BST, is_BST} in prem
  have BST_C: is_BST(C)
    by definition {is_BST, is_BST} in prem
  (A_less_x, x_less_B, fx_less_fy, x_less_C, BST_A, B_less_y, y_less_C, BST_B, BST_C)

end
```


```{.deduce #is_BST_rotate_right_on}
theorem is_BST_rotate_right_on: 
  all AxB:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, C:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(AxB, y, C))
  then is_BST(rotate_right_on(AxB, y, C))
proof
  arbitrary AxB:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, C:Tree<Pair<Nat,Nat>>
  suppose prem
  switch AxB for rotate_right_on {
    case EmptyTree {
      suffices all_nodes(C, λr{first(y) < first(r)}) and is_BST(C)
          with definition {is_BST, all_nodes, is_BST}
      definition is_BST in prem
    }
    case TreeNode(A, x, B) suppose AxB_node {
      apply is_BST_rotate_right to (rewrite AxB_node in prem)
    }
  }
end
```

```{.deduce #is_BST_rotate_left_on}
theorem is_BST_rotate_left_on: all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, ByC:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(A, x, ByC))
  then is_BST(rotate_left_on(A, x, ByC))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, ByC:Tree<Pair<Nat,Nat>>
  suppose prem
  switch ByC for rotate_left_on {
    case EmptyTree {
      suffices all_nodes(A, λl{first(l) < first(x)}) and is_BST(A)
          with definition {is_BST, all_nodes, is_BST}
      definition is_BST in prem
    }
    case TreeNode(B, y, C) suppose ByC_node {
      apply is_BST_rotate_left to (rewrite ByC_node in prem)
    }
  }
end
```

```{.deduce #search_balance_tall_right}
    switch R {
      case EmptyTree suppose R_mt {
        conclude false 
          by definition {operator <, operator+, height, operator≤} in
             rewrite R_mt in tall_right
      }
      case TreeNode(RL, y, RR) suppose R_node {
        switch height(RL) ≤ height(RR) {
          case true suppose hRL_hRR {
            suffices BST_search(TreeNode(L, x, TreeNode(RL, y, RR)))
                = BST_search(rotate_left(L, x, RL, y, RR))
                with definition balance
                and rewrite (rewrite R_node in tall_right) | hRL_hRR
            have fx_less_fy: first(x) < first(y)
              by rewrite R_node in definition {is_BST,all_nodes} in BST_LxR
            symmetric apply search_rotate_left[L,x,RL,y,RR] to fx_less_fy
          }
          case false suppose hRL_hRR {
            suffices BST_search(TreeNode(L, x, TreeNode(RL, y, RR))) 
                   = BST_search(rotate_left_on(L, x, rotate_right_on(RL, y, RR)))
                with definition balance
                 and rewrite (rewrite R_node in tall_right) | hRL_hRR
            have hRL_pos: 0 < height(RL) by
                have hRR_less_hRL: height(RR) < height(RL) by
                   apply not_less_equal_greater 
                   to (conclude not (height(RL) ≤ height(RR)) by rewrite hRL_hRR)
                apply greater_any_zero to hRR_less_hRL
            have BST_RLyRR: is_BST(TreeNode(RL, y, RR))
              by definition is_BST in rewrite R_node in BST_LxR
            have _1: BST_search(TreeNode(RL, y, RR))
                 = BST_search(rotate_right_on(RL, y, RR))
                 by apply search_rotate_right_on to (BST_RLyRR, hRL_pos)
            have BST_LxRR: is_BST(TreeNode(L,x,rotate_right_on(RL, y, RR)))
               by _definition is_BST
                  have L_less_x: all_nodes(L, λl{first(l) < first(x)})
                    by definition is_BST in BST_LxR
                  have BST_L: is_BST(L) by definition is_BST in BST_LxR
                  have x_less_RLyRR: all_nodes(TreeNode(RL, y, RR), λr{first(x) < first(r)})
                    by definition is_BST in rewrite R_node in BST_LxR
                  have x_l_RR: all_nodes(rotate_right_on(RL, y, RR), λr{first(x) < first(r)}) 
                    by rewrite symmetric all_nodes_rotate_right_on[RL,y,RR, λr{first(x) < first(r)}] 
                       in x_less_RLyRR
                  have BST_RR: is_BST(rotate_right_on(RL, y, RR))
                    by apply is_BST_rotate_right_on[RL,y,RR] to BST_RLyRR
                  L_less_x, BST_L, x_less_RLyRR, x_l_RR, BST_RR
            have hRR_pos: 0 < height(rotate_right_on(RL, y, RR))
               by apply rotate_right_on_height[RL,y,RR] to hRL_pos
            have _2: BST_search(rotate_left_on(L, x, rotate_right_on(RL, y, RR)))
                   = BST_search(TreeNode(L, x, rotate_right_on(RL, y, RR)))
                 by apply search_rotate_left_on to (BST_LxRR, hRR_pos)
            equations
                  BST_search(TreeNode(L, x, TreeNode(RL, y, RR))) 
                = search_node(BST_search(L), x, BST_search(TreeNode(RL, y, RR)))
                  by search_compositional[L,x,TreeNode(RL, y, RR)]
            ... = search_node(BST_search(L), x, BST_search(rotate_right_on(RL, y, RR)))
                  by rewrite _1
            ... = BST_search(TreeNode(L, x, rotate_right_on(RL, y, RR)))
                  by symmetric search_compositional[L,x,rotate_right_on(RL, y, RR)]
            ... = BST_search(rotate_left_on(L, x, rotate_right_on(RL, y, RR)))
                  by symmetric _2
          }
        }
      }
    }
```

```{.deduce #search_balance_tall_left}
    switch L {
      case EmptyTree suppose L_mt {
        conclude false
          by definition {height, operator<, operator≤} in rewrite L_mt in tall_left
      }
      case TreeNode(LL, z, LR) suppose L_node {
        have fz_less_fx: first(z) < first(x)
          by rewrite L_node in definition {is_BST,all_nodes} in BST_LxR
        switch height(LR) ≤ height(LL) {
          case true suppose tall_LL {
            suffices BST_search(TreeNode(TreeNode(LL, z, LR), x, R)) 
                   = BST_search(rotate_right(LL, z, LR, x, R))
              with definition balance
              and rewrite (rewrite L_node in not_tall_right) | rewrite L_node in tall_left | tall_LL
            apply search_rotate_right[LL,z,LR,x,R] to fz_less_fx
          }
          case false suppose not_tall_LL {
            suffices BST_search(TreeNode(TreeNode(LL, z, LR), x, R)) 
                   = BST_search(rotate_right_on(rotate_left_on(LL, z, LR), x, R))
              with definition balance
              and rewrite (rewrite L_node in not_tall_right) | rewrite L_node in tall_left | not_tall_LL
            // premises of search_rotate_left_on
            have BST_LLzLR: is_BST(TreeNode(LL,z,LR))
              by definition is_BST in rewrite L_node in BST_LxR
            have hLR_pos: 0 < height(LR) by
                have LL_l_LR: height(LL) < height(LR) by
                    apply not_less_equal_greater
                    to (conclude not (height(LR) ≤ height(LL)) by rewrite not_tall_LL)
                apply greater_any_zero to LL_l_LR
            // premises of search_rotate_right_on
            have BST_RLxR: is_BST(TreeNode(rotate_left_on(LL, z, LR), x, R)) by
                _definition is_BST
                have LLzLR_less_x: all_nodes(TreeNode(LL, z, LR), λl{first(l) < first(x)})
                    by definition is_BST in rewrite L_node in BST_LxR
                have RL_l_x: all_nodes(rotate_left_on(LL, z, LR), λl{first(l) < first(x)}) 
                  by rewrite symmetric all_nodes_rotate_left_on[LL,z,LR, λl{first(l) < first(x)}]
                     in LLzLR_less_x
                have x_less_R: all_nodes(R, λr{first(x) < first(r)}) 
                  by definition is_BST in rewrite L_node in BST_LxR
                have BST_RL:  is_BST(rotate_left_on(LL, z, LR)) 
                  by apply is_BST_rotate_left_on[LL,z,LR] to BST_LLzLR
                have BST_R: is_BST(R)
                  by definition is_BST in rewrite L_node in BST_LxR
                RL_l_x, x_less_R, BST_RL, BST_R
            have hRL_pos: 0 < height(rotate_left_on(LL, z, LR))
                by apply rotate_left_on_height[LL,z,LR] to hLR_pos
            equations
                  BST_search(TreeNode(TreeNode(LL, z, LR), x, R)) 
                = search_node(BST_search(TreeNode(LL, z, LR)), x, BST_search(R))
                   by search_compositional[TreeNode(LL, z, LR), x, R]
            ... = search_node(BST_search(rotate_left_on(LL, z, LR)), x, BST_search(R))
                   by rewrite symmetric (apply search_rotate_left_on to (BST_LLzLR, hLR_pos))
            ... = BST_search(TreeNode(rotate_left_on(LL, z, LR), x, R))
                   by symmetric search_compositional[rotate_left_on(LL, z, LR), x, R]
            ... = BST_search(rotate_right_on(rotate_left_on(LL, z, LR), x, R))
                   by rewrite (apply search_rotate_right_on to (BST_RLxR, hRL_pos))
          }
        }
      }
    }
```

```{.deduce #search_balance}
theorem search_balance:
    all L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(L, x, R))
  then
    BST_search(TreeNode(L, x, R))
  = BST_search(balance(L, x, R))
proof
  arbitrary L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>
  suppose BST_LxR
  switch 1 + height(L) < height(R) {
    case true suppose tall_right {
      <<search_balance_tall_right>>
    }
    case false suppose not_tall_right {
      switch 1 + height(R) < height(L) {
        case true suppose tall_left {
          <<search_balance_tall_left>>
        }
        case false suppose not_tall_left {
          definition balance
          and rewrite not_tall_right | not_tall_left
        }
      }
    }
  }
end
```
```{.deduce #is_BST_balance}
theorem is_BST_balance: all L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>.
  if is_BST(TreeNode(L, x, R))
  then is_BST(balance(L, x, R))
proof
  arbitrary L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>
  suppose BST_LxR
  have BST_L: is_BST(L) by definition is_BST in BST_LxR
  have BST_R: is_BST(R) by definition is_BST in BST_LxR
  have L_less_x: all_nodes(L, λl{first(l) < first(x)})
    by definition is_BST in BST_LxR
  have x_less_R: all_nodes(R, λr{first(x) < first(r)}) 
    by definition is_BST in BST_LxR
  
  switch 1 + height(L) < height(R) {
    case true suppose tall_right {
      switch R {
        case EmptyTree suppose R_mt {
          suffices is_BST(EmptyTree)
              with definition balance
               and rewrite (rewrite R_mt in tall_right)
          definition is_BST
        }
        case TreeNode(RL, z, RR) suppose R_node {
          switch height(RL) ≤ height(RR) {
            case true suppose tall_RR {
              suffices is_BST(rotate_left(L, x, RL, z, RR))
                  with definition balance
                  and rewrite (rewrite R_node in tall_right) | tall_RR
              have BST_LxRLzRR: is_BST(TreeNode(L, x, TreeNode(RL, z, RR)))
                by _definition {is_BST,all_nodes,is_BST}
                   definition {is_BST, is_BST, all_nodes} in rewrite R_node in BST_LxR
              apply is_BST_rotate_left to BST_LxRLzRR
            }
            case false suppose tall_RL {
              suffices is_BST(rotate_left_on(L, x, rotate_right_on(RL, z, RR)))
                  with definition balance
                  and rewrite (rewrite R_node in tall_right) | tall_RL
              have BST_RLzRR: is_BST(TreeNode(RL, z, RR))
                by definition is_BST in rewrite R_node in BST_LxR
              have BST_rr_RLzRR: is_BST(rotate_right_on(RL, z, RR))
                by apply is_BST_rotate_right_on to BST_RLzRR
              have BST_Lx_rr_RLzRR: is_BST(TreeNode(L, x, rotate_right_on(RL, z, RR))) by
                   _definition is_BST
                   have x_less_rr_RLzRR: all_nodes(rotate_right_on(RL, z, RR),
                                                   λr{first(x) < first(r)}) by
                       suffices all_nodes(TreeNode(RL, z, RR), λr{first(x) < first(r)})
                           with rewrite all_nodes_rotate_right_on[RL,z,RR, λr{first(x)<first(r)}]
                       definition is_BST in rewrite R_node in BST_LxR
                   L_less_x, x_less_rr_RLzRR, BST_L, BST_rr_RLzRR
              apply is_BST_rotate_left_on to BST_Lx_rr_RLzRR
            }
          }
        }
      }
    }
    case false suppose not_tall_right {
      switch 1 + height(R) < height(L) {
        case true suppose tall_left {
          switch L {
            case EmptyTree suppose L_mt {
              suffices is_BST(EmptyTree)
                  with definition balance
                  and rewrite (rewrite L_mt in not_tall_right) | (rewrite L_mt in tall_left)
              definition is_BST
            }
            case TreeNode(LL, z, LR) suppose L_node {
              switch height(LR) ≤ height(LL) {
                case true suppose tall_LL {
                  suffices is_BST(rotate_right(LL, z, LR, x, R))
                      with definition balance
                      and rewrite (rewrite L_node in not_tall_right)
                          | (rewrite L_node in tall_left)
                          | tall_LL
                  have BST_LLzLRxR: is_BST(TreeNode(TreeNode(LL, z, LR), x, R))
                    by _definition {is_BST, is_BST, all_nodes, all_nodes}
                       definition {is_BST,is_BST, all_nodes,all_nodes} in
                       rewrite L_node in BST_LxR
                  apply is_BST_rotate_right to BST_LLzLRxR
                }
                case false suppose tall_LR {
                  suffices is_BST(rotate_right_on(rotate_left_on(LL, z, LR), x, R))
                       with definition balance
                       and rewrite (rewrite L_node in not_tall_right)
                            | (rewrite L_node in tall_left)
                            | tall_LR
                  have BST_LLzRL: is_BST(TreeNode(LL, z, LR))
                    by definition is_BST in rewrite L_node in BST_LxR
                  have BST_rl_LLzLR: is_BST(rotate_left_on(LL, z, LR))
                    by apply is_BST_rotate_left_on to BST_LLzRL
                  have BST_rlLLzLR_x_R: is_BST(TreeNode(rotate_left_on(LL, z, LR), x, R))
                    by _definition is_BST
                       have LLzLR_less_x: all_nodes(TreeNode(LL, z, LR), λl{first(l) < first(x)})
                         by definition is_BST in rewrite L_node in BST_LxR
                       have rlLLzLR_less_x:
                           all_nodes(rotate_left_on(LL, z, LR), λl{first(l) < first(x)}) by
                         _rewrite all_nodes_rotate_left_on[LL,z,LR, λl{first(l) < first(x)}]
                         LLzLR_less_x
                       rlLLzLR_less_x, x_less_R, BST_rl_LLzLR, BST_R
                  apply is_BST_rotate_right_on to BST_rlLLzLR_x_R
                }
              }
            }
          }
        }
        case false suppose not_tall_left {
          _definition balance
          _rewrite not_tall_right | not_tall_left
          BST_LxR
        }
      }
    }
  }
end
```

```{.deduce #all_nodes_balance}
theorem all_nodes_balance:
    all L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>,P:fn Pair<Nat,Nat>->bool.
  if all_nodes(TreeNode(L, x, R), P)
  then all_nodes(balance(L, x, R), P)
proof
  arbitrary L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>,
     P:fn Pair<Nat,Nat>->bool
  suppose prem
  switch 1 + height(L) < height(R) {
    case true suppose tall_right {
      switch R {
        case EmptyTree suppose R_mt {
          suffices all_nodes(@EmptyTree<Pair<Nat,Nat>>, P)
              with definition balance
              and rewrite (rewrite R_mt in tall_right)
          definition all_nodes
        }
        case TreeNode(RL, z, RR) suppose R_node {
          switch height(RL) ≤ height(RR) {
            case true suppose tall_RR {
              _definition balance
              _rewrite (rewrite R_node in tall_right) | tall_RR
              _definition {rotate_left, all_nodes, all_nodes}
              definition {all_nodes, all_nodes} in rewrite R_node in prem
            }
            case false suppose tall_RL {
              _definition balance
              _rewrite (rewrite R_node in tall_right) | tall_RL
              _rewrite all_nodes_rotate_left_on[L,x,rotate_right_on(RL, z, RR),P]
              _definition all_nodes
              _rewrite all_nodes_rotate_right_on[RL,z,RR,P]
              _definition all_nodes
              definition {all_nodes, all_nodes} in rewrite R_node in prem
            }
          }
        }
      }
    }
    case false suppose not_tall_right {
      switch 1 + height(R) < height(L) {
        case true suppose tall_left {
          switch L {
            case EmptyTree suppose L_mt {
              _definition {balance, all_nodes}
              rewrite (rewrite L_mt in not_tall_right) | (rewrite L_mt in tall_left)
            }
            case TreeNode(LL, z, LR) suppose L_node {
              _definition {balance, all_nodes}
              _rewrite (rewrite L_node in not_tall_right) | (rewrite L_node in tall_left)
              switch height(LR) ≤ height(LL) {
                case true suppose tall_LL {
                  _definition {rotate_right, all_nodes}
                  definition {all_nodes, all_nodes} in rewrite L_node in prem
                }
                case false suppose tall_LR {
                  _rewrite all_nodes_rotate_right_on[rotate_left_on(LL, z, LR),x,R,P]
                  _definition all_nodes
                  _rewrite all_nodes_rotate_left_on[LL, z, LR, P]
                  _definition all_nodes
                  definition {all_nodes,all_nodes} in rewrite L_node in prem
                }
              }
            }
          }
        }
        case false suppose not_tall_left {
          suffices all_nodes(TreeNode(L, x, R), P)
              with definition balance
              and rewrite not_tall_right | not_tall_left
          prem
        }
      }
    }
  }
end
```

```{.deduce #all_nodes_AVL_insert}
theorem all_nodes_AVL_insert: 
  all A:Tree<Pair<Nat,Nat>>.
  all k:Nat, v:Nat, P:fn Pair<Nat,Nat>->bool.
  if all_nodes(A, P) and P(pair(k,v))
  then all_nodes(AVL_insert(A, k, v), P)
proof
  induction Tree<Pair<Nat,Nat>>
  case EmptyTree {
    arbitrary k:Nat, v:Nat, P:fn Pair<Nat,Nat>->bool
    suppose prem
    suffices P(pair(k,v))
        with definition {AVL_insert, all_nodes, all_nodes}
    prem
  }
  case TreeNode(L, x, R) suppose IH_L, IH_R {
    arbitrary k:Nat, v:Nat, P:fn Pair<Nat,Nat>->bool
    suppose prem
    cases trichotomy[k][first(x)]
    case k_less_x: k < first(x) {
      have not_k_eq_x: not (k = first(x))  by apply less_not_equal to k_less_x
      suffices all_nodes(balance(AVL_insert(L, k, v), x, R), P)
          with definition AVL_insert
          and rewrite not_k_eq_x | k_less_x
      have insL_P: all_nodes(AVL_insert(L, k, v), P)
        by apply IH_L[k,v,P] to (definition all_nodes in prem)
      have insLxR_P: all_nodes(TreeNode(AVL_insert(L, k, v), x, R), P)
        by _definition all_nodes
           insL_P, (definition all_nodes in prem)
      apply all_nodes_balance to insLxR_P
    }
    case k_eq_x: k = first(x) {
      suffices all_nodes(L, P) and P(pair(first(x), v)) and all_nodes(R, P)
          with definition {AVL_insert, all_nodes} and rewrite k_eq_x
      rewrite k_eq_x in definition all_nodes in prem
    }
    case k_greater_x: first(x) < k {
      have not_k_less_x: not (k < first(x))   by apply less_implies_not_greater to k_greater_x
      have not_k_eq_x: not (k = first(x))
         by suppose k_eq_x
            apply (apply less_not_equal to k_greater_x) to symmetric k_eq_x
      suffices all_nodes(balance(L, x, AVL_insert(R, k, v)), P)
          with definition AVL_insert
          and rewrite not_k_eq_x | not_k_less_x
      have insR_P: all_nodes(AVL_insert(R, k, v), P)
        by apply IH_R[k,v,P] to (definition all_nodes in prem)
      have LxinsR_P: all_nodes(TreeNode(L, x, AVL_insert(R, k, v)), P)
        by _definition all_nodes
           (definition all_nodes in prem), insR_P
      apply all_nodes_balance to LxinsR_P
    }
  }
end
```

```{.deduce #is_BST_AVL_insert}
theorem is_BST_AVL_insert: all A:Tree<Pair<Nat,Nat>>. all k:Nat, v:Nat.
   if is_BST(A)
   then is_BST(AVL_insert(A, k, v))
proof
  induction Tree<Pair<Nat,Nat>>
  case EmptyTree {
    arbitrary k:Nat, v:Nat
    suppose _
    definition {AVL_insert, is_BST, all_nodes, is_BST}
  }
  case TreeNode(L, x, R) suppose IH_L, IH_R {
    arbitrary k:Nat, v:Nat
    suppose BST_LxR
    have BST_L: is_BST(L) by definition is_BST in BST_LxR
    have BST_R: is_BST(R) by definition is_BST in BST_LxR
    have L_less_x: all_nodes(L, λl{first(l) < first(x)})
      by definition is_BST in BST_LxR
    have x_less_R: all_nodes(R, λr{first(x) < first(r)}) 
      by definition is_BST in BST_LxR
    have BST_AVL_L: is_BST(AVL_insert(L, k, v))
      by apply IH_L[k, v] to BST_L
    have BST_AVL_R: is_BST(AVL_insert(R, k, v))
      by apply IH_R[k, v] to BST_R
    cases trichotomy[k][first(x)]
    case k_less_fx: k < first(x) {
      have not_k_eq_fx: not (k = first(x))  by apply less_not_equal to k_less_fx
      suffices is_BST(balance(AVL_insert(L, k, v), x, R))
          with definition AVL_insert and rewrite not_k_eq_fx | k_less_fx
      have BST_insLxR: is_BST(TreeNode(AVL_insert(L, k, v), x, R)) by
        _definition is_BST
        have k_l_x: (λl{first(l) < first(x)} : fn Pair<Nat,Nat>->bool)(pair(k,v))
            by _definition first k_less_fx
        have insL_less_x: all_nodes(AVL_insert(L, k, v), λl{first(l) < first(x)}) by 
            apply all_nodes_AVL_insert to L_less_x, k_l_x
        insL_less_x, x_less_R, BST_AVL_L, BST_R
      apply is_BST_balance to BST_insLxR
    }
    case k_eq_fx: k = first(x) {
      suffices is_BST(TreeNode(L, pair(first(x), v), R))
          with definition {AVL_insert} and rewrite k_eq_fx
      suffices all_nodes(L, λl{first(l) < first(x)}) 
           and all_nodes(R, λr{first(x) < first(r)}) 
           and is_BST(L) and is_BST(R)
          with definition {is_BST, first}
      L_less_x, x_less_R, BST_L, BST_R
    }
    case k_greater_fx: first(x) < k {
      have not_k_less_fx: not (k < first(x))   by apply less_implies_not_greater to k_greater_fx
      have not_k_eq_fx: not (k = first(x))
         by suppose k_eq_fx
            apply (apply less_not_equal to k_greater_fx) to symmetric k_eq_fx
      suffices is_BST(balance(L, x, AVL_insert(R, k, v)))
          with definition AVL_insert and rewrite not_k_eq_fx | not_k_less_fx
      have BST_LxinsR: is_BST(TreeNode(L, x, AVL_insert(R, k, v))) by
          _definition is_BST
          have x_l_k: (λr{first(x) < first(r)} : fn Pair<Nat,Nat>->bool)(pair(k,v))
            by _definition first k_greater_fx
          have x_less_insR: all_nodes(AVL_insert(R, k, v), λr{first(x) < first(r)})
            by apply all_nodes_AVL_insert to x_less_R, x_l_k
          L_less_x, x_less_insR, BST_L, BST_AVL_R
      apply is_BST_balance to BST_LxinsR
    }
  }
end
```

```{.deduce #AVL_search_insert_update}
theorem AVL_search_insert_udpate: all T:Tree<Pair<Nat,Nat>>. all k:Nat, v:Nat.
  if is_BST(T)
  then BST_search(AVL_insert(T, k, v)) = update(BST_search(T), k, just(v))
proof
  induction Tree<Pair<Nat,Nat>>
  case EmptyTree {
    arbitrary k:Nat, v:Nat
    suppose BST_T
    extensionality
    arbitrary i:Nat
    suffices BST_search(TreeNode(EmptyTree, pair(k, v), EmptyTree))(i) 
           = update(BST_search(EmptyTree), k, just(v))(i)
        with definition AVL_insert
    <<BST_search_insert_empty_tri>>
  }
  case TreeNode(L, x, R) suppose IH_L, IH_R {
    arbitrary k:Nat, v:Nat
    suppose BST_T
    have BST_L: is_BST(L) by definition is_BST in BST_T
    have BST_R: is_BST(R) by definition is_BST in BST_T
    extensionality
    arbitrary i:Nat
    suffices BST_search(AVL_insert(TreeNode(L, x, R), k, v))(i) 
           = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)  by .
    cases trichotomy[k][first(x)]
    case k_less_fx: k < first(x) {
      have not_k_eq_fx: not (k = first(x))  by apply less_not_equal to k_less_fx
      suffices BST_search(balance(AVL_insert(L, k, v), x, R))(i) 
             = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
          with definition {AVL_insert} and rewrite not_k_eq_fx | k_less_fx
      have BST_insLxR: is_BST(TreeNode(AVL_insert(L, k, v), x, R))
        by _definition is_BST
           have L_less_x: all_nodes(L, λl{first(l) < first(x)})
             by definition is_BST in BST_T
           have k_l_x: (λl{first(l) < first(x)} : fn Pair<Nat,Nat>->bool)(pair(k, v))
             by _definition first k_less_fx
           have insL_less_x: all_nodes(AVL_insert(L, k, v), λl{first(l) < first(x)}) 
             by apply all_nodes_AVL_insert[L, k, v, λl{first(l) < first(x)}] 
                to L_less_x, k_l_x
           have x_less_R: all_nodes(R, λr{first(x) < first(r)}) 
             by definition is_BST in BST_T
           have BST_insL: is_BST(AVL_insert(L, k, v)) 
             by apply is_BST_AVL_insert[L][k, v] to BST_L
           have BST_R: is_BST(R)  by definition is_BST in BST_T
           insL_less_x, x_less_R, BST_insL, BST_R
      suffices BST_search(TreeNode(AVL_insert(L, k, v), x, R))(i) 
             = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
          with rewrite symmetric (apply search_balance[AVL_insert(L, k, v), x, R] to BST_insLxR)
      cases trichotomy[i][first(x)]
      case i_less_fx: i < first(x) {
        // AVL_search_insert_node_k_less_fx_i_less_fx
        have not_i_eq_fx: not (i = first(x)) by apply less_not_equal to i_less_fx
        equations
              BST_search(TreeNode(AVL_insert(L, k, v), x, R))(i) 
            = BST_search(AVL_insert(L, k, v))(i)
                by definition{BST_search} and rewrite not_i_eq_fx | i_less_fx
        ... = update(BST_search(L), k, just(v))(i)
                by rewrite (apply IH_L[k,v] to BST_L)
        ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(i) by
                switch i = k {
                  case true suppose ik_true {
                    definition {BST_search,update} and rewrite ik_true
                  }
                  case false suppose ik_false {
                    definition {BST_search,update}
                    and rewrite ik_false | not_i_eq_fx | i_less_fx
                  }
                }
      }
      case i_eq_fx: i = first(x) {
        // AVL_search_insert_node_k_less_fx_i_eq_fx
        have not_fx_eq_k: not (first(x) = k)
          by suppose fx_eq_k
             conclude false by rewrite not_k_eq_fx in symmetric fx_eq_k 
        equations
              BST_search(TreeNode(AVL_insert(L, k, v), x, R))(i) 
            = just(second(x))
                by definition {BST_search} and rewrite i_eq_fx
        ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
                by definition {BST_search,update} and rewrite i_eq_fx | not_fx_eq_k
      }
      case fx_less_i: first(x) < i {
        // <<AVL_search_insert_node_k_less_fx_i_greater_fx>> =
        have not_i_eq_fx: not (i = first(x))
          by suppose i_eq_fx
             apply (apply less_not_equal to fx_less_i) to symmetric i_eq_fx
        have not_i_less_fx: not (i < first(x))
          by apply less_implies_not_greater to fx_less_i
        have not_i_eq_k: not (i = k)
          by suppose i_eq_k
             have fx_less_k: first(x) < k   by rewrite i_eq_k in fx_less_i
             have not_k_less_fx: not (k < first(x)) 
                 by apply less_implies_not_greater to fx_less_k
             conclude false by apply not_k_less_fx to rewrite k_less_fx
        equations
              BST_search(TreeNode(AVL_insert(L, k, v), x, R))(i) 
            = BST_search(R)(i)
                by definition BST_search and rewrite not_i_eq_fx | not_i_less_fx
        ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
                by definition {BST_search, update}
                   and rewrite not_i_eq_k | not_i_eq_fx | not_i_less_fx
      }
    }
    case k_eq_fx: k = first(x) {
      suffices BST_search(TreeNode(L, pair(k, v), R))(i) 
             = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
               by definition AVL_insert and rewrite k_eq_fx
      <<BST_search_insert_node_k_equal_fx_tri>>
    }
    case k_greater_fx: first(x) < k {
      have not_k_less_fx: not (k < first(x))   by apply less_implies_not_greater to k_greater_fx
      have not_k_eq_fx: not (k = first(x))
         by suppose k_eq_fx
            apply (apply less_not_equal to k_greater_fx) to symmetric k_eq_fx
      suffices BST_search(balance(L, x, AVL_insert(R, k, v)))(i) 
            = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
          with definition AVL_insert
          and rewrite not_k_eq_fx | not_k_less_fx
      have BST_LxinsR: is_BST(TreeNode(L, x, AVL_insert(R, k, v)))
         by _definition is_BST
            have L_less_x: all_nodes(L, λl{first(l) < first(x)}) 
              by definition is_BST in BST_T
            have x_less_R: all_nodes(R, λr{first(x) < first(r)}) 
              by definition is_BST in BST_T
           have x_l_k: (λr{first(x) < first(r)} : fn Pair<Nat,Nat>->bool)(pair(k, v))
             by _definition first k_greater_fx
            have x_less_insR: all_nodes(AVL_insert(R, k, v), λr{first(x) < first(r)}) 
              by apply all_nodes_AVL_insert to x_less_R, x_l_k
            have BST_insR: is_BST(AVL_insert(R, k, v))
              by apply is_BST_AVL_insert[R][k,v] to BST_R
            L_less_x, x_less_insR, BST_L, BST_insR
      suffices BST_search(TreeNode(L, x, AVL_insert(R, k, v)))(i) 
            = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
          with rewrite symmetric (apply search_balance[L, x, AVL_insert(R, k, v)] to BST_LxinsR)
      cases trichotomy[i][first(x)]
      case i_less_fx: i < first(x) {
        have not_i_eq_fx: not (i = first(x)) by apply less_not_equal to i_less_fx
        have not_i_eq_k: not (i = k)
          by suppose i_eq_k
             have k_less_fx: k < first(x)  by rewrite i_eq_k in i_less_fx
             conclude false by rewrite not_k_less_fx in k_less_fx
        equations
              BST_search(TreeNode(L, x, AVL_insert(R, k, v)))(i) 
            = BST_search(L)(i)
               by definition BST_search
                  and rewrite not_i_eq_fx | i_less_fx
        ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
               by definition {BST_search,update}
                  and rewrite not_i_eq_k | not_i_eq_fx | i_less_fx
      }
      case i_eq_fx: i = first(x) {
        have not_fx_eq_k: not (first(x) = k)
          by suppose fx_eq_k
             conclude false by rewrite not_k_eq_fx in symmetric fx_eq_k 
        have not_i_eq_k: not (i = k)
          by suppose i_eq_k 
             have k_eq_fx: k = first(x) by rewrite i_eq_k in i_eq_fx
             apply not_fx_eq_k to symmetric k_eq_fx
        equations
              BST_search(TreeNode(L, x, AVL_insert(R, k, v)))(i) 
            = just(second(x))
                by definition BST_search 
                   and rewrite i_eq_fx
        ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
                by definition {BST_search, update} 
                   and rewrite not_i_eq_k | i_eq_fx
      }
      case fx_less_i: first(x) < i {
        have not_i_eq_fx: not (i = first(x)) 
          by suppose i_eq_fx
             apply (apply less_not_equal to fx_less_i) to symmetric i_eq_fx
        have not_i_less_fx: not (i < first(x)) by apply less_implies_not_greater to fx_less_i
        equations
              BST_search(TreeNode(L, x, AVL_insert(R, k, v)))(i) 
            = BST_search(AVL_insert(R, k, v))(i)
                by definition BST_search
                   and rewrite not_i_eq_fx | not_i_less_fx
        ... = update(BST_search(R), k, just(v))(i)
                by rewrite (apply IH_R[k,v] to BST_R)
        ... = update(BST_search(TreeNode(L, x, R)), k, just(v))(i)
                by switch i = k for BST_search, update {
                     case true {
                       .
                     }
                     case false {
                       rewrite not_i_eq_fx | not_i_less_fx
                     }
                   }
      }
    }
  }
end
```

## AVL Insertion Maintains Balance


```{.deduce #is_AVL}
function is_AVL(Tree<Pair<Nat,Nat>>) -> bool {
  is_AVL(EmptyTree) = true
  is_AVL(TreeNode(L, x, R)) = 
      height(R) ≤ 1 + height(L)
      and height(L) ≤ 1 + height(R)
      and is_AVL(L) 
      and is_AVL(R)
}
```

```{.deduce #is_AVL_rotate_left}
theorem is_AVL_rotate_left:
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, 
      y:Pair<Nat,Nat>, C: Tree<Pair<Nat,Nat>>.
  if 1 + height(A) < height(TreeNode(B, y, C))
  and height(B) ≤ height(C)
  and is_AVL(A)
  and is_AVL(TreeNode(B, y, C))
  and height(TreeNode(B, y, C)) ≤ 2 + height(A)
  and height(A) ≤ 2 + height(TreeNode(B, y, C))
  then is_AVL(rotate_left(A, x, B, y, C))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, 
      y:Pair<Nat,Nat>, C: Tree<Pair<Nat,Nat>>
  suppose prem
  
  have tall_right: 1 + height(A) < height(TreeNode(B, y, C)) by prem
  have B_le_C: height(B) ≤ height(C) by prem

  suffices height(C) ≤ 1 + suc(max(height(A), height(B)))
    and suc(max(height(A), height(B))) ≤ 1 + height(C) 
    and height(B) ≤ 1 + height(A) 
    and height(A) ≤ 1 + height(B) 
    and is_AVL(A) and is_AVL(B) and is_AVL(C)
         with definition {rotate_left, is_AVL, is_AVL, height}

  have R_eq_two_A: height(TreeNode(B, y, C)) = 2 + height(A) by
      have R_le_two_A: height(TreeNode(B, y, C)) ≤ 2 + height(A) by prem
      have two_A_le_R: 2 + height(A) ≤ height(TreeNode(B, y, C)) by 
         _definition {operator+,operator+,operator+}
         rewrite (definition {operator<, operator+,operator+} in tall_right)
      apply less_equal_antisymmetric to R_le_two_A, two_A_le_R


  have max_B_C_eq_C: max(height(B), height(C)) = height(C)
    by apply max_equal_greater_right to 
       (conclude height(B) ≤ height(C) by prem)

  have R_eq_one_C: height(TreeNode(B, y, C)) = 1 + height(C) by
    _definition height
    _rewrite max_B_C_eq_C
    definition {operator+,operator+}

  have R_eq_one_C: height(TreeNode(B, y, C)) = 1 + height(C) by
    _definition height
    _rewrite max_B_C_eq_C
    definition {operator+,operator+}

  have C_eq_one_A: height(C) = 1 + height(A) by
    _definition {operator+,operator+}
    injective suc
    definition {operator+,operator+,operator+} in
    rewrite R_eq_one_C in R_eq_two_A

  have _1: height(C) ≤ 1 + suc(max(height(A), height(B))) by
    have step1: height(C) ≤ max(height(B), height(C))
       by max_greater_right[height(C)][height(B)]
    have step2: max(height(B), height(C)) ≤ suc(height(A)) by 
        have X: suc(max(height(B), height(C))) ≤ 2 + height(A)
           by definition height in prem
        definition {operator+, operator≤, operator+, operator+} in X
    have step3: suc(height(A)) ≤ suc(max(height(A), height(B))) by 
        have X: height(A) ≤ max(height(A), height(B))
           by max_greater_left[height(A)][height(B)]
        _definition operator≤ X
    have step4: suc(max(height(A), height(B))) 
                ≤ 1 + suc(max(height(A), height(B)))
       by _definition {operator+,operator+}
          less_equal_suc[suc(max(height(A), height(B)))]
    apply less_equal_trans to (apply less_equal_trans to step1, step2),
                              (apply less_equal_trans to step3, step4)

  have _2: suc(max(height(A), height(B))) ≤ 1 + height(C) by 
    suffices max(height(A), height(B)) ≤ height(C)
        with definition {operator+, operator+, operator≤}
    have A_le_C: height(A) ≤ height(C) by 
        _rewrite C_eq_one_A
        _definition {operator+, operator+}
        less_equal_suc[height(A)]
    apply max_less_equal to A_le_C, B_le_C

  have _3: height(B) ≤ 1 + height(A) by 
    _rewrite symmetric C_eq_one_A
    B_le_C

  have _4: height(A) ≤ 1 + height(B) by 
    have C_le_one_B: height(C) ≤ 1 + height(B)
      by definition is_AVL in prem
    have one_A_le_one_B: 1 + height(A) ≤ 1 + height(B)
      by rewrite C_eq_one_A in C_le_one_B
    have A_le_one_A: height(A) ≤ 1 + height(A) by 
      _definition {operator+, operator+}
      less_equal_suc[height(A)]
    apply less_equal_trans to (A_le_one_A, one_A_le_one_B)

  have _5: is_AVL(A) by prem

  have _6: is_AVL(B) by definition is_AVL in prem

  have _7: is_AVL(C) by definition is_AVL in prem

  (_1, _2, _3, _4, _5, _6, _7)
end
```

```{.deduce #right_taller}
function right_taller<E>(Tree<E>) -> bool {
  right_taller(EmptyTree) = true
  right_taller(TreeNode(L, x, R)) = height(L) ≤ height(R)
}
```

```{.deduce #left_taller}
function left_taller<E>(Tree<E>) -> bool {
  left_taller(EmptyTree) = true
  left_taller(TreeNode(L, x, R)) = height(R) ≤ height(L)
}
```

```{.deduce #is_AVL_rotate_left_on}
theorem is_AVL_rotate_left_on: 
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      ByC:Tree<Pair<Nat,Nat>>.
  if is_AVL(A)
  and 1 + height(A) < height(ByC)
  and is_AVL(ByC)
  and right_taller(ByC)
  and height(ByC) ≤ 2 + height(A)
  and height(A) ≤ 2 + height(ByC)
  then is_AVL(rotate_left_on(A, x, ByC))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, 
      ByC:Tree<Pair<Nat,Nat>>
  suppose prem
  switch ByC {
    case EmptyTree suppose ByC_empty {
      conclude false by
        definition {height,operator<, operator≤} in 
        rewrite ByC_empty in (conjunct 1 of prem)
    }
    case TreeNode(B, y, C) suppose ByC_node {
      suffices is_AVL(rotate_left(A, x, B, y, C))
          with definition rotate_left_on
          
      have prem_1: 1 + height(A) < height(TreeNode(B,y,C))
        by rewrite ByC_node in prem
        
      have prem_2: height(B) ≤ height(C)
        by definition right_taller in
           rewrite ByC_node in prem
        
      have prem_3: is_AVL(A) by prem
      
      have prem_4: is_AVL(TreeNode(B,y,C)) 
          by rewrite ByC_node in prem
      
      have prem_5: height(TreeNode(B,y,C)) ≤ 2 + height(A) 
          by rewrite ByC_node in prem
      
      have prem_6: height(A) ≤ 2 + height(TreeNode(B,y,C))
          by rewrite ByC_node in prem
      
      apply is_AVL_rotate_left[A,x,B,y,C]
      to prem_1, prem_2, prem_3, prem_4, prem_5, prem_6
    }
  }
end
```

```{.deduce #is_AVL_rotate_right}
theorem is_AVL_rotate_right:
  all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, 
      y:Pair<Nat,Nat>, C: Tree<Pair<Nat,Nat>>.
  if 1 + height(C) < height(TreeNode(A,x,B))
  and height(B) ≤ height(A)
  and is_AVL(C)
  and is_AVL(TreeNode(A,x,B))
  and height(C) ≤ 2 + height(TreeNode(A,x,B))
  and height(TreeNode(A,x,B)) ≤ 2 + height(C)
  then is_AVL(rotate_right(A, x, B, y, C))
proof
  arbitrary A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, 
      y:Pair<Nat,Nat>, C: Tree<Pair<Nat,Nat>>
  suppose prem
  suffices suc(max(height(B), height(C))) ≤ 1 + height(A) 
       and height(A) ≤ 1 + suc(max(height(B), height(C))) 
       and is_AVL(A) 
       and height(C) ≤ 1 + height(B) 
       and height(B) ≤ 1 + height(C) 
       and is_AVL(B) and is_AVL(C)
      with definition {rotate_right, is_AVL, is_AVL, height}

  have B_le_A: height(B) ≤ height(A)  by prem

  have AxB_eq_two_C: height(TreeNode(A,x,B)) = 2 + height(C) by
    have X: height(TreeNode(A,x,B)) ≤ 2 + height(C) by prem
    have Y: 2 + height(C) ≤ height(TreeNode(A,x,B)) by 
      _definition {operator+,operator+,operator+}
      definition {operator<, operator+,operator+} in 
      conjunct 0 of prem
    apply less_equal_antisymmetric to X, Y

  have max_A_B_eq_A: max(height(A), height(B)) = height(A)
    by apply max_equal_greater_left to (conclude height(B) ≤ height(A) by prem)

  have A_eq_one_C: height(A) = 1 + height(C) by
      _definition {operator+,operator+}
      injective suc
      definition {operator+,operator+,operator+} in
      rewrite max_A_B_eq_A in
      definition height in AxB_eq_two_C

  have _1: suc(max(height(B), height(C))) ≤ 1 + height(A) by 
      suffices max(height(B), height(C)) ≤ height(A)
          with definition {operator+,operator+,operator≤}
      have C_le_A: height(C) ≤ height(A) by 
        have sC_le_A: suc(height(C)) ≤ height(A)
          by rewrite max_A_B_eq_A in
             definition {operator<,operator+,operator+, height,operator≤} in 
             conjunct 0 of prem
        have C_le_sC: height(C) ≤ suc(height(C))
             by less_equal_suc[height(C)]
        apply less_equal_trans to (C_le_sC, sC_le_A)
      apply max_less_equal to B_le_A, C_le_A
      
  have _2: height(A) ≤ 1 + suc(max(height(B), height(C))) by 
      suffices 1 + height(C) ≤ 1 + suc(max(height(B), height(C)))
          with rewrite A_eq_one_C
      suffices height(C) ≤ suc(max(height(B), height(C)))
          with definition {operator+,operator+,operator+, operator≤}
      have sC_le_smBC: suc(height(C)) ≤ suc(max(height(B), height(C))) by
          _definition operator≤
          max_greater_right[height(C)][height(B)]
      have C_le_sC: height(C) ≤ suc(height(C))
          by less_equal_suc[height(C)]
      apply less_equal_trans to (C_le_sC, sC_le_smBC)
  
  have _3: is_AVL(A) by definition is_AVL in prem
  
  have _4: height(C) ≤ 1 + height(B) by 
    have X: 1 + height(C) ≤ 2 + height(B) by
        suffices height(A) ≤ 2 + height(B)
            with rewrite symmetric A_eq_one_C
        have A_le_one_B: height(A) ≤ 1 + height(B)
          by definition is_AVL in conjunct 3 of prem
        have one_B_le_two_B: 1 + height(B) ≤ 2 + height(B) by
          _definition {operator+,operator+,operator+}
          less_equal_suc[suc(height(B))]
        apply less_equal_trans to (A_le_one_B, one_B_le_two_B)
    _definition {operator+,operator+}
    definition {operator+,operator+, operator+, operator≤} in X
  
  have _5: height(B) ≤ 1 + height(C) by 
    suffices height(B) ≤ height(A)  with rewrite symmetric A_eq_one_C
    B_le_A
  
  have _6: is_AVL(B) by definition is_AVL in prem
  
  have _7: is_AVL(C) by prem
  
  _1, _2, _3, _4, _5, _6, _7
end
```

```{.deduce #is_AVL_rotate_right_on}
theorem is_AVL_rotate_right_on:
  all AxB:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, C:Tree<Pair<Nat,Nat>>.
  if is_AVL(C)
  and is_AVL(AxB)
  and left_taller(AxB)
  and 1 + height(C) < height(AxB) 
  and height(C) ≤ 2 + height(AxB)
  and height(AxB) ≤ 2 + height(C)
  then is_AVL(rotate_right_on(AxB, y, C))
proof
  arbitrary AxB:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, C:Tree<Pair<Nat,Nat>>
  suppose prem
  switch AxB {
    case EmptyTree suppose AxB_empty {
      conclude false
        by definition {height,operator+,operator<,operator≤} in 
           rewrite AxB_empty in
           conjunct 3 of prem
    }
    case TreeNode(A, x, B) suppose AxB_node {
      suffices is_AVL(rotate_right(A, x, B, y, C))
          with definition rotate_right_on
      have p1: 1 + height(C) < height(TreeNode(A, x, B)) by rewrite AxB_node in prem
      have p2: height(B) ≤ height(A) 
          by definition left_taller in rewrite AxB_node in prem
      have p3: is_AVL(C) by prem
      have p4: is_AVL(TreeNode(A, x, B)) by rewrite AxB_node in prem
      have p5: height(C) ≤ 2 + height(TreeNode(A, x, B)) by rewrite AxB_node in prem
      have p6: height(TreeNode(A, x, B)) ≤ 2 + height(C) by rewrite AxB_node in prem
      apply is_AVL_rotate_right[A,x,B,y,C]
      to p1, p2, p3, p4, p5, p6
    }
  }
end
```

```{.deduce #is_AVL_balance_tall_right_tall_RR}
    have RL_le_RR: height(RL) ≤ height(RR) by rewrite tall_RR
    suffices is_AVL(rotate_left(L, x, RL, z, RR))
        with definition balance
         and rewrite (rewrite R_node in tall_right) | tall_RR
    apply is_AVL_rotate_left[L,x,RL,z,RR] to 
        (conclude 1 + height(L) < height(TreeNode(RL,z,RR))
          by rewrite (rewrite R_node in tall_right)),
        RL_le_RR, AVL_L, (rewrite R_node in AVL_R), 
        (rewrite R_node in prem)
```

```{.deduce #is_AVL_balance_tall_right_tall_RL}
    suffices is_AVL(rotate_left_on(L, x, rotate_right_on(RL, z, RR)))
        with definition balance
         and rewrite (rewrite R_node in tall_right) | tall_RL

    have RL_eq_one_RR: height(RL) = 1 + height(RR) by
      have s1: 1 + height(RR) ≤ height(RL) by
         have X: not (height(RL) ≤ height(RR))
           by rewrite tall_RL
         have Y: height(RR) < height(RL)
           by apply not_less_equal_greater to X
         suffices suc(height(RR)) ≤ height(RL)
             with definition {operator+,operator+}
         definition operator< in Y
      have s2: height(RL) ≤ 1 + height(RR) by
         definition is_AVL in rewrite R_node in AVL_R
      symmetric (apply less_equal_antisymmetric  to s1, s2)

    have R_eq_one_RL: height(R) = 1 + height(RL) by
      suffices suc(max(1 + height(RR), height(RR))) = 1 + (1 + height(RR))
        with definition {height}
        and rewrite R_node | RL_eq_one_RR
      definition {operator+, operator+,operator+}
        and rewrite max_suc[height(RR)] | max_same[height(RR)]

    have RL_eq_one_L: height(RL) = 1 + height(L) by
      have X: 1 + height(RL) = 2 + height(L)
        by transitive (symmetric R_eq_one_RL) R_eq_two_L
      injective suc
      suffices suc(height(RL)) = suc(suc(height(L)))
        with definition {operator+,operator+}
      definition {operator+,operator+,operator+} in X

    switch RL {
      case EmptyTree suppose RL_mt {
        conclude false
          by definition {height,operator≤} in 
             rewrite RL_mt in tall_RL
      }
      case TreeNode(A, y, B) suppose RL_node {
        suffices is_AVL(TreeNode(TreeNode(L, x, A), y, 
                                 TreeNode(B, z, RR)))
          with definition {rotate_right_on, rotate_right, 
              rotate_left_on, rotate_left}
          and rewrite RL_node

        suffices suc(max(height(B), height(RR))) 
                 ≤ 1 + suc(max(height(L), height(A))) 
          and suc(max(height(L), height(A))) 
              ≤ 1 + suc(max(height(B), height(RR))) 
          and height(A) ≤ 1 + height(L) 
          and height(L) ≤ 1 + height(A) 
          and is_AVL(L) 
          and is_AVL(A) 
          and height(RR) ≤ 1 + height(B) 
          and height(B) ≤ 1 + height(RR) 
          and is_AVL(B) 
          and is_AVL(RR)
          with definition {is_AVL,is_AVL,is_AVL, height}

        have RL_eq_one_max_A_B: 
          height(RL) = 1 + max(height(A), height(B)) by
              definition {height, operator+,operator+}
              and rewrite RL_node

        have RR_eq_max_A_B: height(RR) = max(height(A), height(B)) by
          have X: 1 + height(RR) = 1 + max(height(A), height(B)) by
            transitive (symmetric RL_eq_one_RR) RL_eq_one_max_A_B
          injective suc
          definition {operator+,operator+} in X

        have L_eq_max_A_B: height(L) = max(height(A), height(B)) by
          injective suc
          have X: 1 + height(L) = 1 + max(height(A), height(B)) by
              transitive (symmetric RL_eq_one_L) RL_eq_one_max_A_B
          definition {operator+,operator+} in X

        have AVL_x1: height(A) ≤ 1 + height(L) by {
          suffices height(A) ≤ 1 + max(height(A), height(B))
            with rewrite L_eq_max_A_B
          have _1: height(A) ≤ max(height(A), height(B))
            by max_greater_left[height(A)][height(B)]
          have _2: max(height(A), height(B)) ≤ 1 + max(height(A), height(B))
            by definition {operator+,operator+}
            and rewrite less_equal_suc[max(height(A), height(B))]
          apply less_equal_trans to _1, _2
        }

        have AVL_RL: is_AVL(RL) by
          definition is_AVL in rewrite R_node in AVL_R

        have AVL_x2: height(L) ≤ 1 + height(A) by {
          suffices max(height(A), height(B)) ≤ 1 + height(A)
              with rewrite L_eq_max_A_B
          have B_le_one_A: height(B) ≤ 1 + height(A) by 
              definition is_AVL in 
              rewrite RL_node in AVL_RL
          have A_le_one_A: height(A) ≤ 1 + height(A)
              by definition {operator+, operator+} 
                 and rewrite less_equal_suc[height(A)]
          apply max_less_equal to A_le_one_A, B_le_one_A
        }

        have AVL_y1: suc(max(height(B), height(RR))) 
                 ≤ 1 + suc(max(height(L), height(A))) by {
          suffices max(height(B), height(RR)) ≤ suc(max(height(L), height(A)))
             with definition {operator+,operator+,operator≤}
          have B_le: height(B) ≤ suc(max(height(L), height(A))) by 
             suffices height(B) ≤ suc(max(max(height(A), height(B)), height(A)))
                with rewrite L_eq_max_A_B
             have B_le_max_AB: height(B) ≤ max(height(A), height(B)) 
                 by max_greater_right[height(B)][height(A)]
             have max_AB_le: max(height(A), height(B))
                           ≤ max(max(height(A), height(B)), height(A))
                 by max_greater_left[max(height(A), height(B))][height(A)]
             have max_AB_suc: max(max(height(A), height(B)), height(A)) 
                   ≤ suc(max(max(height(A), height(B)), height(A)))
                    by less_equal_suc[max(max(height(A), height(B)), height(A))]
             apply less_equal_trans to (B_le_max_AB, 
                apply less_equal_trans to (max_AB_le, max_AB_suc))
          have RR_le: height(RR) ≤ suc(max(height(L), height(A))) by 
             suffices max(height(A), height(B))
                    ≤ suc(max(max(height(A), height(B)), height(A)))
                 with rewrite RR_eq_max_A_B | L_eq_max_A_B
             suffices max(height(B), height(A)) ≤ suc(max(height(B), height(A)))
                 with rewrite max_symmetric[height(A)][height(B)]
                      | max_assoc[height(B)][height(A), height(A)]
                      | max_same[height(A)]
             less_equal_suc
          apply max_less_equal to B_le, RR_le
        }

        have AVL_y2: suc(max(height(L), height(A))) 
              ≤ 1 + suc(max(height(B), height(RR))) by {
          suffices max(height(B), height(A)) ≤ suc(max(height(B), height(A)))
              with definition {operator+, operator+, operator≤}
              and rewrite L_eq_max_A_B | RR_eq_max_A_B
                  | max_symmetric[height(A)][height(B)]
                  | max_assoc[height(B)][height(A),height(A)]
                  | max_same[height(A)]
                  | symmetric max_assoc[height(B)][height(B),height(A)]
                  | max_same[height(B)]
          less_equal_suc
        }
        
        have AVL_z1: height(RR) ≤ 1 + height(B) by {
           suffices max(height(A), height(B)) ≤ 1 + height(B)
              with rewrite RR_eq_max_A_B
           have A_le_one_B: height(A) ≤ 1 + height(B) by
              definition is_AVL in rewrite RL_node in AVL_RL
           have B_le_one_B: height(B) ≤ 1 + height(B) by less_equal_add_left
           apply max_less_equal to A_le_one_B, B_le_one_B
        }
        
        have AVL_z2: height(B) ≤ 1 + height(RR) by {
           suffices height(B) ≤ 1 + max(height(A), height(B))
              with rewrite RR_eq_max_A_B
           have B_le_max_AB: height(B) ≤ max(height(A), height(B))
                by max_greater_right
           have max_AB_le: max(height(A), height(B)) 
                           ≤ 1 + max(height(A), height(B))
                by less_equal_add_left
           apply less_equal_trans to B_le_max_AB, max_AB_le
        }
        
        have AVL_A: is_AVL(A)
            by definition is_AVL in rewrite RL_node in AVL_RL
        have AVL_B: is_AVL(B)
            by definition is_AVL in rewrite RL_node in AVL_RL

        AVL_x1, AVL_x2, AVL_y1, AVL_y2, AVL_z1, AVL_z2, 
          AVL_L, AVL_A, AVL_B, AVL_RR
      }
    }
```

```{.deduce #is_AVL_balance_tall_left_tall_LR}
    suffices
      is_AVL(rotate_right_on(rotate_left_on(LL, z, LR), x, R))
       with definition balance
       and rewrite (rewrite L_node in not_tall_right) 
           | (rewrite L_node in tall_left) | tall_LR

    have LR_eq_one_LL: height(LR) = 1 + height(LL) by
      have s1: 1 + height(LL) ≤ height(LR) by
         have X: not (height(LR) ≤ height(LL))
           by rewrite tall_LR
         have Y: height(LL) < height(LR)
           by apply not_less_equal_greater to X
         suffices suc(height(LL)) ≤ height(LR)
             with definition {operator+,operator+}
         definition operator< in Y
      have s2: height(LR) ≤ 1 + height(LL) by
         definition is_AVL in rewrite L_node in AVL_L
      symmetric (apply less_equal_antisymmetric  to s1, s2)

    have L_eq_one_LR: height(L) = 1 + height(LR) by
      suffices suc(max(height(LL), 1 + height(LL)))
              = 1 + (1 + height(LL))
        with definition {height}
        and rewrite L_node | LR_eq_one_LL
      definition {operator+, operator+,operator+}
      and rewrite max_symmetric[height(LL)][suc(height(LL))]
            | max_suc[height(LL)] | max_same[height(LL)]

    have LR_eq_one_R: height(LR) = 1 + height(R) by
      have X: 1 + height(LR) = 2 + height(R)
        by transitive (symmetric L_eq_one_LR) L_eq_two_R
      injective suc
      suffices suc(height(LR)) = suc(suc(height(R)))
        with definition {operator+,operator+}
      definition {operator+,operator+,operator+} in X

    switch LR {
      case EmptyTree suppose LR_mt {
        conclude false
          by definition {height, operator≤} in
             rewrite LR_mt in tall_LR
      }
      case TreeNode(A, y, B) suppose LR_node {
        suffices is_AVL(TreeNode(TreeNode(LL, z, A), y,
                                 TreeNode(B, x, R)))
           with definition {rotate_left_on, rotate_left,
                  rotate_right_on, rotate_right}
        suffices 
            suc(max(height(B), height(R))) 
              ≤ 1 + suc(max(height(LL), height(A))) 
            and suc(max(height(LL), height(A))) 
                ≤ 1 + suc(max(height(B), height(R))) 
            and height(A) ≤ 1 + height(LL) 
            and height(LL) ≤ 1 + height(A) 
            and is_AVL(LL) 
            and is_AVL(A) 
            and height(R) ≤ 1 + height(B) 
            and height(B) ≤ 1 + height(R) 
            and is_AVL(B) 
            and is_AVL(R)
            with definition {is_AVL, is_AVL, is_AVL, height}

        have LR_eq_one_max_A_B: 
          height(LR) = 1 + max(height(A), height(B)) by
              definition {height, operator+,operator+}
              and rewrite LR_node

        have LL_eq_max_A_B: 
            height(LL) = max(height(A), height(B)) by
          have X: 1 + height(LL) = 1 + max(height(A), height(B)) 
            by transitive (symmetric LR_eq_one_LL) 
                          LR_eq_one_max_A_B
          injective suc
          definition {operator+,operator+} in X

        have R_eq_max_A_B: 
            height(R) = max(height(A), height(B)) by
          injective suc
          have X: 1 + height(R) = 1 + max(height(A), height(B)) by
              transitive (symmetric LR_eq_one_R) LR_eq_one_max_A_B
          definition {operator+,operator+} in X

        have AVL_x1: height(B) ≤ 1 + height(R) by {
          suffices height(B) ≤ 1 + max(height(A), height(B))
            with rewrite R_eq_max_A_B
          have _1: height(B) ≤ max(height(A), height(B))
            by max_greater_right[height(B)][height(A)]
          have _2: max(height(A), height(B)) ≤ 1 + max(height(A), height(B))
            by definition {operator+,operator+}
            and rewrite less_equal_suc[max(height(A), height(B))]
          apply less_equal_trans to _1, _2
        }

        have AVL_LR: is_AVL(LR) by
          definition is_AVL in rewrite L_node in AVL_L

        have AVL_x2: height(R) ≤ 1 + height(B) by {
          suffices max(height(A), height(B)) ≤ 1 + height(B)
              with rewrite R_eq_max_A_B
          have A_le_one_B: height(A) ≤ 1 + height(B) by 
              definition is_AVL in 
              rewrite LR_node in AVL_LR
          have B_le_one_B: height(B) ≤ 1 + height(B)
              by definition {operator+, operator+} 
              and rewrite less_equal_suc[height(B)]
          apply max_less_equal to A_le_one_B, B_le_one_B
        }
        
        have AVL_y1: suc(max(height(B), height(R))) 
                     ≤ 1 + suc(max(height(LL), height(A))) by {
          suffices suc(max(height(B), max(height(A), height(B)))) 
                 ≤ 1 + suc(max(max(height(A), height(B)), height(A)))
              with rewrite R_eq_max_A_B | LL_eq_max_A_B
          suffices max(height(B), height(A)) ≤ suc(max(height(B), height(A)))
              with definition {operator+, operator+, operator≤}
              and rewrite max_symmetric[height(A)][height(B)]
                | symmetric max_assoc[height(B)][height(B), height(A)]
                | max_same[height(B)]
                | max_assoc[height(B)][height(A), height(A)]
                | max_same[height(A)]
          less_equal_suc
        }
        have AVL_y2: suc(max(height(LL), height(A))) 
                     ≤ 1 + suc(max(height(B), height(R))) by {
          suffices max(height(LL), height(A)) ≤ suc(max(height(B), height(R)))
             with definition {operator+,operator+,operator≤}
          have LL_le: height(LL) ≤ suc(max(height(B), height(R))) by 
            suffices max(height(A), height(B))
                   ≤ suc(max(height(B), max(height(A), height(B))))
                with rewrite R_eq_max_A_B | LL_eq_max_A_B
            suffices max(height(B), height(A)) ≤ suc(max(height(B), height(A)))
                with rewrite max_symmetric[height(A)][height(B)]
                     | symmetric max_assoc[height(B)][height(B), height(A)]
                     | max_same[height(B)]
            less_equal_suc
          have A_le: height(A) ≤ suc(max(height(B), height(R))) by {
            suffices height(A) ≤ suc(max(height(B), max(height(A), height(B))))
                with rewrite R_eq_max_A_B
            suffices height(A) ≤ suc(max(height(B), height(A)))
                with rewrite max_symmetric[height(A)][height(B)]
                     | symmetric max_assoc[height(B)][height(B), height(A)]
                     | max_same[height(B)]
            have A_le_suc_A: height(A) ≤ suc(height(A)) by less_equal_suc
            have suc_A_le_suc_max: 
                suc(height(A)) ≤ suc(max(height(B), height(A))) by
              suffices height(A) ≤ max(height(B), height(A))
                 with definition operator≤
              max_greater_right
            apply less_equal_trans to A_le_suc_A, suc_A_le_suc_max
          }
          apply max_less_equal to LL_le, A_le
        }
        
        have AVL_z1: height(A) ≤ 1 + height(LL) by {
          suffices height(A) ≤ suc(max(height(A), height(B)))
            with definition {operator+,operator+}
            and rewrite LL_eq_max_A_B
          have A_le_sucA: height(A) ≤ suc(height(A)) by less_equal_suc
          have sucA_le_suc_max: suc(height(A)) ≤ suc(max(height(A), height(B)))
            by suffices height(A) ≤ max(height(A), height(B))
                  with definition operator≤
               max_greater_left
          apply less_equal_trans to A_le_sucA, sucA_le_suc_max
        }
        
        have AVL_z2: height(LL) ≤ 1 + height(A) by {
          suffices max(height(A), height(B)) ≤ 1 + height(A)
            with rewrite LL_eq_max_A_B
          have A_le_one_A: height(A) ≤ 1 + height(A) by 
            _definition {operator+, operator+}
            less_equal_suc
          have B_le_one_A: height(B) ≤ 1 + height(A) by 
            definition is_AVL in rewrite LR_node in AVL_LR
          apply max_less_equal to A_le_one_A, B_le_one_A
        }
        
        have AVL_A: is_AVL(A)
            by definition is_AVL in rewrite LR_node in AVL_LR
        have AVL_B: is_AVL(B)
            by definition is_AVL in rewrite LR_node in AVL_LR
        
        AVL_x1, AVL_x2, AVL_y1, AVL_y2, AVL_z1, AVL_z2,
          AVL_LL, AVL_A, AVL_B, AVL_R
      }
    }
```


```{.deduce #is_AVL_balance_tall_left_tall_LL}
    have LR_l_LL: height(LR) ≤ height(LL)
        by rewrite tall_LL
    suffices is_AVL(rotate_right(LL, z, LR, x, R))
        with definition balance
        and rewrite (rewrite L_node in not_tall_right) 
                  | (rewrite L_node in tall_left) | tall_LL
    apply is_AVL_rotate_right[LL,z,LR,x,R]
    to (rewrite L_node in one_R_l_L), LR_l_LL, AVL_R,
       (rewrite L_node in AVL_L), rewrite L_node in prem
```

```{.deduce #is_AVL_balance_already_balanced}
    suffices is_AVL(TreeNode(L, x, R))
        with definition balance
        and rewrite not_tall_right | not_tall_left
    _definition is_AVL
    have R_le_one_L: height(R) ≤ 1 + height(L) by
      have X: not (1 + height(L) < height(R)) by rewrite not_tall_right
      apply not_less_less_equal to X
    have L_le_one_R: height(L) ≤ 1 + height(R) by
      have X: not (1 + height(R) < height(L)) by rewrite not_tall_left
      apply not_less_less_equal to X
    R_le_one_L, L_le_one_R, AVL_L, AVL_R
```

```{.deduce #is_AVL_balance}
theorem is_AVL_balance: all L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>.
  if is_AVL(L) and is_AVL(R)
  and height(R) ≤ 2 + height(L)
  and height(L) ≤ 2 + height(R)
  then is_AVL(balance(L, x, R))
proof
  arbitrary L:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, R:Tree<Pair<Nat,Nat>>
  suppose prem
  have AVL_L: is_AVL(L) by prem
  have AVL_R: is_AVL(R) by prem
  
  switch 1 + height(L) < height(R) {
    case true suppose tall_right {
    
      have R_eq_two_L: height(R) = 2 + height(L) by
          have R_le_two_L: height(R) ≤ 2 + height(L) by prem
          have two_L_le_R: 2 + height(L) ≤ height(R) by 
             _definition {operator+,operator+,operator+}
             rewrite (definition {operator<, operator+,operator+} in tall_right)
          apply less_equal_antisymmetric to R_le_two_L, two_L_le_R
    
      switch R {
        case EmptyTree suppose R_mt {
          conclude false
            by definition {height, operator<, operator≤} in
               rewrite R_mt in tall_right
        }
        case TreeNode(RL, z, RR) suppose R_node {
          have AVL_RR: is_AVL(RR)
              by definition is_AVL in rewrite R_node in AVL_R
          switch height(RL) ≤ height(RR) {
            case true suppose tall_RR {
              <<is_AVL_balance_tall_right_tall_RR>>
            }
            case false suppose tall_RL {
              <<is_AVL_balance_tall_right_tall_RL>>
            }
          }
        }
      }
    }
    case false suppose not_tall_right {
      switch 1 + height(R) < height(L) {
        case true suppose tall_left {
          have one_R_l_L: 1 + height(R) < height(L)  by rewrite tall_left
          
          have L_eq_two_R: height(L) = 2 + height(R) by
            have L_le_two_R: height(L) ≤ 2 + height(R) by prem
            have two_R_le_L: 2 + height(R) ≤ height(L) by 
               _definition {operator+,operator+,operator+}
               rewrite (definition {operator<, operator+,operator+} 
                        in one_R_l_L)
            apply less_equal_antisymmetric to L_le_two_R, two_R_le_L
          
          switch L {
            case EmptyTree suppose L_mt {
              conclude false
                by definition {operator<, operator+, operator+, 
                               operator≤, height} in
                   rewrite L_mt in tall_left
            }
            case TreeNode(LL, z, LR) suppose L_node {
            
              have AVL_LL: is_AVL(LL)
                  by definition is_AVL in rewrite L_node in AVL_L
            
              switch height(LR) ≤ height(LL) {
                case true suppose tall_LL {
                  <<is_AVL_balance_tall_left_tall_LL>>
                }
                case false suppose tall_LR {
                  <<is_AVL_balance_tall_left_tall_LR>>
                }
              }
            }
          }
        }
        case false suppose not_tall_left {
          <<is_AVL_balance_already_balanced>>
        }
      }
    }
  }
end
```

```{.deduce #height_AVL_insert}
theorem height_AVL_insert: all T:Tree<Pair<Nat,Nat>>. all k:Nat, v:Nat.
  height(AVL_insert(T, k, v)) ≤ suc(height(T))
  and
  height(T) ≤ height(AVL_insert(T, k, v))
proof
  sorry
end
```

```{.deduce #is_AVL_insert}
theorem is_AVL_insert: all T:Tree<Pair<Nat,Nat>>. all k:Nat, v:Nat.
  if is_AVL(T)
  then is_AVL(AVL_insert(T, k, v))
proof
  induction Tree<Pair<Nat,Nat>>
  case EmptyTree {
    arbitrary k:Nat, v:Nat
    suppose AVL_mt
    definition {AVL_insert, is_AVL, height, operator+, operator≤, is_AVL}
  }
  case TreeNode(L, x, R) suppose IH_L, IH_R {
    arbitrary k:Nat, v:Nat
    suppose AVL_LxR
    have AVL_L: is_AVL(L) by definition is_AVL in AVL_LxR
    have AVL_R: is_AVL(R) by definition is_AVL in AVL_LxR
    cases trichotomy[k][first(x)]
    case k_less_x: k < first(x) {
      have not_k_eq_x: not (k = first(x))  by apply less_not_equal to k_less_x
      suffices is_AVL(balance(AVL_insert(L, k, v), x, R))
          with definition AVL_insert and rewrite not_k_eq_x | k_less_x
      have AVL_insL: is_AVL(AVL_insert(L, k, v))
        by apply IH_L[k,v] to AVL_L
      have R_le_two_insL: height(R) ≤ 2 + height(AVL_insert(L,k,v)) by 
        have L_le_insL: height(L) ≤ height(AVL_insert(L,k,v)) by
           height_AVL_insert[L][k,v]
        have R_le_one_L: height(R) ≤ 1 + height(L) by
           definition is_AVL in AVL_LxR 
        have one_L_two_L: 1 + height(L) ≤ 2 + height(L) by
           suffices height(L) ≤ suc(height(L))
               with definition {operator+, operator+, operator+, operator≤}
           less_equal_suc
        have two_L_le_2_insL: 2 + height(L) ≤ 2 + height(AVL_insert(L,k,v)) by 
           suffices height(L) ≤ height(AVL_insert(L, k, v))
               with definition {operator+, operator+, operator+, 
                      operator≤,operator≤}
           L_le_insL
        apply less_equal_trans to R_le_one_L, 
            (apply less_equal_trans to one_L_two_L, two_L_le_2_insL)
        
      have insL_le_two_R: height(AVL_insert(L,k,v)) ≤ 2 + height(R) by 
        have insL_le_one_L: height(AVL_insert(L,k,v)) ≤ suc(height(L))
            by height_AVL_insert[L][k,v]
        have one_L_le_2_R: suc(height(L)) ≤ 2 + height(R) by
            suffices height(L) ≤ suc(height(R))
              with definition {operator+,operator+,operator+, operator≤}
            definition {is_AVL,operator+,operator+} in AVL_LxR
        apply less_equal_trans to insL_le_one_L, one_L_le_2_R
      apply is_AVL_balance[AVL_insert(L,k,v), x, R] 
      to AVL_insL, AVL_R, R_le_two_insL, insL_le_two_R
    }
    case k_eq_x: k = first(x) {
      suffices is_AVL(TreeNode(L, pair(first(x), v), R))
          with definition AVL_insert and rewrite k_eq_x
      suffices height(R) ≤ 1 + height(L) and height(L) ≤ 1 + height(R) 
           and is_AVL(L) and is_AVL(R)   with definition is_AVL
      definition is_AVL in AVL_LxR
    }
    case k_greater_x: first(x) < k {
      have not_k_less_x: not (k < first(x))   
          by apply less_implies_not_greater to k_greater_x
      have not_k_eq_x: not (k = first(x))
         by suppose k_eq_x
            apply (apply less_not_equal to k_greater_x) to symmetric k_eq_x
      suffices is_AVL(balance(L, x, AVL_insert(R, k, v)))
          with definition AVL_insert and rewrite not_k_eq_x | not_k_less_x
      have AVL_insR: is_AVL(AVL_insert(R,k,v))
        by apply IH_R[k,v] to AVL_R
      have insR_le_two_L: height(AVL_insert(R,k,v)) ≤ 2 + height(L) by {
        have insR_le_sucR: height(AVL_insert(R,k,v)) ≤ suc(height(R))
            by height_AVL_insert[R][k,v]
        have sucR_le_two_L: suc(height(R)) ≤ 2 + height(L) by
            suffices height(R) ≤ suc(height(L))
              with definition {operator+, operator+, operator+, operator≤}
            have R_le_one_L: height(R) ≤ 1 + height(L)
                by definition is_AVL in AVL_LxR
            definition {operator+,operator+} in R_le_one_L
        apply less_equal_trans to insR_le_sucR, sucR_le_two_L
      }
      have L_le_two_insR: height(L) ≤ 2 + height(AVL_insert(R,k,v)) by {
        have two_R_le_two_insR: 2 + height(R) ≤ 2 + height(AVL_insert(R,k,v))
            by suffices height(R) ≤ height(AVL_insert(R, k, v))
                  with definition {operator+, operator+, operator+, 
                           operator≤, operator≤}
               height_AVL_insert[R][k,v]
        have L_le_one_R: height(L) ≤ 1 + height(R)
            by definition is_AVL in AVL_LxR
        have one_R_le_two_R: 1 + height(R) ≤ 2 + height(R) by
            suffices height(R) ≤ suc(height(R))
               with definition {operator+, operator+, operator+, operator≤}
            less_equal_suc
        apply less_equal_trans to L_le_one_R,
           (apply less_equal_trans to one_R_le_two_R, two_R_le_two_insR)
      }
      apply is_AVL_balance[L, x, AVL_insert(R,k,v)] 
      to AVL_L, AVL_insR, insR_le_two_L, L_le_two_insR
    }
  }
end
```


<!--
```{.deduce file=BalancedBST.pf} 

import Maps
import BinaryTree
import BinarySearchTree

<<rotate_right>>
<<rotate_left>>
<<rotate_right_on>>
<<rotate_left_on>>
<<balance>>
<<AVL_insert>>

<<search_rotate>>
<<search_rotate_right>>
<<search_rotate_left>>
<<search_rotate_right_on>>
<<search_rotate_left_on>>

<<search_node>>
<<search_compositional>>
<<rotate_right_on_height>>
<<rotate_left_on_height>>
<<all_nodes_rotate_right_on>>
<<all_nodes_rotate_left_on>>
<<all_nodes_implies>>
<<is_BST_rotate_left>>
<<is_BST_rotate_right>>
<<is_BST_rotate_right_on>>
<<is_BST_rotate_left_on>>
<<search_balance>>
<<is_BST_balance>>
<<all_nodes_balance>>
<<all_nodes_AVL_insert>>
<<is_BST_AVL_insert>>
<<AVL_search_insert_update>>

<<is_AVL>>
<<right_taller>>
<<left_taller>>
<<height_AVL_insert>>
<<is_AVL_rotate_left>>
<<is_AVL_rotate_left_on>>
<<is_AVL_rotate_right>>
<<is_AVL_rotate_right_on>>
<<is_AVL_balance>>
<<is_AVL_insert>>

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
