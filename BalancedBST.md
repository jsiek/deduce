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
theorem all_nodes_rotate_right_on: all A:Tree<Pair<Nat,Nat>>, x:Pair<Nat,Nat>, B:Tree<Pair<Nat,Nat>>, P:fn Pair<Nat,Nat>->bool.
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

```{.deduce #is_BST_rotate_right_on}
theorem is_BST_rotate_right_on: all AxB:Tree<Pair<Nat,Nat>>, y:Pair<Nat,Nat>, C:Tree<Pair<Nat,Nat>>.
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
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      have x_less_B: all_nodes(B, λr{first(x) < first(r)}) 
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      have fx_less_fy: first(x) < first(y) 
        by definition {is_BST, is_BST, all_nodes} in rewrite AxB_node in prem
      have BST_A: is_BST(A) 
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      have B_less_y: all_nodes(B, λl{first(l) < first(y)}) 
        by definition {is_BST, is_BST, all_nodes} in rewrite AxB_node in prem
      have y_less_C: all_nodes(C, λr{first(y) < first(r)}) 
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
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
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      have BST_C: is_BST(C)
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      (A_less_x, x_less_B, fx_less_fy, x_less_C, BST_A, B_less_y, y_less_C, BST_B, BST_C)
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
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      have A_less_x: all_nodes(A, λl{first(l) < first(x)}) 
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
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
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      have y_less_C: all_nodes(C, λr{first(y) < first(r)}) 
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      have x_less_B: all_nodes(B, λr{first(x) < first(r)}) 
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      have BST_A: is_BST(A)
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      have BST_B: is_BST(B)
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      have BST_C: is_BST(C)
        by definition {is_BST, is_BST, all_nodes} in rewrite ByC_node in prem
      A_less_y, x_less_y, B_less_y, y_less_C, A_less_x, x_less_B, BST_A, BST_B, BST_C
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
    cases trichotomy[k][first(x)]
    case k_less_fx: k < first(x) {
      have not_k_eq_fx: not (k = first(x))  by apply less_not_equal to k_less_fx
      _definition AVL_insert
      _rewrite not_k_eq_fx | k_less_fx
      ?
    }
    case k_eq_fx: k = first(x) {
      ?
    }
    case k_greater_fx: first(x) < k {
      ?
    }
  }
end
```

```{.deduce #all_nodes_AVL_insert}
theorem all_nodes_AVL_insert: 
  all A:Tree<Pair<Nat,Nat>>, k:Nat, v:Nat, P:fn Pair<Nat,Nat>->bool.
  if all_nodes(A, P) and P(pair(k,v))
  then all_nodes(AVL_insert(A, k, v), P)
proof
  sorry
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
<<is_BST_rotate_right_on>>
<<is_BST_rotate_left_on>>
<<search_balance>>
<<is_BST_AVL_insert>>
<<all_nodes_AVL_insert>>
<<AVL_search_insert_update>>

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
