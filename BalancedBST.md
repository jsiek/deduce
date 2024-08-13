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
  sorry
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
      have x_less_C: all_nodes(C, λr{first(x) < first(r)}) 
        by sorry
      have BST_A: is_BST(A) 
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      have B_less_y: all_nodes(B, λl{first(l) < first(y)}) 
        by sorry
      have y_less_C: all_nodes(C, λr{first(y) < first(r)}) 
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      have BST_B: is_BST(B)
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      have BST_C: is_BST(C)
        by definition {is_BST, is_BST} in rewrite AxB_node in prem
      (A_less_x, x_less_B, fx_less_fy, x_less_C, BST_A, B_less_y, y_less_C, BST_B, BST_C)
    }
  }
end
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
    case true suppose hL_hR {
      switch R {
        case EmptyTree suppose R_mt {
          conclude false 
            by definition {operator <, operator+, height, operator≤} in
               rewrite R_mt in hL_hR
        }
        case TreeNode(RL, y, RR) suppose R_node {
          switch height(RL) ≤ height(RR) {
            case true suppose hRL_hRR {
              suffices BST_search(TreeNode(L, x, TreeNode(RL, y, RR)))
                  = BST_search(rotate_left(L, x, RL, y, RR))
                  with definition balance
                  and rewrite (rewrite R_node in hL_hR) | hRL_hRR
              have fx_less_fy: first(x) < first(y)
                by rewrite R_node in definition {is_BST,all_nodes} in BST_LxR
              symmetric apply search_rotate_left[L,x,RL,y,RR] to fx_less_fy
            }
            case false suppose hRL_hRR {
              suffices BST_search(TreeNode(L, x, TreeNode(RL, y, RR))) 
                     = BST_search(rotate_left_on(L, x, rotate_right_on(RL, y, RR)))
                  with definition balance
                   and rewrite (rewrite R_node in hL_hR) | hRL_hRR
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
                    have x_less_RR: all_nodes(rotate_right_on(RL, y, RR), λr{first(x) < first(r)}) 
                      by rewrite symmetric all_nodes_rotate_right_on[RL,y,RR, λr{first(x) < first(r)}] 
                         in x_less_RLyRR
                    ?
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
    }
    case false {
      ?
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

<<search_rotate>>
<<search_rotate_right>>
<<search_rotate_left>>
<<search_rotate_right_on>>
<<search_rotate_left_on>>

<<search_node>>
<<search_compositional>>
<<rotate_right_on_height>>
<<all_nodes_rotate_right_on>>
<<is_BST_rotate_right_on>>
<<search_balance>>

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
