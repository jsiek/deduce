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
means of the following left and right rotations:

![Diagram of left and right rotation](https://www.dropbox.com/scl/fi/lob6iu0xc8zyg51tlvfqg/Rotate.png?rlkey=de7qa94a2ganr4dustmm30axn&raw=1)


