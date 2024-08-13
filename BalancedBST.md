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
For AVL, the invariant is that two siblings only differ in height by
at most 1.

![Diagram of several AVL Trees](https://www.dropbox.com/scl/fi/wh06d9vvdb2b5rkxuebsx/AVLTrees.png?rlkey=6nhmiffmprvgwzvftohwkivqs&raw=1)



The main idea of the AVL algorithm is that we can change the 

