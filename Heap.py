union Heap {
  empty_tree;
  heap_node(Nat, Heap, Heap);
}

function heapify(Heap) -> Heap {
  heapify(heap_node(x, L, R)) =
    switch L {
      case empty_tree {  heap_node(x, L, R) }
      case heap_node(y, LL, LR) {
        switch R {
          
        
        if y ≤ x then
          heap_node(x, L, R)
        else
          heap_node(y, heapify(heap_node(x, LL, LR)), R)
        
      }
    }
}
