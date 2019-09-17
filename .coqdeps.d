RCCBase.vo RCCBase.glob RCCBase.v.beautified: RCCBase.v
RCCBase.vio: RCCBase.v
./Sorting/QuicksortSpec.vo ./Sorting/QuicksortSpec.glob ./Sorting/QuicksortSpec.v.beautified: ./Sorting/QuicksortSpec.v ./Sorting/QuickSort.vo
./Sorting/QuicksortSpec.vio: ./Sorting/QuicksortSpec.v ./Sorting/QuickSort.vio
./Sorting/Perm.vo ./Sorting/Perm.glob ./Sorting/Perm.v.beautified: ./Sorting/Perm.v RCCBase.vo ./Structures/LinDec.vo ./Sorting/ListLemmas.vo ./Structures/TrichDec.vo
./Sorting/Perm.vio: ./Sorting/Perm.v RCCBase.vio ./Structures/LinDec.vio ./Sorting/ListLemmas.vio ./Structures/TrichDec.vio
./Sorting/ListLemmas.vo ./Sorting/ListLemmas.glob ./Sorting/ListLemmas.v.beautified: ./Sorting/ListLemmas.v RCCBase.vo ./Structures/LinDec.vo ./Structures/TrichDec.vo
./Sorting/ListLemmas.vio: ./Sorting/ListLemmas.v RCCBase.vio ./Structures/LinDec.vio ./Structures/TrichDec.vio
./Sorting/TreeSort.vo ./Sorting/TreeSort.glob ./Sorting/TreeSort.v.beautified: ./Sorting/TreeSort.v ./Structures/LinDec.vo ./Sorting/Sort.vo ./Basic/BTree.vo ./DS/BST.vo ./Sorting/ListLemmas.vo
./Sorting/TreeSort.vio: ./Sorting/TreeSort.v ./Structures/LinDec.vio ./Sorting/Sort.vio ./Basic/BTree.vio ./DS/BST.vio ./Sorting/ListLemmas.vio
./Sorting/SplaySort.vo ./Sorting/SplaySort.glob ./Sorting/SplaySort.v.beautified: ./Sorting/SplaySort.v ./Sorting/Sort.vo ./Sorting/ListLemmas.vo ./DS/BST.vo ./DS/SplayHeap.vo
./Sorting/SplaySort.vio: ./Sorting/SplaySort.v ./Sorting/Sort.vio ./Sorting/ListLemmas.vio ./DS/BST.vio ./DS/SplayHeap.vio
./Sorting/Sort_generalized.vo ./Sorting/Sort_generalized.glob ./Sorting/Sort_generalized.v.beautified: ./Sorting/Sort_generalized.v RCCBase.vo ./Sorting/Perm.vo
./Sorting/Sort_generalized.vio: ./Sorting/Sort_generalized.v RCCBase.vio ./Sorting/Perm.vio
./Sorting/Test.vo ./Sorting/Test.glob ./Sorting/Test.v.beautified: ./Sorting/Test.v ./Sorting/MergeSort.vo ./Sorting/QuickSort.vo ./Sorting/TreeSort.vo ./Sorting/RedblackSort.vo ./Sorting/PairingSort.vo ./Sorting/SplaySort.vo ./Sorting/ListLemmas.vo ./DS/LeftistHeap.vo
./Sorting/Test.vio: ./Sorting/Test.v ./Sorting/MergeSort.vio ./Sorting/QuickSort.vio ./Sorting/TreeSort.vio ./Sorting/RedblackSort.vio ./Sorting/PairingSort.vio ./Sorting/SplaySort.vio ./Sorting/ListLemmas.vio ./DS/LeftistHeap.vio
./Sorting/Perm_generalized.vo ./Sorting/Perm_generalized.glob ./Sorting/Perm_generalized.v.beautified: ./Sorting/Perm_generalized.v RCCBase.vo ./Structures/LinDec.vo ./Sorting/ListLemmas_generalized.vo ./Structures/TrichDec.vo
./Sorting/Perm_generalized.vio: ./Sorting/Perm_generalized.v RCCBase.vio ./Structures/LinDec.vio ./Sorting/ListLemmas_generalized.vio ./Structures/TrichDec.vio
./Sorting/TreeSortSpec.vo ./Sorting/TreeSortSpec.glob ./Sorting/TreeSortSpec.v.beautified: ./Sorting/TreeSortSpec.v ./Sorting/TreeSort.vo
./Sorting/TreeSortSpec.vio: ./Sorting/TreeSortSpec.v ./Sorting/TreeSort.vio
./Sorting/QuickSort.vo ./Sorting/QuickSort.glob ./Sorting/QuickSort.v.beautified: ./Sorting/QuickSort.v ./Sorting/ListLemmas.vo ./Sorting/Sort.vo ./Sorting/InsertionSort.vo ./Structures/TrichDec.vo
./Sorting/QuickSort.vio: ./Sorting/QuickSort.v ./Sorting/ListLemmas.vio ./Sorting/Sort.vio ./Sorting/InsertionSort.vio ./Structures/TrichDec.vio
./Sorting/BraunMergeSort.vo ./Sorting/BraunMergeSort.glob ./Sorting/BraunMergeSort.v.beautified: ./Sorting/BraunMergeSort.v ./Sorting/Sort.vo ./Sorting/MergeSort.vo
./Sorting/BraunMergeSort.vio: ./Sorting/BraunMergeSort.v ./Sorting/Sort.vio ./Sorting/MergeSort.vio
./Sorting/SelectionSort.vo ./Sorting/SelectionSort.glob ./Sorting/SelectionSort.v.beautified: ./Sorting/SelectionSort.v ./Sorting/Sort.vo
./Sorting/SelectionSort.vio: ./Sorting/SelectionSort.v ./Sorting/Sort.vio
./Sorting/ListLemmas_generalized.vo ./Sorting/ListLemmas_generalized.glob ./Sorting/ListLemmas_generalized.v.beautified: ./Sorting/ListLemmas_generalized.v RCCBase.vo ./Structures/LinDec.vo ./Structures/TrichDec.vo
./Sorting/ListLemmas_generalized.vio: ./Sorting/ListLemmas_generalized.v RCCBase.vio ./Structures/LinDec.vio ./Structures/TrichDec.vio
./Sorting/MergeSort.vo ./Sorting/MergeSort.glob ./Sorting/MergeSort.v.beautified: ./Sorting/MergeSort.v ./Sorting/Sort.vo ./Sorting/ListLemmas.vo
./Sorting/MergeSort.vio: ./Sorting/MergeSort.v ./Sorting/Sort.vio ./Sorting/ListLemmas.vio
./Sorting/MergeSortSpec.vo ./Sorting/MergeSortSpec.glob ./Sorting/MergeSortSpec.v.beautified: ./Sorting/MergeSortSpec.v ./Sorting/MergeSort.vo
./Sorting/MergeSortSpec.vio: ./Sorting/MergeSortSpec.v ./Sorting/MergeSort.vio
./Sorting/Sort.vo ./Sorting/Sort.glob ./Sorting/Sort.v.beautified: ./Sorting/Sort.v RCCBase.vo ./Sorting/Perm.vo
./Sorting/Sort.vio: ./Sorting/Sort.v RCCBase.vio ./Sorting/Perm.vio
./Sorting/InsertionSort.vo ./Sorting/InsertionSort.glob ./Sorting/InsertionSort.v.beautified: ./Sorting/InsertionSort.v ./Sorting/Sort.vo
./Sorting/InsertionSort.vio: ./Sorting/InsertionSort.v ./Sorting/Sort.vio
./Sorting/PairingSort.vo ./Sorting/PairingSort.glob ./Sorting/PairingSort.v.beautified: ./Sorting/PairingSort.v ./Sorting/Sort.vo ./Sorting/ListLemmas.vo ./DS/PairingHeap.vo
./Sorting/PairingSort.vio: ./Sorting/PairingSort.v ./Sorting/Sort.vio ./Sorting/ListLemmas.vio ./DS/PairingHeap.vio
./Sorting/SortSpec.vo ./Sorting/SortSpec.glob ./Sorting/SortSpec.v.beautified: ./Sorting/SortSpec.v RCCBase.vo ./Sorting/Sort.vo ./Sorting/ListLemmas.vo ./Sorting/SelectionSort.vo
./Sorting/SortSpec.vio: ./Sorting/SortSpec.v RCCBase.vio ./Sorting/Sort.vio ./Sorting/ListLemmas.vio ./Sorting/SelectionSort.vio
./Sorting/RedblackSort.vo ./Sorting/RedblackSort.glob ./Sorting/RedblackSort.v.beautified: ./Sorting/RedblackSort.v ./DS/RedBlack.vo ./Sorting/ListLemmas.vo
./Sorting/RedblackSort.vio: ./Sorting/RedblackSort.v ./DS/RedBlack.vio ./Sorting/ListLemmas.vio
./Reflection/UCRingRefl.vo ./Reflection/UCRingRefl.glob ./Reflection/UCRingRefl.v.beautified: ./Reflection/UCRingRefl.v ./Structures/UCRing.vo
./Reflection/UCRingRefl.vio: ./Reflection/UCRingRefl.v ./Structures/UCRing.vio
./Reflection/Test/FormulaTest.vo ./Reflection/Test/FormulaTest.glob ./Reflection/Test/FormulaTest.v.beautified: ./Reflection/Test/FormulaTest.v ./Reflection/Formula.vo
./Reflection/Test/FormulaTest.vio: ./Reflection/Test/FormulaTest.v ./Reflection/Formula.vio
./Reflection/Test/CMonExpTest.vo ./Reflection/Test/CMonExpTest.glob ./Reflection/Test/CMonExpTest.v.beautified: ./Reflection/Test/CMonExpTest.v ./Reflection/CMonRefl2.vo
./Reflection/Test/CMonExpTest.vio: ./Reflection/Test/CMonExpTest.v ./Reflection/CMonRefl2.vio
./Reflection/Test/CMonFormulaTest.vo ./Reflection/Test/CMonFormulaTest.glob ./Reflection/Test/CMonFormulaTest.v.beautified: ./Reflection/Test/CMonFormulaTest.v ./Reflection/CMonRefl.vo
./Reflection/Test/CMonFormulaTest.vio: ./Reflection/Test/CMonFormulaTest.v ./Reflection/CMonRefl.vio
./Reflection/Formula.vo ./Reflection/Formula.glob ./Reflection/Formula.v.beautified: ./Reflection/Formula.v RCCBase.vo
./Reflection/Formula.vio: ./Reflection/Formula.v RCCBase.vio
./Reflection/CMonRefl2.vo ./Reflection/CMonRefl2.glob ./Reflection/CMonRefl2.v.beautified: ./Reflection/CMonRefl2.v ./Sorting/InsertionSort.vo ./Sorting/SortSpec.vo ./Structures/CMon.vo
./Reflection/CMonRefl2.vio: ./Reflection/CMonRefl2.v ./Sorting/InsertionSort.vio ./Sorting/SortSpec.vio ./Structures/CMon.vio
./Reflection/Reflection_a_la_carte.vo ./Reflection/Reflection_a_la_carte.glob ./Reflection/Reflection_a_la_carte.v.beautified: ./Reflection/Reflection_a_la_carte.v RCCBase.vo
./Reflection/Reflection_a_la_carte.vio: ./Reflection/Reflection_a_la_carte.v RCCBase.vio
./Reflection/ReflectionClass.vo ./Reflection/ReflectionClass.glob ./Reflection/ReflectionClass.v.beautified: ./Reflection/ReflectionClass.v RCCBase.vo
./Reflection/ReflectionClass.vio: ./Reflection/ReflectionClass.v RCCBase.vio
./Reflection/ReflectionLtac.vo ./Reflection/ReflectionLtac.glob ./Reflection/ReflectionLtac.v.beautified: ./Reflection/ReflectionLtac.v RCCBase.vo
./Reflection/ReflectionLtac.vio: ./Reflection/ReflectionLtac.v RCCBase.vio
./Reflection/CMonRefl.vo ./Reflection/CMonRefl.glob ./Reflection/CMonRefl.v.beautified: ./Reflection/CMonRefl.v ./Structures/CMon.vo ./Sorting/InsertionSort.vo ./Sorting/SortSpec.vo
./Reflection/CMonRefl.vio: ./Reflection/CMonRefl.v ./Structures/CMon.vio ./Sorting/InsertionSort.vio ./Sorting/SortSpec.vio
./Reflection/Formula2.vo ./Reflection/Formula2.glob ./Reflection/Formula2.v.beautified: ./Reflection/Formula2.v RCCBase.vo
./Reflection/Formula2.vio: ./Reflection/Formula2.v RCCBase.vio
./Reflection/MonRefl_NBE.vo ./Reflection/MonRefl_NBE.glob ./Reflection/MonRefl_NBE.v.beautified: ./Reflection/MonRefl_NBE.v ./Structures/CMon.vo ./Sorting/InsertionSort.vo ./Sorting/SortSpec.vo
./Reflection/MonRefl_NBE.vio: ./Reflection/MonRefl_NBE.v ./Structures/CMon.vio ./Sorting/InsertionSort.vio ./Sorting/SortSpec.vio
./Trash/Yoneda2.vo ./Trash/Yoneda2.glob ./Trash/Yoneda2.v.beautified: ./Trash/Yoneda2.v
./Trash/Yoneda2.vio: ./Trash/Yoneda2.v
./Trash/Yoneda.vo ./Trash/Yoneda.glob ./Trash/Yoneda.v.beautified: ./Trash/Yoneda.v
./Trash/Yoneda.vio: ./Trash/Yoneda.v
./Trash/Cantor.vo ./Trash/Cantor.glob ./Trash/Cantor.v.beautified: ./Trash/Cantor.v
./Trash/Cantor.vio: ./Trash/Cantor.v
./Trash/BinomialTreeTrash.vo ./Trash/BinomialTreeTrash.glob ./Trash/BinomialTreeTrash.v.beautified: ./Trash/BinomialTreeTrash.v
./Trash/BinomialTreeTrash.vio: ./Trash/BinomialTreeTrash.v
./Trash/Scheduling2.vo ./Trash/Scheduling2.glob ./Trash/Scheduling2.v.beautified: ./Trash/Scheduling2.v ./Structures/LinDec.vo ./Structures/TrichDec.vo ./Sorting/InsertionSort.vo
./Trash/Scheduling2.vio: ./Trash/Scheduling2.v ./Structures/LinDec.vio ./Structures/TrichDec.vio ./Sorting/InsertionSort.vio
./Trash/Prod.vo ./Trash/Prod.glob ./Trash/Prod.v.beautified: ./Trash/Prod.v
./Trash/Prod.vio: ./Trash/Prod.v
./Trash/Scheduling.vo ./Trash/Scheduling.glob ./Trash/Scheduling.v.beautified: ./Trash/Scheduling.v ./Structures/LinDec.vo ./Structures/TrichDec.vo ./Sorting/InsertionSort.vo
./Trash/Scheduling.vio: ./Trash/Scheduling.v ./Structures/LinDec.vio ./Structures/TrichDec.vio ./Sorting/InsertionSort.vio
./Trash/DFA.vo ./Trash/DFA.glob ./Trash/DFA.v.beautified: ./Trash/DFA.v
./Trash/DFA.vio: ./Trash/DFA.v
./Trash/LazyList.vo ./Trash/LazyList.glob ./Trash/LazyList.v.beautified: ./Trash/LazyList.v
./Trash/LazyList.vio: ./Trash/LazyList.v
./Trash/Enumerable.vo ./Trash/Enumerable.glob ./Trash/Enumerable.v.beautified: ./Trash/Enumerable.v
./Trash/Enumerable.vio: ./Trash/Enumerable.v
./Trash/LazyEvalTest.vo ./Trash/LazyEvalTest.glob ./Trash/LazyEvalTest.v.beautified: ./Trash/LazyEvalTest.v
./Trash/LazyEvalTest.vio: ./Trash/LazyEvalTest.v
./ADT/Sortable.vo ./ADT/Sortable.glob ./ADT/Sortable.v.beautified: ./ADT/Sortable.v RCCBase.vo ./Structures/LinDec.vo ./Sorting/Sort.vo ./Sorting/MergeSort.vo
./ADT/Sortable.vio: ./ADT/Sortable.v RCCBase.vio ./Structures/LinDec.vio ./Sorting/Sort.vio ./Sorting/MergeSort.vio
./ADT/PartialFinMap.vo ./ADT/PartialFinMap.glob ./ADT/PartialFinMap.v.beautified: ./ADT/PartialFinMap.v RCCBase.vo ./Structures/LinDec.vo
./ADT/PartialFinMap.vio: ./ADT/PartialFinMap.v RCCBase.vio ./Structures/LinDec.vio
./ADT/Sequence.vo ./ADT/Sequence.glob ./ADT/Sequence.v.beautified: ./ADT/Sequence.v RCCBase.vo
./ADT/Sequence.vio: ./ADT/Sequence.v RCCBase.vio
./ADT/Queue.vo ./ADT/Queue.glob ./ADT/Queue.v.beautified: ./ADT/Queue.v RCCBase.vo
./ADT/Queue.vio: ./ADT/Queue.v RCCBase.vio
./ADT/Deque.vo ./ADT/Deque.glob ./ADT/Deque.v.beautified: ./ADT/Deque.v RCCBase.vo
./ADT/Deque.vio: ./ADT/Deque.v RCCBase.vio
./ADT/Stack.vo ./ADT/Stack.glob ./ADT/Stack.v.beautified: ./ADT/Stack.v RCCBase.vo
./ADT/Stack.vio: ./ADT/Stack.v RCCBase.vio
./ADT/Set.vo ./ADT/Set.glob ./ADT/Set.v.beautified: ./ADT/Set.v RCCBase.vo ./Structures/LinDec.vo
./ADT/Set.vio: ./ADT/Set.v RCCBase.vio ./Structures/LinDec.vio
./ADT/PriorityQueue.vo ./ADT/PriorityQueue.glob ./ADT/PriorityQueue.v.beautified: ./ADT/PriorityQueue.v RCCBase.vo ./Structures/LinDec.vo ./Sorting/Sort.vo
./ADT/PriorityQueue.vio: ./ADT/PriorityQueue.v RCCBase.vio ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/RedBlack.vo ./DS/RedBlack.glob ./DS/RedBlack.v.beautified: ./DS/RedBlack.v RCCBase.vo ./Basic/BTree.vo ./Structures/LinDec.vo ./Sorting/Sort.vo
./DS/RedBlack.vio: ./DS/RedBlack.v RCCBase.vio ./Basic/BTree.vio ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/BinomialHeap.vo ./DS/BinomialHeap.glob ./DS/BinomialHeap.v.beautified: ./DS/BinomialHeap.v ./Structures/LinDec.vo RCCBase.vo
./DS/BinomialHeap.vio: ./DS/BinomialHeap.v ./Structures/LinDec.vio RCCBase.vio
./DS/HeightBalanced.vo ./DS/HeightBalanced.glob ./DS/HeightBalanced.v.beautified: ./DS/HeightBalanced.v RCCBase.vo ./Basic/BTree.vo ./Structures/LinDec.vo ./Sorting/Sort.vo ./Structures/TrichDec.vo
./DS/HeightBalanced.vio: ./DS/HeightBalanced.v RCCBase.vio ./Basic/BTree.vio ./Structures/LinDec.vio ./Sorting/Sort.vio ./Structures/TrichDec.vio
./DS/PhysicistsQueue.vo ./DS/PhysicistsQueue.glob ./DS/PhysicistsQueue.v.beautified: ./DS/PhysicistsQueue.v RCCBase.vo ./Structures/LinDec.vo
./DS/PhysicistsQueue.vio: ./DS/PhysicistsQueue.v RCCBase.vio ./Structures/LinDec.vio
./DS/Positional.vo ./DS/Positional.glob ./DS/Positional.v.beautified: ./DS/Positional.v RCCBase.vo
./DS/Positional.vio: ./DS/Positional.v RCCBase.vio
./DS/PairingHeap.vo ./DS/PairingHeap.glob ./DS/PairingHeap.v.beautified: ./DS/PairingHeap.v
./DS/PairingHeap.vio: ./DS/PairingHeap.v
./DS/SplayHeap2.vo ./DS/SplayHeap2.glob ./DS/SplayHeap2.v.beautified: ./DS/SplayHeap2.v ./Basic/BTree.vo ./DS/BST.vo ./Structures/LinDec.vo ./Sorting/Sort.vo
./DS/SplayHeap2.vio: ./DS/SplayHeap2.v ./Basic/BTree.vio ./DS/BST.vio ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/Heap.vo ./DS/Heap.glob ./DS/Heap.v.beautified: ./DS/Heap.v ./Basic/BTree.vo ./Structures/LinDec.vo ./Sorting/Sort.vo
./DS/Heap.vio: ./DS/Heap.v ./Basic/BTree.vio ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/Queue.vo ./DS/Queue.glob ./DS/Queue.v.beautified: ./DS/Queue.v RCCBase.vo
./DS/Queue.vio: ./DS/Queue.v RCCBase.vio
./DS/Deque.vo ./DS/Deque.glob ./DS/Deque.v.beautified: ./DS/Deque.v RCCBase.vo
./DS/Deque.vio: ./DS/Deque.v RCCBase.vio
./DS/BST.vo ./DS/BST.glob ./DS/BST.v.beautified: ./DS/BST.v ./Basic/BTree.vo ./Structures/LinDec.vo ./Sorting/Sort.vo
./DS/BST.vio: ./DS/BST.v ./Basic/BTree.vio ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/LList2.vo ./DS/LList2.glob ./DS/LList2.v.beautified: ./DS/LList2.v RCCBase.vo
./DS/LList2.vio: ./DS/LList2.v RCCBase.vio
./DS/Okasaki_Ch10.vo ./DS/Okasaki_Ch10.glob ./DS/Okasaki_Ch10.v.beautified: ./DS/Okasaki_Ch10.v RCCBase.vo
./DS/Okasaki_Ch10.vio: ./DS/Okasaki_Ch10.v RCCBase.vio
./DS/SplayHeap.vo ./DS/SplayHeap.glob ./DS/SplayHeap.v.beautified: ./DS/SplayHeap.v ./Basic/BTree.vo ./DS/BST.vo ./Structures/LinDec.vo ./Sorting/Sort.vo
./DS/SplayHeap.vio: ./DS/SplayHeap.v ./Basic/BTree.vio ./DS/BST.vio ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/LeftistHeap.vo ./DS/LeftistHeap.glob ./DS/LeftistHeap.v.beautified: ./DS/LeftistHeap.v ./Structures/LinDec.vo ./Sorting/Sort.vo
./DS/LeftistHeap.vio: ./DS/LeftistHeap.v ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/LeftistHeap2.vo ./DS/LeftistHeap2.glob ./DS/LeftistHeap2.v.beautified: ./DS/LeftistHeap2.v ./Structures/LinDec.vo ./Sorting/Sort.vo
./DS/LeftistHeap2.vio: ./DS/LeftistHeap2.v ./Structures/LinDec.vio ./Sorting/Sort.vio
./DS/LList.vo ./DS/LList.glob ./DS/LList.v.beautified: ./DS/LList.v RCCBase.vo ./Sorting/InsertionSort.vo
./DS/LList.vio: ./DS/LList.v RCCBase.vio ./Sorting/InsertionSort.vio
./Structures/TrichDec.vo ./Structures/TrichDec.glob ./Structures/TrichDec.v.beautified: ./Structures/TrichDec.v RCCBase.vo ./Structures/LinDec.vo
./Structures/TrichDec.vio: ./Structures/TrichDec.v RCCBase.vio ./Structures/LinDec.vio
./Structures/LinDec.vo ./Structures/LinDec.glob ./Structures/LinDec.v.beautified: ./Structures/LinDec.v
./Structures/LinDec.vio: ./Structures/LinDec.v
./Structures/CMon.vo ./Structures/CMon.glob ./Structures/CMon.v.beautified: ./Structures/CMon.v RCCBase.vo
./Structures/CMon.vio: ./Structures/CMon.v RCCBase.vio
./Structures/UCRing.vo ./Structures/UCRing.glob ./Structures/UCRing.v.beautified: ./Structures/UCRing.v RCCBase.vo
./Structures/UCRing.vio: ./Structures/UCRing.v RCCBase.vio
./Basic/BTree.vo ./Basic/BTree.glob ./Basic/BTree.v.beautified: ./Basic/BTree.v RCCBase.vo ./Structures/LinDec.vo ./Sorting/ListLemmas.vo ./Sorting/Sort.vo
./Basic/BTree.vio: ./Basic/BTree.v RCCBase.vio ./Structures/LinDec.vio ./Sorting/ListLemmas.vio ./Sorting/Sort.vio
./Basic/BinomialTree.vo ./Basic/BinomialTree.glob ./Basic/BinomialTree.v.beautified: ./Basic/BinomialTree.v ./Structures/LinDec.vo RCCBase.vo
./Basic/BinomialTree.vio: ./Basic/BinomialTree.v ./Structures/LinDec.vio RCCBase.vio
./Basic/NonEmptyTree.vo ./Basic/NonEmptyTree.glob ./Basic/NonEmptyTree.v.beautified: ./Basic/NonEmptyTree.v
./Basic/NonEmptyTree.vio: ./Basic/NonEmptyTree.v
./Basic/Tree.vo ./Basic/Tree.glob ./Basic/Tree.v.beautified: ./Basic/Tree.v ./Structures/LinDec.vo RCCBase.vo
./Basic/Tree.vio: ./Basic/Tree.v ./Structures/LinDec.vio RCCBase.vio
./Memoization/Memoize2.vo ./Memoization/Memoize2.glob ./Memoization/Memoize2.v.beautified: ./Memoization/Memoize2.v
./Memoization/Memoize2.vio: ./Memoization/Memoize2.v
./Memoization/Memoize.vo ./Memoization/Memoize.glob ./Memoization/Memoize.v.beautified: ./Memoization/Memoize.v RCCBase.vo ./Basic/BTree.vo ./DS/BST.vo ./Structures/TrichDec.vo
./Memoization/Memoize.vio: ./Memoization/Memoize.v RCCBase.vio ./Basic/BTree.vio ./DS/BST.vio ./Structures/TrichDec.vio
