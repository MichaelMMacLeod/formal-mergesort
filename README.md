# Formal Mergesort (work in progress)

`LeanSorting/Total.lean` defines `Array.mergeSort`, an implementation
of [mergesort](https://en.wikipedia.org/wiki/Merge_sort) that uses one auxiliary array and sorts in-place.

I have proved that all array accesses are in-bounds (i.e., `Array.mergeSort` uses `Fin`-based indexing) and that `Array.mergeSort` terminates, but have not yet proved that it actually sorts the array.

Some 'eyeball' performance testing suggests that the performance of `Array.mergeSort` is on-par with Lean's standard library `Array.qsort` (quicksort) implementation. More rigorous statistical testing is needed to determine actual performance differences.

An additional implementation, `Array.mergeSortPartial`, is also provided in `LeanSorting/Partial.lean`. It is the same algorithm as `Array.mergeSort`, except that it uses `panic`-based indexing. Because of this, the code is more concise, and thus is easier to understand. I recommend reading this first if you want to learn how the code works.

Lean uses reference counting for memory management, and will mutate data in-place if there are no other references to it. `Array.mergeSort` takes advantage of this and ensures that no copies of the original or auxiliary array are made during the sorting process.

You may notice that `Array.mergeSort` requires the type of element it is sorting to implement `Inhabited`. Often times when seen on a type signature this suggests that the function in question uses `panic`-based indexing, as `panic`-based indexing requires the element type to implement `Inhabited`. This is not the case with `Array.mergeSort`; we need `Inhabited` here to create default values for the auxiliary array when we allocate it before we start sorting.

Throughout the file `LeanSorting/Total.lean` you will see several structures defined, each named `M<something>`. The point of these structures is to group together hypotheses and data required for using `Fin`-based indexing. Without them, the code becomes a huge mess, with loops requiring super-long and unmaintainable type signatures.

See the file `LeanSorting/TotalExamples.lean` for some examples.