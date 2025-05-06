# Fast Formal Merge Sort (work in progress)

The goal of this project is to write a reasonably fast, formally verified merge sort implementation in the Lean programming language. More specifically:

- To be considered a stable sorting algorithm, it should provably:

    - [x] Terminate without crashing (there are no infinite loops, and all array access instructions are in-bounds)

    - [ ] Return data in increasing order

    - [ ] Return a permutation of the input (i.e., the data is simply rearranged; no new data is added, and no existing data is removed)

    - [ ] Preserve the order of equal elements (stability)

- To be reasonably fast, it should:

    - [x] Receive and return values of type `Array` (instead of `List`, the type of singly linked lists)

    - [x] Mutate `Array` values in-place (instead of making expensive functional copies)

    - [x] Require only one auxiliary `Array` allocation

    - [x] Index into `Array` using `USize` (unboxed machine integers[^1], instead of `Nat` or `Fin`, boxed arbitrary precision integers)

    - [x] Contain proofs that all indexing operations (both read and write) are in-bounds at compile time, so no superfluous runtime checks are required

    - [x] Contain no extra non-`Prop` proof-related data, so that all proof work has no runtime performance impact.

- I chose an algorithm that was complex enough to allow for only one auxiliary `Array` allocation, while simple enough to be amenable to formal verification by a Lean beginner (me!). There are much more efficient merge sort implementations (such as Multiway Powersort), but these are also much more complex. The algorithm I chose to pursue here goes, roughly, as follows:

    a. Allocate an auxiliary array with the same length as the input array.

    b. Merge every two adjacent elements in the input array into the auxiliary array.

    c. Merge adjacent pairs of two elements in the auxiliary array into the input array.

    d. Continue merging between the two arrays (doubling the number of elements merged each time) until one is sorted. Return the sorted array.

### Performance Testing

Warning: these results are based on "eyeball statistics" (i.e., bad statistics). I will try and do something more substantial in the future.

#### Test Description

All tests were performed on `Array Nat` values of size `10^6`, except for `List.mergeSort`, which was performed on `List Nat`. The time spent allocating the `Array` or `List` values is not included in the elapsed time. The time spent allocating the auxiliary `Array` value for `Array.mergeSort` in each test *is* included in the elapsed time (unless the compiler is doing some smart optimizations that I'm not aware of). 

- mostlyAscending: An `Array` where most of the elements are already in ascending order. Specifically, it's an ascending `Array`, except that `size/2` two-element swaps were performed randomly, where the distance between the swapped elements is never more than `log2(size)`.

- randomWithDuplicates: An `Array` containing many duplicate values. Specifically, it contains `1 + log2(size)` distinct values.

- random: A randomly shuffled `Array` containing no duplicate values.

- ascending: An `Array` which is already sorted.

- descending: An `Array` which is sorted in reverse order.

- ascendingWithRandomTail: An `Array` where all but the last `10%` of values are sorted.

#### Results

| test name               | `Array.mergeSort` | `List.mergeSort` | `Array.qsortOrd` |
| ----------------------- | ----------------- | ---------------- | ---------------- |
| mostlyAscending         | 43ms              | 130ms            | 26104ms (26s)    |
| randomWithDuplicates    | 57ms              | 389ms            | 138469ms (138s)  |
| random                  | 80ms              | 380ms            | 221ms            |
| ascending               | 33ms              | 101ms            | 161ms            |
| descending              | 29ms              | 106ms            | 231ms            |
| ascendingWithRandomTail | 37ms              | 111ms            | 159ms            |

#### Analysis

`Array.mergeSort` is faster than `List.mergeSort` at sorting `10^6` `Nat` values, by a factor of `3-7x`.

`Array.mergeSort` is faster than `Array.qsortOrd` at sorting `10^6` `Nat` values, by a factor of `3-2429x`. Clearly, `Array.qsortOrd` experiences asymptotically worse performance on tests "mostlyAscending" and "randomWithDuplicates" than both `Array.mergeSort` and `List.mergeSort`.

It seems like `List.mergeSort`, despite being defined on linked lists, is faster at sorting `10^6` `Nat` values than `Array.qsortOrd`, especially when processing almost-sorted data, or data containing many duplicate values.

[^1]: I don't think Lean gives any guarantees that `USize` is unboxed. In fact, according to the reference, sometimes it will be boxed. My hope is that the implementation of `mergeSort` is simple enough to allow for unboxing. Inspecting the generated code (which I have yet to do) could prove/disprove this.