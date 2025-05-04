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

[^1]: I don't think Lean gives any guarantees that `USize` is unboxed. In fact, according to the reference, sometimes it will be boxed. My hope is that the implementation of `mergeSort` is simple enough to allow for unboxing. Inspecting the generated code (which I have yet to do) could prove/disprove this.