/-!
# Definition of `Array.ascending` and related theorems.

Here we define the notion of an `Array` being in ascending order: `Array.ascending le`.

This is in contrast to the standard library's definition of a `List` being in ascending
order: `List.Pariwise le`.

We do this so that in proving `Array.mergeSort` returns a sorted list, we can
work with a definition of 'ascending' that is more natural for `Array` values.

Most of this module is dedicated to proving `pairwise_le_iff_ascending_le_of_trans`,
which demonstrates that these two notions of 'ascending' are equivalent.
-/

variable
  {α}
  {le : α → α → Bool}

/--
A portion of a `List` that is non-decreasing, in the sense of `le`. The region is
inclusive on the lower end and bounded by `low`, and exclusive on the higher end
where it is bounded by `high`.

Why provide an alternative definition of 'ascending' for `List` values, when we are
really only concerned with `Array` values? We do this so that we can convert
proofs about `Array.ascendingSlice` into proofs about `List.ascendingSlice`, which
eases the process of showing that `Array.ascending le` is equivalent to
`List.Pairwise le`.
-/
def List.ascendingSlice
    {α}
    (lst : List α)
    (le : α → α → Bool)
    (low high : Nat)
    (high_le_lst_length : high ≤ lst.length)
    : Prop :=
  ∀ i : Nat,
    (inbounds : low ≤ i ∧ i + 1 < high) →
      le lst[i] lst[i + 1]

/--
Like `List.ascendingSlice`, except that it is known that if `b` is an arbitrary element
of the `List` which follows `a`, then `le a b` holds. This is in contrast to
`List.ascendingSlice`, where we only know `le a b` in the case of `a` and `b` being
adjacent elements of the list.

This definition is useful because it works similarly to `List.Pairwise`, in contrast
to `List.ascending` or `Array.ascending`, which both only reason about adjacent pairs
of elements (for simplicity).
-/
def List.ascendingSliceAll
    {α}
    (lst : List α)
    (le : α → α → Bool)
    (low high : Nat)
    (high_le_lst_length : high ≤ lst.length)
    : Prop :=
  ∀ i j : Nat,
    (i_lt_j : i < j) →
      (inbounds : low ≤ i ∧ j < high) →
        le lst[i] lst[j]

/--
Proofs of `List.ascendingSlice` can be converted into proofs of
`List.ascendingSliceAll`
-/
theorem List.ascendingSlice_all_of_ascendingSlice
    {α}
    (lst : List α)
    (le : α → α → Bool)
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (low high : Nat)
    (high_le_lst_length : high ≤ lst.length)
    (h : lst.ascendingSlice le low high high_le_lst_length)
    : lst.ascendingSliceAll le low high high_le_lst_length := by
  unfold List.ascendingSliceAll
  intro i j i_lt_j inbounds
  let rec loop
      (k : Nat)
      (k_inbounds : k > i ∧ k < j)
      (ih : le lst[i] lst[k])
      : le lst[i] lst[j] := by
    if adjacent : k + 1 = j then
      simp only [← adjacent]
      have : le lst[k] lst[k + 1] := h k (by omega)
      exact trans lst[i] lst[k] lst[k + 1] ih this
    else
      refine loop (k + 1) (by omega) ?ih
      have : le lst[k] lst[k + 1] := h k (by omega)
      exact trans lst[i] lst[k] lst[k + 1] ih this
  termination_by j - k
  if j_eq_i_add_one : j = i + 1 then
    simp only [j_eq_i_add_one]
    exact h i (by omega)
  else
    exact loop (i + 1) (by omega) (h i (by omega))

def List.ascending
    {α}
    (lst : List α)
    (le : α → α → Bool)
    : Prop :=
  ascendingSlice lst le 0 lst.length (by exact Nat.le_refl lst.length)

def Array.ascendingSlice
    {α}
    (arr : Array α)
    (le : α → α → Bool)
    (low high : Nat)
    (high_le_arr_size : high ≤ arr.size)
    : Prop :=
  ∀ i : Nat,
    (inbounds : low ≤ i ∧ i + 1 < high) →
      le arr[i] arr[i + 1]

def Array.ascending
    {α}
    (arr : Array α)
    (le : α → α → Bool)
    : Prop :=
  ascendingSlice arr le 0 arr.size (by exact Nat.le_refl arr.size)

theorem Array.ascending_of_empty {α} (le : α → α → Bool) : (#[] : Array α).ascending le := by
  unfold Array.ascending Array.ascendingSlice
  intro i inbounds
  have : i + 1 < 0 := inbounds.right
  contradiction

theorem Array.ascending_of_singleton {α} (a : α) (le : α → α → Bool) : #[a].ascending le := by
  unfold Array.ascending Array.ascendingSlice
  intro i inbounds
  have : i + 1 = 0 := by
    simp only [Nat.zero_le, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.lt_one_iff, Nat.le_refl, and_true, true_and] at inbounds
    exact inbounds
  contradiction

theorem List.toArray_ascending_of_ascending
    (l : List α)
    (h : l.ascending le)
    : l.toArray.ascending le := by
  unfold Array.ascending Array.ascendingSlice
  unfold List.ascending List.ascendingSlice at h
  intro i inbounds
  exact h i inbounds

theorem Array.toList_ascending_of_ascending
    (arr : Array α)
    (h : arr.ascending le)
    : arr.toList.ascending le := by
  unfold List.ascending List.ascendingSlice
  unfold Array.ascending Array.ascendingSlice at h
  intro i inbounds
  exact h i inbounds

theorem List.getElem_cons_mem
    {α}
    (a : α)
    (l : List α)
    (j : Nat)
    (j_lt_length : j < (a :: l).length)
    (j_gt_zero : j > 0)
    : (a :: l)[j] ∈ l := by
  cases j with
  | zero => simp at j_gt_zero
  | succ j' => simp [List.get]

theorem le_head_of_ascending_of_mem_tail
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (head a : α)
    (tail : List α)
    (a_mem_tail : a ∈ tail)
    (h : (head :: tail).ascending le)
    : le head a = true := by
  have h_all := List.ascendingSlice_all_of_ascendingSlice
    (head :: tail) le trans 0 (head :: tail).length
    (by exact Nat.le_refl (head :: tail).length) h
  unfold List.ascendingSliceAll at h_all
  have ⟨a_index, tail_get_eq_a⟩ := List.get_of_mem a_mem_tail
  have h := h_all 0 (a_index + 1) (Nat.zero_lt_succ a_index) ?inbounds
  case inbounds =>
    simp only [Nat.le_refl, List.length_cons, Nat.add_lt_add_iff_right, Fin.is_lt, and_self]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  have getElem_eq_get : tail[(↑a_index : Nat)] = tail.get a_index := rfl
  rwa [getElem_eq_get, tail_get_eq_a] at h

namespace MergeSort.Internal

attribute [local instance] boolRelToRel

theorem ascending_le_of_pairwise_le
    {lst : List α}
    (h : lst.Pairwise le)
    : lst.ascending le := by
  unfold List.ascending List.ascendingSlice
  intro i inbounds
  induction h generalizing i
  case nil =>
    have : i + 1 < 0 := inbounds.right
    contradiction
  case cons a' b' ih =>
    rename_i a l
    by_cases i_eq_zero : i = 0
    . simp only [i_eq_zero, List.getElem_cons_zero]
      refine a' (a :: l)[1] ?_
      exact List.getElem_cons_mem a l 1 (by omega) (by omega)
    . have rhs_eq := List.getElem_cons_succ a l i (by omega)
      rw [rhs_eq]
      have lhs_eq := List.getElem_cons_succ a l (i - 1) (by omega)
      have i_pred_succ_eq_i : i - 1 + 1 = i := by omega
      simp only [i_pred_succ_eq_i] at lhs_eq
      rw [lhs_eq]
      have inbounds' : i < l.length := Nat.succ_lt_succ_iff.mp inbounds.right
      have h := ih (i - 1) (by omega)
      simp only [i_pred_succ_eq_i] at h
      exact h

theorem toArray_ascending_of_pairwise_le
    {lst : List α}
    (h : lst.Pairwise le)
    : lst.toArray.ascending le := by
  refine List.toArray_ascending_of_ascending lst ?_
  exact ascending_le_of_pairwise_le h

theorem pairwise_le_of_ascending_le
    (lst : List α)
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (h : lst.ascending le)
    : lst.Pairwise le := by
  unfold List.ascending List.ascendingSlice at h
  induction lst
  case nil => exact List.Pairwise.nil
  case cons head tail ih =>
    rw [List.pairwise_cons]
    apply And.intro
    . intro a' a'_mem_tail
      exact le_head_of_ascending_of_mem_tail trans head a' tail a'_mem_tail h
    . refine ih ?_
      intro i inbounds
      have : i + 2 < (head :: tail).length := by
        simp only [List.length_cons]
        omega
      have le_head_cons_tail := h (i + 1) (by omega)
      have left_eq := List.getElem_cons_succ head tail i (by omega)
      have right_eq := List.getElem_cons_succ head tail (i + 1) (by omega)
      rw [left_eq, right_eq] at le_head_cons_tail
      exact le_head_cons_tail

theorem pairwise_le_of_toArray_ascending_le
    {lst : List α}
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (h : lst.toArray.ascending le)
    : lst.Pairwise le := by
  exact pairwise_le_of_ascending_le lst trans h

theorem pairwise_le_iff_ascending_le_of_trans
    {lst : List α}
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    : lst.Pairwise le ↔ lst.toArray.ascending le := by
  apply Iff.intro
  case mp => exact toArray_ascending_of_pairwise_le
  case mpr => exact pairwise_le_of_toArray_ascending_le trans

end MergeSort.Internal
