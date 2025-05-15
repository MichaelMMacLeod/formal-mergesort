import MergeSort.Fin.Extras
import Std.Tactic.BVDecide
import Init.Data.List.Basic


abbrev USize.succ (n : USize) := n + 1

theorem USize.ge_of_eq {a b : USize} (h : a = b) : a ≥ b := USize.le_of_eq (Eq.symm h)

theorem USize.add_one_sub_right_comm
    {a b c : USize}
    : a + b - c + 1 = a + (b + 1) - c := by
  rw [← USize.toNat_inj]
  repeat rw [USize.toNat_add, USize.toNat_sub]
  simp [Nat.add_assoc, Nat.add_comm 1]

theorem USize.add_sub_self_left
    {a b : USize}
    : a + b - a = b := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    simp +arith only [← USize.toNat_inj, USize.toNat_sub, USize.toNat_add, Nat.mod_add_mod]
    rw [← Nat.add_sub_assoc (Nat.le_of_succ_le (USize.toNat_lt_size _)),
      Nat.add_assoc, Nat.add_sub_self_left, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (USize.toNat_lt_two_pow_numBits b)

theorem USize.add_one_le_of_lt {a b : USize} (h : a < b) : a + 1 ≤ b :=
  Fin.add_one_le_of_lt h

theorem USize.add_sub_add_one_le_of_lt
    {a b c : USize}
    (h : b < c)
    : a + b - a + 1 ≤ c := by
  rw [USize.add_one_sub_right_comm, USize.add_sub_self_left]
  exact add_one_le_of_lt h

theorem USize.add_one_sub_add_ge_of_mid_lt_of_ge
    {a b c d : USize}
    (h1 : a + b - a ≥ c)
    (h2 : b < d)
    : a + b - a + 1 ≥ c := by
  exact Fin.add_one_sub_add_ge_of_mid_lt_of_ge h1 h2

theorem USize.add_one_ge_of_lt_of_ge
    {a b c : USize}
    (h1 : a ≥ b)
    (h2 : a < c)
    : a + 1 ≥ b := by
  exact Fin.add_one_ge_of_lt_of_ge h1 h2

theorem USize.sub_add_lt_of_and_lt_lt
    {a b c d : USize}
    (h1 : b ≥ c)
    (h2 : a < c ∧ b < d)
    : a + b - c < d := by
  exact Fin.sub_add_lt_of_and_lt_lt h1 h2

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i chunkSize : USize}

theorem idk1
    (i_lt_high : i < high)
    (ptr₁_le_mid : ptr₁ ≤ mid)
    (ptr₂_ge_mid : ptr₂ ≥ mid)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (arr_size_lt_usize_size : arr.size < USize.size)
    (high_le_size : high ≤ arr.usize)
    : ptr₁.toNat < arr.size := by
  have ptr₁_lt_size : ptr₁ < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  exact (USize.lt_ofNat_iff arr_size_lt_usize_size).mp ptr₁_lt_size

def List.ascendingSlice
    {α}
    (lst : List α)
    (le : α → α → Bool)
    (low high : Nat)
    : Prop :=
  ∀ i j : Nat,
    (adjacent : i + 1 = j) →
      (inbounds : low ≤ i ∧ j < high ∧ high ≤ lst.length) →
        le lst[i] lst[j]

def List.ascendingSlice_all
    {α}
    (lst : List α)
    (le : α → α → Bool)
    (low high : Nat)
    : Prop :=
  ∀ i j : Nat,
    (i_lt_j : i < j) →
      (inbounds : low ≤ i ∧ j < high ∧ high ≤ lst.length) →
        le lst[i] lst[j]

theorem List.ascendingSlice_all_of_ascendingSlice
    {α}
    (lst : List α)
    (le : α → α → Bool)
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (low high : Nat)
    (h : lst.ascendingSlice le low high)
    : lst.ascendingSlice_all le low high := by
  unfold List.ascendingSlice_all
  intro i j i_lt_j inbounds
  let rec loop
      (k : Nat)
      (k_inbounds : k > i ∧ k < j)
      (ih : le lst[i] lst[k])
      : le lst[i] lst[j] := by
    if adjacent : k + 1 = j then
      simp only [← adjacent]
      have : le lst[k] lst[k + 1] := h k (k + 1) rfl (by omega)
      exact trans lst[i] lst[k] lst[k + 1] ih this
    else
      refine loop (k + 1) (by omega) ?ih
      have : le lst[k] lst[k + 1] := h k (k + 1) rfl (by omega)
      exact trans lst[i] lst[k] lst[k + 1] ih this
  termination_by j - k
  if j_eq_i_add_one : j = i + 1 then
    simp only [j_eq_i_add_one]
    exact h i (i + 1) rfl (by omega)
  else
    exact loop (i + 1) (by omega) (h i (i + 1) rfl (by omega))

def List.ascending
    {α}
    (lst : List α)
    (le : α → α → Bool)
    : Prop :=
  ascendingSlice lst le 0 lst.length

def Array.ascendingSlice
    {α}
    (arr : Array α)
    (le : α → α → Bool)
    (low high : Nat)
    : Prop :=
  ∀ i j : Nat,
    (adjacent : i + 1 = j) →
      (inbounds : low ≤ i ∧ j < high ∧ high ≤ arr.size) →
        le arr[i] arr[j]

def Array.ascending
    {α}
    (arr : Array α)
    (le : α → α → Bool)
    : Prop :=
  ascendingSlice arr le 0 arr.size

theorem Array.ascending_of_empty {α} (le : α → α → Bool) : (#[] : Array α).ascending le := by
  unfold Array.ascending Array.ascendingSlice
  intro i j adjacent inbounds
  have : j < 0 := inbounds.right.left
  contradiction

theorem Array.ascending_of_singleton {α} (a : α) (le : α → α → Bool) : #[a].ascending le := by
  unfold Array.ascending Array.ascendingSlice
  intro i j adjacent inbounds
  have j_eq_zero : j = 0 := by
    simp only [Nat.zero_le, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.lt_one_iff, Nat.le_refl, and_true, true_and] at inbounds
    exact inbounds
  have : i + 1 = 0 := by
    rw [j_eq_zero] at adjacent
    exact adjacent
  contradiction

namespace MergeSort.Internal

variable
  {le : α → α → Bool}

attribute [local instance] boolRelToRel

theorem List.toArray_ascending_of_ascending
    (l : List α)
    (h : l.ascending le)
    : l.toArray.ascending le := by
  unfold Array.ascending Array.ascendingSlice
  unfold List.ascending List.ascendingSlice at h
  intro i j adjacent inbounds
  exact h i j adjacent inbounds

theorem Array.toList_ascending_of_ascending
    (arr : Array α)
    (h : arr.ascending le)
    : arr.toList.ascending le := by
  unfold List.ascending List.ascendingSlice
  unfold Array.ascending Array.ascendingSlice at h
  intro i j adjacent inbounds
  exact h i j adjacent inbounds

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

theorem ascending_le_of_pairwise_le
    {lst : List α}
    (h : lst.Pairwise le)
    : lst.ascending le := by
  unfold List.ascending List.ascendingSlice
  intro i j adjacent inbounds
  induction h generalizing i j
  case nil =>
    have : j < 0 := inbounds.right.left
    contradiction
  case cons a' b' ih =>
    rename_i a l
    by_cases i_eq_zero : i = 0
    . simp only [i_eq_zero, List.getElem_cons_zero]
      refine a' (a :: l)[j] ?_
      exact List.getElem_cons_mem a l j (by omega) (by omega)
    . have rhs_eq := List.getElem_cons_succ a l i (by omega)
      simp only [adjacent] at rhs_eq
      rw [rhs_eq]
      have lhs_eq := List.getElem_cons_succ a l (i - 1) (by omega)
      have i_pred_succ_eq_i : i - 1 + 1 = i := by omega
      simp only [i_pred_succ_eq_i] at lhs_eq
      rw [lhs_eq]
      refine ih (i - 1) i i_pred_succ_eq_i ?_
      have := inbounds.right.left
      simp only [← adjacent, List.length_cons, Nat.add_lt_add_iff_right] at this
      simp only [Nat.zero_le, this, Nat.le_refl, and_self]

theorem toArray_ascending_of_pairwise_le
    {lst : List α}
    (h : lst.Pairwise le)
    : lst.toArray.ascending le := by
  refine List.toArray_ascending_of_ascending lst ?_
  exact ascending_le_of_pairwise_le h

theorem le_head_of_ascending_of_mem_tail
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (head a : α)
    (tail : List α)
    (a_mem_tail : a ∈ tail)
    (h : (head :: tail).ascending le)
    : le head a = true := by
  have h_all := List.ascendingSlice_all_of_ascendingSlice (head :: tail) le trans 0 (head :: tail).length h
  unfold List.ascendingSlice_all at h_all
  have ⟨a_index, tail_get_eq_a⟩ := List.get_of_mem a_mem_tail
  have h := h_all 0 (a_index + 1) (Nat.zero_lt_succ a_index) ?inbounds
  case inbounds =>
    simp only [Nat.le_refl, List.length_cons, Nat.add_lt_add_iff_right, Fin.is_lt, and_self]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  have getElem_eq_get : tail[(↑a_index : Nat)] = tail.get a_index := rfl
  rwa [getElem_eq_get, tail_get_eq_a] at h

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
      intro i j adjacent inbounds
      have i_plus_one_eq_j' : i + 1 + 1 = j + 1 := by omega
      have : 0 ≤ i + 1 ∧ j + 1 < (head :: tail).length := by
        simp only [Nat.le_add_left, List.length_cons, Nat.add_lt_add_iff_right, true_and]
        exact inbounds.right.left
      have le_head_cons_tail := h (i + 1) (j + 1) i_plus_one_eq_j' (by omega)
      have left_eq := List.getElem_cons_succ head tail i (by omega)
      have right_eq := List.getElem_cons_succ head tail j (by omega)
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
