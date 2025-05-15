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
    . simp [i_eq_zero]
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

theorem pairwise_le_iff_ascending_of_le
    {lst : List α}
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), le a b || le b a)
    : lst.Pairwise le ↔ lst.toArray.ascending le := by
  apply Iff.intro
  case mp => exact toArray_ascending_of_pairwise_le
  case mpr => sorry

end MergeSort.Internal

#check List.sorted_mergeSort

    -- (irreflexive : ∀ a : α, ¬lt a a)
    -- (asymmetric : ∀ a b : α, lt a b → ¬lt b a)
    -- (transitive : ∀ a b c : α, lt a b → lt b c → lt a c)
