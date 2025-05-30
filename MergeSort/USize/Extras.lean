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

theorem USize.ptr₁_lt_arr_size
    {α : Type}
    {arr : Array α}
    {mid high ptr₁ ptr₂ i : USize}
    (i_lt_high : i < high)
    (ptr₁_le_mid : ptr₁ ≤ mid)
    (ptr₂_ge_mid : ptr₂ ≥ mid)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (arr_size_lt_usize_size : arr.size < USize.size)
    (high_le_size : high ≤ arr.usize)
    : ptr₁.toNat < arr.size := by
  have ptr₁_lt_size : ptr₁ < arr.usize := by
    exact Fin.ptr₁_lt_size
      i_lt_high
      ptr₁_le_mid
      ptr₂_ge_mid
      (congrArg BitVec.toFin (congrArg toBitVec i_def))
      arr_size_lt_usize_size
      high_le_size
  exact (USize.lt_ofNat_iff arr_size_lt_usize_size).mp ptr₁_lt_size

theorem USize.ptr₂_lt_arr_size
    {α : Type}
    {arr : Array α}
    {high ptr₂ : USize}
    (arr_size_lt_usize_size : arr.size < USize.size)
    (high_le_size : high ≤ arr.usize)
    (ptr₂_lt_high : ptr₂ < high)
    : ptr₂.toNat < arr.size := by
  have ptr₂_lt_size : ptr₂ < arr.usize := by
    exact USize.lt_of_lt_of_le ptr₂_lt_high high_le_size
  exact (USize.lt_ofNat_iff arr_size_lt_usize_size).mp ptr₂_lt_size

theorem USize.i_lt_aux_size
    {α : Type}
    {arr aux : Array α}
    {high i : USize}
    (arr_size_lt_usize_size : arr.size < USize.size)
    (high_le_size : high ≤ arr.usize)
    (size_eq : arr.size = aux.size)
    (i_lt_high : i < high)
    : i.toNat < aux.size := by
  have i_lt_size : i < arr.usize := by
    exact USize.lt_of_lt_of_le i_lt_high high_le_size
  rw [← size_eq]
  exact (USize.lt_ofNat_iff arr_size_lt_usize_size).mp i_lt_size

theorem USize.succ_eq_succ_add_sub_of_add_sub
    {mid ptr₁ ptr₂ i : USize}
    (i_def : i = ptr₁ + ptr₂ - mid)
    : i.succ = ptr₁.succ + ptr₂ - mid := by
  have := Fin.succ_eq_succ_add_sub_of_add_sub
    (congrArg BitVec.toFin (congrArg toBitVec i_def))
  exact USize.eq_of_toFin_eq this

theorem USize.succ_eq_add_succ_sub_of_add_sub
    {mid ptr₁ ptr₂ i : USize}
    (i_def : i = ptr₁ + ptr₂ - mid)
    : i.succ = ptr₁ + ptr₂.succ - mid := by
  have := Fin.succ_eq_add_succ_sub_of_add_sub
    (congrArg BitVec.toFin (congrArg toBitVec i_def))
  exact USize.eq_of_toFin_eq this

theorem USize.eq_of_not_lt_of_le
    {a b : USize}
    (le : a ≤ b)
    (not_lt : ¬a < b)
    : a = b :=
  USize.eq_of_toFin_eq (Fin.eq_of_not_lt_of_le le not_lt)

theorem USize.ptr₁_eq_mid_or_ptr₂_eq_high
    {mid high ptr₁ ptr₂ : USize}
    (ptr₁_le_mid : ptr₁ ≤ mid)
    (ptr₂_le_high : ptr₂ ≤ high)
    (not_ptr₁_ptr₂_in_range : ¬(ptr₁ < mid ∧ ptr₂ < high))
    : ptr₁ = mid ∨ ptr₂ = high := by
  apply (Decidable.not_and_iff_or_not.mp not_ptr₁_ptr₂_in_range).elim
  . intro not_ptr₁_lt_mid
    apply Or.intro_left
    exact USize.eq_of_not_lt_of_le ptr₁_le_mid not_ptr₁_lt_mid
  . intro not_ptr₂_lt_high
    apply Or.intro_right
    exact USize.eq_of_not_lt_of_le ptr₂_le_high not_ptr₂_lt_high

theorem USize.i_lt_arr_usize
    {α : Type}
    {arr : Array α}
    {mid high ptr₁ ptr₂ i : USize}
    (high_le_size : high ≤ arr.usize)
    (i_le_high : i ≤ high)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high)
    (ptr₁_lt_mid : ptr₁ < mid)
    : i < arr.usize :=
  Fin.i_lt_arr_usize high_le_size i_le_high
    (congrArg BitVec.toFin (congrArg toBitVec i_def))
    (Or.imp (congrArg toFin) (congrArg toFin) not_ptr₁_ptr₂_in_range)
    ptr₁_lt_mid

theorem USize.i_succ_ge_low
    {low mid high ptr₁ ptr₂ i : USize}
    (i_ge_low : i ≥ low)
    (i_le_high : i ≤ high)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high)
    (ptr₁_lt_mid : ptr₁ < mid)
    : i.succ ≥ low :=
  Fin.i_add_one_ge_low i_ge_low i_le_high
    (congrArg BitVec.toFin (congrArg toBitVec i_def))
    (Or.imp (congrArg toFin) (congrArg toFin) not_ptr₁_ptr₂_in_range)
    ptr₁_lt_mid

theorem USize.i_succ_le_high
    {mid high ptr₁ ptr₂ i : USize}
    (i_le_high : i ≤ high)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high)
    (ptr₁_lt_mid : ptr₁ < mid)
    : i.succ ≤ high :=
  Fin.i_add_one_le_high i_le_high
    (congrArg BitVec.toFin (congrArg toBitVec i_def))
    (Or.imp (congrArg toFin) (congrArg toFin) not_ptr₁_ptr₂_in_range)
    ptr₁_lt_mid

theorem USize.not_ptr₁_succ_ptr₂_in_range
    {mid high ptr₁ ptr₂ : USize}
    (not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high)
    (ptr₁_lt_mid : ptr₁ < mid)
    : ptr₁ + 1 = mid ∨ ptr₂ = high := by
  have := Fin.not_ptr₁_add_one_ptr₂_in_range
    (Or.imp (congrArg toFin) (congrArg toFin) not_ptr₁_ptr₂_in_range)
    ptr₁_lt_mid
  -- there's got to be a better way to do this
  match this with
  | Or.inl h =>
    have v : ptr₁ + 1 = mid := USize.eq_of_toFin_eq h
    apply Or.intro_left
    exact v
  | Or.inr h =>
    apply Or.intro_right
    apply USize.eq_of_toFin_eq
    exact h

  -- cases System.Platform.numBits_eq
  -- . bv_decide
  -- . bv_decide

--   variable
--     {α : Type}
--     {arr aux : Array α}
--     {low mid high ptr₁ ptr₂ i chunkSize : USize}
