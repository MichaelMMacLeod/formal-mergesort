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

-- variable
--   {α : Type}
--   {arr aux : Array α}
--   {low mid high ptr₁ ptr₂ i chunkSize : USize}
