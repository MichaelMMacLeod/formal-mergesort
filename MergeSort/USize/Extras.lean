import MergeSort.Fin.Extras
import Std.Tactic.BVDecide

abbrev USize.succ (n : USize) := n + 1

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

def USize.add_sub_add_one_le_of_lt
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

def USize.add_one_ge_of_lt_of_ge
    {a b c : USize}
    (h1 : a ≥ b)
    (h2 : a < c)
    : a + 1 ≥ b := by
  exact Fin.add_one_ge_of_lt_of_ge h1 h2
