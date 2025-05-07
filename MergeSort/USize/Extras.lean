abbrev USize.succ (n : USize) := n + 1

theorem USize.add_one_sub_right_comm
    {a b c : USize}
    : a + b - c + 1 = a + (b + 1) - c := by
  rw [← USize.toNat_inj]
  repeat rw [USize.toNat_add, USize.toNat_sub]
  simp [Nat.add_assoc, Nat.add_comm 1]

def USize.add_sub_self_eq
    {a b : USize}
    : a + b - a = b := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    simp +arith only [← USize.toNat_inj, USize.toNat_sub, USize.toNat_add, Nat.mod_add_mod]
    have toNat_lt_maxVal {n : USize} : n.toNat ≤ 2 ^ System.Platform.numBits :=
      Nat.le_of_succ_le (USize.toNat_lt_two_pow_numBits n)
    rw [← Nat.add_sub_assoc toNat_lt_maxVal, Nat.add_assoc, Nat.add_sub_self_left, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (USize.toNat_lt_two_pow_numBits b)

-- def idk13 (u : USize) (h : u > 0) : u - 1 < u := by
--   cases System.Platform.numBits_eq
--   . bv_decide
--   . bv_decide

-- def idk15 (n m : USize) (h : n < m) : n.toNat < m.toNat := by
--   exact h

-- def idk14 {u : USize} (h : u > 0) : (u - 1).toNat < u.toNat := by
--   apply idk15
--   apply idk13
--   exact h

-- def USize.induction
--     {motive : USize → Sort _}
--     (zero : motive 0)
--     (succ : ∀ u, motive u → motive (u + 1))
--     (u : USize)
--     : motive u := by
--   if h : u = 0 then
--     rw [h]; exact zero
--   else
--     have u_gt_zero : u > 0 := USize.pos_iff_ne_zero.mpr h
--     have v2 := USize.induction (motive := motive) zero succ (u - 1)
--     have v2 := succ (u - 1) v2
--     simp at v2
--     exact v2
-- termination_by u.toNat
-- decreasing_by exact idk14 u_gt_zero
