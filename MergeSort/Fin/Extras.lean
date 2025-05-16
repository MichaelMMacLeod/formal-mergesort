import Lean.LocalContext
import Lean.Elab.Tactic
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Revert

syntax "revert_all_except" ident : tactic
elab "revert_all_except" t:ident : tactic => do
  let mut result := #[]
  for h in (← Lean.getLCtx) do
    if !h.isImplementationDetail ∧ h.userName ≠ t.getId then
      result := result.push <| h.fvarId
  Lean.Elab.Tactic.liftMetaTactic fun mvarid => do
    let (_, mvarid) ← mvarid.revert result
    pure [mvarid]

syntax "solve_numBits_fin_goal" : tactic
macro_rules
| `(tactic| solve_numBits_fin_goal) =>
  `(tactic| {
      cases System.Platform.numBits_eq
      case inl h | inr h =>
        revert_all_except h
        rw [h]
        simp only [Nat.reducePow]
        omega
    })

theorem Fin.add_one_le_of_lt
    {a b : Fin (2 ^ System.Platform.numBits)}
    (h : a < b)
    : a + 1 ≤ b := by solve_numBits_fin_goal

theorem Fin.add_one_sub_add_ge_of_mid_lt_of_ge
    {a b c d : Fin (2 ^ System.Platform.numBits)}
    (h1 : a + b - a ≥ c)
    (h2 : b < d)
    : a + b - a + 1 ≥ c := by solve_numBits_fin_goal

theorem Fin.add_one_ge_of_lt_of_ge
    {a b c : Fin (2 ^ System.Platform.numBits)}
    (h1 : a ≥ b)
    (h2 : a < c)
    : a + 1 ≥ b := by solve_numBits_fin_goal

theorem Fin.sub_add_lt_of_and_lt_lt
    {a b c d : Fin (2 ^ System.Platform.numBits)}
    (h1 : b ≥ c)
    (h2 : a < c ∧ b < d)
    : a + b - c < d := by solve_numBits_fin_goal

theorem Fin.ptr₁_lt_size
    {α : Type}
    {arr : Array α}
    {mid high ptr₁ ptr₂ i arrUsize : Fin (2 ^ System.Platform.numBits)}
    (i_lt_high : i < high)
    (ptr₁_le_mid : ptr₁ ≤ mid)
    (ptr₂_ge_mid : ptr₂ ≥ mid)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (arr_size_lt_usize_size : arr.size < USize.size)
    (high_le_size : high ≤ arrUsize)
    : ptr₁ < arrUsize := by solve_numBits_fin_goal

theorem Fin.succ_eq_succ_add_sub_of_add_sub
    {mid ptr₁ ptr₂ i : Fin (2 ^ System.Platform.numBits)}
    (i_def : i = ptr₁ + ptr₂ - mid)
    : i + 1 = (ptr₁ + 1) + ptr₂ - mid := by solve_numBits_fin_goal

theorem Fin.succ_eq_add_succ_sub_of_add_sub
    {mid ptr₁ ptr₂ i : Fin (2 ^ System.Platform.numBits)}
    (i_def : i = ptr₁ + ptr₂ - mid)
    : i + 1 = ptr₁ + (ptr₂ + 1) - mid := by solve_numBits_fin_goal

theorem Fin.eq_of_not_lt_of_le
    {a b : Fin (2 ^ System.Platform.numBits)}
    (le : a ≤ b)
    (not_lt : ¬a < b)
    : a = b := by omega

theorem Fin.i_lt_arr_usize
    {mid high ptr₁ ptr₂ i arrUSize : Fin (2 ^ System.Platform.numBits)}
    (high_le_size : high ≤ arrUSize)
    (i_le_high : i ≤ high)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high)
    (ptr₁_lt_mid : ptr₁ < mid)
    : i < arrUSize := by solve_numBits_fin_goal

theorem Fin.i_add_one_ge_low
    {low mid high ptr₁ ptr₂ i : Fin (2 ^ System.Platform.numBits)}
    (i_ge_low : i ≥ low)
    (i_le_high : i ≤ high)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high)
    (ptr₁_lt_mid : ptr₁ < mid)
    : i + 1 ≥ low := by solve_numBits_fin_goal
