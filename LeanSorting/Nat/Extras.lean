import Mathlib.Data.Nat.Defs

def Nat.in_range (n : ℕ) (low high : ℕ) : Prop := n ≥ low ∧ n < high
def Nat.adjacent_in_range (n m low high : ℕ) : Prop := n.succ = m ∧ n ≥ low ∧ m < high
