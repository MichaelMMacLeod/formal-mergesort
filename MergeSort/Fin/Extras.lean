theorem Fin.add_one_le_of_lt {a b : Fin (2 ^ System.Platform.numBits)} (h : a < b) : a + 1 ≤ b := by
  cases System.Platform.numBits_eq
  case inl hs | inr hs =>
    revert a b h
    rw [hs]
    intro a b h
    simp only [Nat.reducePow] at a b
    show a + 1 ≤ b
    omega

theorem Fin.add_one_sub_add_ge_of_mid_lt_of_ge_32
    {a b c d : Fin 4294967296}
    (h1 : a + b - a ≥ c)
    (h2 : b < d)
    : a + b - a + 1 ≥ c := by
  omega

theorem Fin.add_one_sub_add_ge_of_mid_lt_of_ge_64
    {a b c d : Fin 18446744073709551616}
    (h1 : a + b - a ≥ c)
    (h2 : b < d)
    : a + b - a + 1 ≥ c := by
  omega

theorem Fin.add_one_sub_add_ge_of_mid_lt_of_ge
    {a b c d : Fin (2 ^ System.Platform.numBits)}
    (h1 : a + b - a ≥ c)
    (h2 : b < d)
    : a + b - a + 1 ≥ c := by
  cases System.Platform.numBits_eq
  case inl h =>
    revert a b c d h1 h2
    rw [h]
    intro a b c d h1 h2
    exact add_one_sub_add_ge_of_mid_lt_of_ge_32 h1 h2
  case inr h =>
    revert a b c d h1 h2
    rw [h]
    intro a b c d h1 h2
    exact add_one_sub_add_ge_of_mid_lt_of_ge_64 h1 h2

def Fin.add_one_ge_of_lt_of_ge_32
    {a b c : Fin 4294967296}
    (h1 : a ≥ b)
    (h2 : a < c)
    : a + 1 ≥ b := by
  omega

def Fin.add_one_ge_of_lt_of_ge_64
    {a b c : Fin 18446744073709551616}
    (h1 : a ≥ b)
    (h2 : a < c)
    : a + 1 ≥ b := by
  omega

def Fin.add_one_ge_of_lt_of_ge
    {a b c : Fin (2 ^ System.Platform.numBits)}
    (h1 : a ≥ b)
    (h2 : a < c)
    : a + 1 ≥ b := by
  cases System.Platform.numBits_eq
  case inl h =>
    revert a b c h1 h2
    rw [h]
    intro a b c h1 h2
    exact add_one_ge_of_lt_of_ge_32 h1 h2
  case inr h =>
    revert a b c h1 h2
    rw [h]
    intro a b c h1 h2
    exact add_one_ge_of_lt_of_ge_64 h1 h2
