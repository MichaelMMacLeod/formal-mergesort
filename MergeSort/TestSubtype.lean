set_option trace.compiler.ir.result true

structure H (a b : Nat) : Prop where
  eq : a = b

-------------------- Original version

def H.next
    {a b : Nat}
    (h : H a b)
    : H (a - 1) (b - 1) :=
  { eq := by rw [h.eq] }

def versionA (a b : Nat) (h : H a b) : Nat :=
  if a = 0 then
    b
  else
    versionA (a - 1) (b - 1) h.next

-------------------- Version with subtypes

def HB.next
    {a : Nat}
    (hb : Subtype (H a))
    : Subtype (H (a - 1)) :=
  Subtype.mk (hb.val - 1) { eq := by rw [← hb.property.eq] }

def versionB (a : Nat) (hb : Subtype (H a)) : Nat :=
  if a = 0 then
    hb.val
  else
    versionB (a - 1) (HB.next hb)
