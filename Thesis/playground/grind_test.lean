import Mathlib
-- Or more specifically, if available: import Lean.Meta.Tactic.Grind

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  grind
