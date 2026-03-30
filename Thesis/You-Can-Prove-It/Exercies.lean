import Mathlib.Data.Set.Basic

inductive Person where
  -- left blank

def is_scrub (p : Person) : Bool := sorry

def tlc_members : Set Person := sorry

def can_get_love_from (p1 p2 : Person) : Bool := sorry

def no_scrubs : Prop :=
  ∀ p t, t ∈ tlc_members ∧ is_scrub p → ¬ can_get_love_from t p
