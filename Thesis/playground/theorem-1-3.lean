import Mathlib

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

theorem and_elim (p q : Prop) : p ∧ q → p :=
  fun h : p ∧ q =>
  show p from And.left h

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (fun h : p ∧ q =>
  show q ∧ p from And.intro (And.right h) (And.left h))
  (fun h : q ∧ p =>
  show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
  (fun h : p ∨ q =>
    show q ∨ p from Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq))
  (fun h : q ∨ p =>
    show p ∨ q from Or.elim h
      (fun hq : q =>
        show p ∨ q from Or.intro_right p hq)
      (fun hp : p =>
        show p ∨ q from Or.intro_left q hp))


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
  (fun h : (p ∧ q) ∧ r =>
    have hp : p := And.left (And.left h)
    have hq : q := And.right (And.left h)
    have hr : r := And.right h
    show p ∧ q ∧ r from And.intro (hp) (And.intro hq hr))
  (fun h : p ∧ q ∧ r =>
    have hp : p := And.left h
    have hq : q := And.left (And.right h)
    have hr : r := And.right (And.right h)
    show (p ∧ q) ∧ r from And.intro (And.intro hp hq) hr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (fun h : (p ∨ q) ∨ r =>
    show p ∨ q ∨ r from Or.elim h
      (fun hp_q : p ∨ q =>
        show p ∨ q ∨ r from Or.elim hp_q
          (fun hp : p =>
            Or.intro_left (q ∨ r) hp)
          (fun hq : q =>
            Or.intro_right p (Or.intro_left r hq)))
      (fun hr : r =>
        Or.intro_right p (Or.intro_right q hr)))
  (fun h : p ∨ q ∨ r =>
    show (p ∨ q) ∨ r from Or.elim h
      (fun hp : p =>
        Or.intro_left r (Or.intro_left q hp))
      (fun hq_r : q ∨ r =>
        show (p ∨ q) ∨ r from Or.elim hq_r
          (fun hq : q =>
            Or.intro_left r (Or.intro_right p hq))
          (fun hr : r =>
            Or.intro_right (p ∨ q) hr)))


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  case mp =>
    intro p_or_q__or_r
    cases p_or_q__or_r with
    | inl p_or_q =>
      cases p_or_q with
      | inl h_p => left; exact h_p
      | inr h_q => right; left; exact h_q
    | inr h_r => right; right; exact h_r
  case mpr =>
    intro p_or__q_or_r
    cases p_or__q_or_r with
    | inl h_p => left; left; exact h_p
    | inr q_or_r =>
      cases q_or_r with
        | inl h_q => left; right; exact h_q
        | inr h_r => right; exact h_r


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  by grind

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
