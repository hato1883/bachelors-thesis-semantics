
import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics

open While
open NaturalSemantics

/--
  Semantic equivalence of while-loop and its one-step unrolling.

  Proof strategy (cf. literature):
  - The proof is bidirectional (iff):
    1. If ⟨while b do S, s⟩ →ₙₛ s', then ⟨if b then (S; while b do S) else skip, s⟩ →ₙₛ s'.
    2. If ⟨if b then (S; while b do S) else skip, s⟩ →ₙₛ s', then ⟨while b do S, s⟩ →ₙₛ s'.
  - In Lean, we must explicitly invert the derivation trees (using `cases`) where the textbook says "the derivation tree has one of two forms...".
  - The first explicit Lean-only inversion is marked below.

  Naming scheme:
  - `h...`  : hypothesis/proof term (e.g. `h_cond_true`, `h_deriv_while_true`, `h_deriv_seq_right`).
  - `h_deriv..._alt` : alternative derivation in the direction.
  - `s...`  : states (e.g. `s`, `s'`, `s_mid`).
-/
theorem while_expand (b : Bexp) (S : Stmt) (s s'' : State) :
  (⟨while b then S, s⟩ →ₙₛ s'') →
  (⟨if b then (S; while b then S) else Stmt.skip, s⟩ →ₙₛ s'') := by
  intro h_while
  cases h_while with

  | while_true
    h_cond_true h_deriv_seq_left h_while_rest =>
    have h_comp :
      (⟨S; while b then S, s⟩ →ₙₛ s'') :=
      big_step.comp h_deriv_seq_left h_while_rest
    exact big_step.if_true
      h_cond_true -- Condition
      h_comp      -- Then case

  -- Invert while statement to
  -- access condition
  | while_false
    h_cond_false =>

    -- build skip statement
    have skip_stmt :
      (⟨Stmt.skip, s⟩ →ₙₛ s) :=
      -- Use axiom
      big_step.skip

    exact big_step.if_false
      h_cond_false -- Condition
      skip_stmt    -- Else case

theorem if_compact (b : Bexp) (S : Stmt) (s s'' : State) :
  (⟨if b then (S; while b then S) else Stmt.skip, s⟩ →ₙₛ s'') →
  (⟨while b then S, s⟩ →ₙₛ s'') := by
  intro h_if
  show ⟨while b then S,s⟩ →ₙₛ s''


  cases h_if with

  | if_true
    h_cond_true
    h_deriv_seq =>
    -- Deconstruct the composition derivation into its two parts.
    cases h_deriv_seq with
    | comp
      h_deriv_seq_left
      h_deriv_seq_right =>
      -- Build the `while` derivation from the condition and the two sub-derivations.
      exact big_step.while_true
        h_cond_true
        h_deriv_seq_left
        h_deriv_seq_right

  | if_false
    h_cond_false
    h_deriv_skip =>
    -- The `else` branch is `skip`; invert that derivation and produce `while_false`.
    cases h_deriv_skip
    exact big_step.while_false h_cond_false

lemma lemma_2_5 (b : Bexp) (S : Stmt) (s s'' : State) :
(⟨if b then (S; while b then S) else Stmt.skip, s⟩ →ₙₛ s'')  ↔
(⟨while b then S, s⟩ →ₙₛ s'') := by
  -- equivalence introduction
  apply Iff.intro

  -- Forward direction: if => while
  case mp =>
    -- Reusing our previous proof for if => while
    exact if_compact b S s s''

  -- Backward direction: while => if
  case mpr =>
    -- Reusing our previous proof for while => if
    exact while_expand b S s s''
