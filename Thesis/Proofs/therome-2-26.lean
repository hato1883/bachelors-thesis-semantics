import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics
import Thesis.Definitions.StructuralSemantics
import Thesis.Proofs.Exercise_2_21

open While
open NaturalSemantics
open StructuralSemantics
/-!
  Equivalence between NS (big-step) and SOS (small-step) semantics.

  For any statement `S` and states `s`, `s'`, there is a natural semantics
  derivation `⟨S, s⟩ →ₙₛ s'` iff there is a (multi-step) small-step semantics
  derivation `⟨S, s⟩ →ₛₒₛ* s'.

  Proof strategy:
  - Prove each direction as a separate lemma to keep the main theorem concise:
    * `ns_to_sos` : natural semantics implies multi-step SOS
    * `sos_to_ns` : multi-step SOS implies natural semantics
  - Each lemma below is scaffolded; fill in the case analyses and inductions.
  - Naming:
    - `h...`  : hypothesis/proof term
    - `ih...` : induction hypothesis
    - `s...`  : states
--/
theorem ns_to_sos (S : Stmt) (s s' : State) :
  (⟨S, s⟩ →ₙₛ s') → (⟨S, s⟩ →ₛₒₛ* s') := by
  intro h
  -- Proof outline:
  -- 1. Induction on `h : ⟨S, s⟩ →ₙₛ s'`.
  -- 2. For each constructor of the natural semantics, construct the
  --    corresponding multi-step SOS derivation.
  -- TODO: implement detailed case proofs here.
  induction h with
  | ass =>
    apply small_step_star.step
    apply small_step.ass
    apply small_step_star.refl

  | skip =>
    apply small_step_star.step
    apply small_step.skip
    apply small_step_star.refl

  | comp ih1 ih2 ih3 ih4 =>
    rename_i S₁ S₂ s s' s''
    -- ih1: ⟨S₁, s⟩ →ₛₒₛ* s_mid
    -- ih2: ⟨S₂, s_mid⟩ →ₛₒₛ* s_final

    -- 1. Using your k-step derived lemma: ⟨S₁; S₂, s⟩ →ₛₒₛ* ⟨S₂, s_mid⟩
    let h_first_part := seq_exec_preserve_right_star (S₂ := S₂) ih3

    -- 2. Glue the first part to the second part (ih2)
    exact small_step_star_trans h_first_part ih4

  | if_true hcond h ih =>
    apply small_step_star.step
    apply small_step.if_true
    exact hcond
    exact ih

  | if_false hcond h ih =>
    apply small_step_star.step
    apply small_step.if_false
    exact hcond
    exact ih

  | while_true hcond h1 h2 ih_body ih_loop =>
    rename_i b S₂ s s' s''
    -- 1. Unroll: while b do S₂ →ₛₒₛ if b then (S₂; while b do S₂) else skip
    apply small_step_star.step
    · exact small_step.while_unroll
    -- 2. Condition is true: if b then ... →ₛₒₛ ⟨S₂; while b do S₂, s⟩
    apply small_step_star.step
    · exact small_step.if_true hcond
    -- 3. Use the local S₂ for the suffix of the sequence
    let h_seq := seq_exec_preserve_right_star (S₂ := Stmt.loop b S₂) ih_body
    -- 4. Transitivity: ⟨S₂; while b do S₂, s⟩ →* ⟨while b do S₂, s'⟩ →* s''
    exact small_step_star_trans h_seq ih_loop

  | while_false h_cond =>
    apply small_step_star.step
    · apply small_step.while_unroll
    · apply small_step_star.step
      · apply small_step.if_false
        · exact h_cond
      · apply small_step_star.step
        apply small_step.skip
        · apply small_step_star.refl


theorem sos_to_ns (S : Stmt) (s s' : State) :
  (⟨S, s⟩ →ₛₒₛ* s') → (⟨S, s⟩ →ₙₛ s') := by
  intro h
  -- Proof outline:
  -- 1. Induction on the SOS multi-step derivation `h`.
  -- 2. Reconstruct the natural semantics derivation from the sequence of steps.
  -- TODO: implement detailed case proofs here.
  cases h
  sorry

theorem ns_equvivlent_sos (S : Stmt) (s s' : State) :
  (⟨S, s⟩ →ₙₛ s') ↔ (⟨ S, s⟩ →ₛₒₛ* s') := by
  apply Iff.intro
  case mp => exact ns_to_sos S s s'
  case mpr => exact sos_to_ns S s s'
