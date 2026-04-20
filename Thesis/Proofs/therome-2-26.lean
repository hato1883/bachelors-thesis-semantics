import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics
import Thesis.Definitions.StructuralSemantics

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

  | seq _ _ ih3 ih4 =>
    apply small_step_star.step
    sorry
    -- stuck:
    -- Missing Exercise 2.21
    -- ih3 : ⟨S₁✝,s✝⟩ →ₛₒₛ* s'✝
    -- ih4 : ⟨S₂✝,s'✝⟩ →ₛₒₛ* s''✝
    -- ⊢ ⟨S₁✝; S₂✝,s✝⟩ →ₛₒₛ ?seq.γ'
    apply ih4

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

  | while_true hcond h1 h2 ih1 ih2 =>
    apply small_step_star.step
    apply small_step.while
    apply small_step_star.step
    apply small_step.if_true
    exact hcond
    sorry
    -- Stuck
    -- Missing Exercise 2.21
    -- ih1 : ⟨S✝,s✝⟩ →ₛₒₛ* s'✝
    -- ih2 : ⟨whileₛ✝ b✝ doₛ✝ S✝,s'✝⟩ →ₛₒₛ* s''✝
    -- ⊢ ⟨S✝; whileₛ✝ b✝ doₛ✝ S✝,s✝⟩ →ₛₒₛ* s''✝

  | while_false hcond =>
    apply small_step_star.step
    apply small_step.while
    apply small_step_star.step
    apply small_step.if_false
    exact hcond
    apply small_step_star.step
    apply small_step.skip
    apply small_step_star.refl


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
