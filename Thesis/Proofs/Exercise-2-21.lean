import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics
import Thesis.Definitions.StructuralSemantics

open While
open NaturalSemantics
open StructuralSemantics

section Exercise_2_21



/-!
Exercise 2.21 (Essential)
Prove that if `⟨S₁, s⟩ →ₛₒₛ[k] s'` then `⟨S₁; S₂, s⟩ →ₛₒₛ[k] ⟨S₂, s'⟩`.
The execution of `S₁` is not influenced by the statement following it.
-/
lemma seq_exec_preserve_right {S₁ S₂ : Stmt} {s s' : State} {k : Nat}
  (h : ⟨S₁, s⟩ →ₛₒₛ[k] s') :
  ⟨Stmt.sequence S₁ S₂, s⟩ →ₛₒₛ[k] ⟨S₂, s'⟩ := by
  -- Induction on the length `k` of the derivation sequence.
  induction k generalizing s S₁ S₂ with
  | zero =>
    -- No rule derives `⟨S, s⟩ →ₛₒₛ[0] s'` when the left-hand side is a `Config.step`.
    cases h
  | succ k ih =>
    -- The derivation has at least one step: ⟨S₁, s⟩ →ₛₒₛ γ →ₛₒₛ[k] s'.
    cases h with
    | step h_step h_rest =>
      -- Analyze which small-step rule produced the first step of `S₁`.
      cases h_step with
      | ass =>
        -- assignment: S₁ → final s₁, so h_rest must be `refl` and we can use `comp2`.
        cases h_rest
        exact small_step_k.step (small_step.comp2 (small_step.ass : _)) small_step_k.refl

      | skip =>
        -- S₁ = skip, similar to assignment.
        cases h_rest
        exact small_step_k.step (small_step.comp2 (small_step.skip : _)) small_step_k.refl

      | comp1 hS =>
        -- S₁ → ⟨S₁', s'⟩, use comp1 then apply IH to the remainder.
        cases h_rest
        specialize ih h_rest
        exact small_step_k.step (small_step.comp1 hS) ih

      | comp2 hS =>
        -- S₁ → final s₁ (via comp2), so remainder must be `refl`.
        cases h_rest
        exact small_step_k.step (small_step.comp2 hS) small_step_k.refl

      | if_true hb =>
        specialize ih h_rest
        exact small_step_k.step (small_step.comp1 (small_step.if_true hb)) ih

      | if_false hb =>
        specialize ih h_rest
        exact small_step_k.step (small_step.comp1 (small_step.if_false hb)) ih

      | while_unroll =>
        specialize ih h_rest
        exact small_step_k.step (small_step.comp1 (small_step.while : _)) ih

end Exercise_2_21
