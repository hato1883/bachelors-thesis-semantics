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
  ⟨S₁ ; S₂, s⟩ →ₛₒₛ[k] ⟨S₂, s'⟩ := by
  induction k generalizing s S₁ with
  | zero =>
    -- ⟨S₁, s⟩ →ₛₒₛ[0] s' is impossible because Step ≠ Final
    cases h
  | succ k ih =>
    -- We have ⟨S₁, s⟩ →ₛₒₛ γ' →ₛₒₛ[k] s'
    cases h with
    | step h_step h_rest =>
      rename_i γ'
      -- Now we branch on whether γ' is a final state or a continuing step
      cases γ' with
      | final s_next =>
        -- Case 1: S₁ finishes in one step (γ' = s_next)
        -- This matches the [comp2] rule: ⟨S₁; S₂, s⟩ →ₛₒₛ ⟨S₂, s_next⟩
        -- Since h_rest is ⟨s_next, ...⟩ →ₛₒₛ[k] s', and s_next is final,
        -- k must be 0 and s_next = s'.
        cases h_rest
        exact small_step_k.step (small_step.comp2 h_step) small_step_k.refl
      | step S_next s_next =>
        -- Case 2: S₁ takes one step to a new configuration ⟨S_next, s_next⟩
        -- This matches the [comp1] rule: ⟨S₁; S₂, s⟩ →ₛₒₛ ⟨S_next; S₂, s_next⟩
        apply small_step_k.step
        · exact small_step.comp1 h_step
        · -- Now we need: ⟨S_next; S₂, s_next⟩ →ₛₒₛ[k] ⟨S₂, s'⟩
          -- This is exactly our IH applied to the remaining steps h_rest
          exact ih h_rest

end Exercise_2_21
