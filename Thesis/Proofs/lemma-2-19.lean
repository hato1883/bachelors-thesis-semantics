import Thesis.Definitions.While
import Thesis.Definitions.StructuralSemantics

open While
open StructuralSemantics

/--
Lemma 2.19 (Decomposition of sequential derivations):
If ⟨S₁ ; S₂, s⟩ ⇒ᵏ s'', then there exists a state s' and natural numbers k₁ and k₂ such that
⟨S₁, s⟩ ⇒ᵏ¹ s' and ⟨S₂, s'⟩ ⇒ᵏ² s'' and k = k₁ + k₂.

Strategy alignment with literature:
- Textbook proof uses induction on the length of the derivation sequence (k).
- In Lean, we use induction on k, analyzing the first step of the derivation.

Naming scheme used in this file:
- `h...`  : hypothesis/proof term (examples: ...).
- `ih...` : induction hypothesis supplied by `induction` (examples: ...).
- `s...`  : states (examples: ...).
- `hDerivAlt` : the second derivation provided after `intro`.
--/
lemma seq_split {S₁ S₂ : Stmt} {s s'' : State} {k : Nat}
    (h : ⟨S₁; S₂, s⟩ →ₛₒₛ[k] s'') :
    ∃ s' k₁ k₂, ⟨S₁, s⟩ →ₛₒₛ[k₁] s' ∧ ⟨S₂, s'⟩ →ₛₒₛ[k₂] s'' ∧ k = k₁ + k₂ := by
  -- Proof by induction on the number k
  induction k generalizing s S₁ with
  | zero =>
    -- If k = 0, the result holds vacuously (no rule for ⟨S₁; S₂, s⟩ →ₛₒₛ[0] s'')
    cases h
  | succ k₀ ih =>
    -- Assume the lemma holds for k₀, prove for k₀ + 1
    -- This means the derivation sequence is ⟨S₁; S₂, s⟩ ⇒ γ ⇒k₀ s''
    cases h with
    | step h_step h_rest =>
      -- Branch on which rule was used: [comp1_sos] or [comp2_sos]
      cases h_step with
      | comp1 hS₁ =>
        -- Case 1: γ = ⟨S₁'; S₂, s'⟩ and ⟨S₁, s⟩ ⇒ ⟨S₁', s'⟩
        -- Apply the induction hypothesis to the shorter sequence ⟨S₁'; S₂, s'⟩ ⇒k₀ s''
        specialize ih h_rest

        -- Deconstruct the induction hypothesis
        -- into 3 separate parts sharing the same state and k₁ k₂ values
        let ⟨s₀, k₁, k₂, hk₁, hk₂, h_sum⟩ := ih

        -- We have ⟨S₁, s⟩ ⇒ ⟨S₁', s'⟩ and ⟨S₁', s'⟩ ⇒k₁ s₀, so ⟨S₁, s⟩ ⇒k₁+1 s₀
        exists s₀, k₁ + 1, k₂
        constructor
        · exact small_step_k.step hS₁ hk₁
        constructor
        · exact hk₂
        · -- Since (k₁ + 1) + k₂ = k₀ + 1
          simp [h_sum]
          linarith

      | comp2 hS₁ =>
        -- Case 2: ⟨S₁, s⟩ ⇒ s' and γ = ⟨S₂, s'⟩
        -- We have ⟨S₂, s'⟩ ⇒k₀ s''
        -- Choosing k₁ = 1 and k₂ = k₀
        rename_i s'
        exists s', 1, k₀
        constructor
        · -- ⟨S₁, s⟩ ⇒₁ s'
          exact small_step_k.step hS₁ small_step_k.refl
        constructor
        · exact h_rest
        · linarith
