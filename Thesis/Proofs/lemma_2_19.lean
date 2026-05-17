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
- `h_deriv_alt` : the second derivation provided after `intro`.
--/
lemma lemma_2_19 {S₁ S₂ : Stmt} {s s'' : State} {k : Nat}
    (h : ⟨S₁; S₂, s⟩ →ₛₒₛ[k] s'') :
    ∃ s' k₁ k₂, ⟨S₁, s⟩ →ₛₒₛ[k₁] s' ∧ ⟨S₂, s'⟩ →ₛₒₛ[k₂] s'' ∧ k = k₁ + k₂ := by
  -- `generalizing s S₁` ensures `ih` is quantified over ∀ S₁ s.
  -- This is required because S₁ and s will change (to S₁' and s') in the comp1 step.
  induction k
  using Nat.strongRecOn
  generalizing s S₁ with
  | ind k₀ ih =>
    cases h with
    | @step _ _ _ _ k₀ h_step h_rest =>
      cases h_step with
      | comp1 progress =>
        have h_lt : k₀ < k₀ + 1 := Nat.lt_succ_self k₀
        -- `specialize` instantiates the generic `ih` with our specific smaller step count (k₀),
        -- the strict inequality proof (h_lt), and the remaining derivation (h_rest).
        specialize ih k₀ h_lt h_rest
        have ⟨s₀, k₁, k₂, hk₁, hk₂, h_sum⟩ := ih

        -- `exists` instantiates the existential goal (∃ s' k₁ k₂).
        -- It changes the goal's placeholders to: s₀ (the midpoint from the IH),
        -- k₁ + 1 (the IH steps plus our first progress step), and k₂ (the remaining IH steps).
        exists s₀, k₁ + 1, k₂

        apply And.intro
        case left =>
          apply small_step_k.step
          case step => exact progress
          case rest => exact hk₁
        case right =>
          apply And.intro
          case left => exact hk₂
          case right => linarith [h_sum]
      | @comp2 _ _ _ s' terminates =>

        -- `exists` instantiates the existential goal (∃ s' k₁ k₂).
        -- It changes placeholders to: s' (the state right after S₁ finishes),
        -- 1 (since S₁ took exactly 1 step to terminate), and k₀ (the remaining steps for S₂).
        exists s', 1, k₀

        apply And.intro
        case left =>
          apply small_step_k.step
          case step => exact terminates
          case rest => apply small_step_k.refl
        case right =>
          apply And.intro
          case left => exact h_rest
          case right => linarith
