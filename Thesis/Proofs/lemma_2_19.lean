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
lemma seq_split {S₁ S₂ : Stmt} {s s'' : State} {k : Nat}
    (h : ⟨S₁; S₂, s⟩ →ₛₒₛ[k] s'') :
    ∃ s' k₁ k₂, ⟨S₁, s⟩ →ₛₒₛ[k₁] s' ∧ ⟨S₂, s'⟩ →ₛₒₛ[k₂] s'' ∧ k = k₁ + k₂ := by
  -- Proof by induction on the number k (length of the derivation sequence).
  induction k generalizing s S₁ with
  | zero =>
    -- Base case k = 0: impossible for a starting configuration ⟨S₁; S₂, s⟩
    cases h
  | succ k₀ ih =>
    -- Inductive step: assume the statement for k₀, prove for k₀ + 1.
    -- The derivation can be written as a first small-step to some configuration γ,
    -- followed by k₀ further steps to s''.
    cases h with
    | step gamma_step h_tail =>
      -- gamma_step : small_step (composition S₁ S₂) s γ  (the first step)
      -- h_tail     : small_step_k γ k₀ (Config.final s'')
      -- Now inspect which rule produced that first step: [comp1] or [comp2].
      cases gamma_step with
      | comp1 progress =>
        -- [comp1]: γ = ⟨S₁'; S₂, s'⟩ because
        -- progress : ⟨S₁, s⟩ →ₛₒₛ ⟨S₁', s'⟩.
        -- We therefore have ⟨S₁'; S₂, s'⟩ →ₛₒₛ[k₀] s'', so apply IH to that shorter derivation.
        specialize ih h_tail
        let ⟨s₀, k₁, k₂, hk₁, hk₂, h_sum⟩ := ih

        -- From progress : ⟨S₁, s⟩ →ₛₒₛ ⟨S₁', s'⟩ and hk₁ : ⟨S₁', s'⟩ →ₛₒₛ[k₁] s₀
        -- we obtain ⟨S₁, s⟩ →ₛₒₛ[k₁ + 1] s₀.
        exists s₀, k₁ + 1, k₂
        constructor
        case left =>
          exact small_step_k.step progress hk₁
        case right =>
          constructor
          case left => exact hk₂
          case right =>
            -- arithmetic: (k₁ + 1) + k₂ = k₀ + 1
            simp [h_sum]
            linarith

      | comp2 terminates =>
        -- [comp2]: the first step returns γ = ⟨S₂, s'⟩ because
        -- terminates : ⟨S₁, s⟩ →ₛₒₛ s'. We have ⟨S₂, s'⟩ →ₛₒₛ[k₀] s''.
        -- Choose k₁ = 1 and k₂ = k₀.
        rename_i s'
        exists s', 1, k₀
        constructor
        case left =>
          exact small_step_k.step terminates small_step_k.refl
        case right =>
          constructor
          case left => exact h_tail
          case right => linarith
