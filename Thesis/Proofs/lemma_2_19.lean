import Thesis.Definitions.While
import Thesis.Definitions.StructuralSemantics

open While
open StructuralSemantics

/--
Lemma 2.19 (Decomposition of sequential derivations):
Proof from: [Semantics with Applications: An Appetizer]
Proof: The proof is by induction on the number k;
that is, by induction on the
length of the derivation sequence
⟨S₁; S₂, s⟩ ⇒ᵏ s''

If k = 0, then the result holds vacuously
(because ⟨S₁; S₂, s⟩ and s'' are different).

For the induction step,
we assume that the
lemma hold for k ≤ k₀,
and we shall prove it for k₀ + 1.
So assume that
⟨S₁; S₂, s⟩ ⇒ᵏ⁰⁺¹ s''
This mean that the derivation
sequence can be written as
⟨S₁; S₂, s⟩ ⇒ γ ⇒ᵏ⁰ s''
for some configuration γ.

Now one of two cases applies
depending on which of the two
rules [compₛₒₛ¹] and [compₛₒₛ²]
is used.

In the first case, where [compₛₒₛ¹] is used, we have
γ = ⟨S₁'; S₂, s'⟩ and
⟨S₁; S₂, s⟩ ⇒ ⟨S₁'; S₂, s'⟩
because
⟨S₁, s⟩ ⇒ ⟨S₁', s'⟩
We therefore have
⟨S₁'; S₂, s'⟩ ⇒ᵏ⁰ s''
and the induction hypothesis can be applied to this derivation sequence because it
is shorter than the one with which we started.
This means that there is a state s₀ and natural numbers k₁ and k₂ such that
⟨S₁', s'⟩ ⇒ᵏ¹ s₀ and ⟨S₂, s₀⟩ ⇒ᵏ² s''
where k₁ + k₂ = k₀.

Using that
⟨S₁, s⟩ ⇒ ⟨S₁', s'⟩ and ⟨S₁', s'⟩ ⇒ᵏ¹ s₀
we get
⟨S₁, s⟩ ⇒ᵏ¹⁺¹ s_0
We have already seen that
⟨S₂, s₀⟩ ⇒ᵏ² s'',
and since
(k₁ + 1) + k₂ = k₀ + 1
we have proved the required result.

The second possibility is that [compₛₒₛ²]
has been used to obtain the derivation
⟨S₁; S₂, s⟩ ⇒ γ
Then we have
⟨S₁, s⟩ ⇒ s'
and γ is ⟨S₂, s'⟩ so that
⟨S₂, s'⟩ ⇒ᵏ⁰ s''
The result now follows by choosing k₁ = 1 and k₂ = k₀.




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
        exists s₀, k₁ + 1, k₂

        and_intros
        · exact small_step_k.step
                progress hk₁
        · exact hk₂
        · linarith [h_sum]

      | @comp2 _ _ _ s' terminates =>

        -- `exists` instantiates the existential goal (∃ s' k₁ k₂).
        exists s', 1, k₀

        and_intros
        · exact small_step_k.step
            terminates
            small_step_k.refl
        · exact h_rest
        · linarith

lemma lemma_2_19_verbatim_strong {S₁ S₂ : Stmt} {s s'' : State} {k : Nat}
    (h : ⟨S₁; S₂, s⟩ →ₛₒₛ[k] s'') :
    ∃ s₀ k₁ k₂,
    ⟨S₁, s⟩  →ₛₒₛ[k₁] s₀  ∧
    ⟨S₂, s₀⟩ →ₛₒₛ[k₂] s'' ∧
    k = k₁ + k₂ := by
  -- The proof is by induction on the number k;
  -- that is, by induction on the length of the derivation sequence
  induction k using Nat.strongRecOn generalizing s S₁ with
  | ind k ih =>
    -- If k = 0, then the result holds vacuously
    -- (because ⟨S₁; S₂, s⟩ and s'' are different).
    by_cases hk : k = 0
    · subst hk
      cases h

    -- For the induction step, we assume that
    -- the lemma holds for k ≤ k₀,
    -- and we shall prove it for k₀ + 1.
    -- So assume that ⟨S₁; S₂, s⟩ ⇒ᵏ⁰⁺¹ s''
    · have hk_succ : ∃ k₀, k = k₀ + 1 :=
        Nat.exists_eq_succ_of_ne_zero hk

      cases hk_succ with
      | intro k₀ hk_eq =>
        subst hk_eq
        -- This mean that the derivation sequence can be written as
        -- ⟨S₁; S₂, s⟩ ⇒ γ ⇒ᵏ⁰ s'' for some configuration γ.
        cases h with
        | step h_step h_rest =>

          -- Now one of two cases applies depending on which of the two
          -- rules [comp_sos¹] and [comp_sos²] is used.
          cases h_step with
          | comp1 progress =>
            -- In the first case, where [comp_sos¹] is used, we have
            -- γ = ⟨S₁'; S₂, s'⟩ and ⟨S₁; S₂, s⟩ ⇒ ⟨S₁'; S₂, s'⟩ because ⟨S₁, s⟩ ⇒ ⟨S₁', s'⟩.
            -- We therefore have ⟨S₁'; S₂, s'⟩ ⇒ᵏ⁰ s''

            -- and the induction hypothesis can be applied to this derivation sequence
            -- because it is shorter than the one with which we started.
            have
              h_lt : k₀ < k₀ + 1 :=
              Nat.lt_succ_self k₀
            specialize ih k₀
              h_lt h_rest

            -- This means that there is a state s₀ and natural numbers k₁ and k₂ such that
            -- ⟨S₁', s'⟩ ⇒ᵏ¹ s₀ and ⟨S₂, s₀⟩ ⇒ᵏ² s'' where k₁ + k₂ = k₀.
            -- (Unpacking the existential components manually without rcases)
            cases ih with
            | intro s₀ h_exists1 =>
            cases h_exists1 with
            | intro k₁ h_exists2 =>
            cases h_exists2 with
            | intro k₂ h_props =>

            have hk₁ :=
              h_props.left
            have hk₂ :=
              h_props.right.left
            have h_sum :=
              h_props.right.right

            -- Using that ⟨S₁, s⟩ ⇒ ⟨S₁', s'⟩ and ⟨S₁', s'⟩ ⇒ᵏ¹ s₀ we get ⟨S₁, s⟩ ⇒ᵏ¹⁺¹ s₀
            have h_S₁_steps : ⟨S₁, s⟩ →ₛₒₛ[k₁ + 1] s₀ :=
              small_step_k.step progress hk₁

            -- We have already seen that ⟨S₂, s₀⟩ ⇒ᵏ² s'',
            -- and since (k₁ + 1) + k₂ = k₀ + 1 we have proved the required result.
            exists s₀, k₁ + 1, k₂

            -- Reconstructing the conjunction bundle manually
            have h_arith : k₀ + 1 = (k₁ + 1) + k₂ := by linarith [h_sum]

            and_intros
            exact h_S₁_steps
            exact hk₂
            exact h_arith

          | @comp2 _ _ _ s' terminates =>
            -- The second possibility is that [comp_sos²] has been used to obtain
            -- the derivation ⟨S₁; S₂, s⟩ ⇒ γ.
            -- Then we have ⟨S₁, s⟩ ⇒ s' and γ is ⟨S₂, s'⟩ so that ⟨S₂, s'⟩ ⇒ᵏ⁰ s''

            -- The result now follows by choosing k₁ = 1 and k₂ = k₀.
            exists s', 1, k₀
            have h_S₁_one_step : ⟨S₁, s⟩ →ₛₒₛ[1] s' :=
              small_step_k.step terminates small_step_k.refl

            have h_arith_simple : k₀ + 1 = 1 + k₀ := by linarith

            and_intros
            exact h_S₁_one_step
            exact h_rest
            exact h_arith_simple
