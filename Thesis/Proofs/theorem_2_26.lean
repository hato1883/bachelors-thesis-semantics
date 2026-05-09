import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics
import Thesis.Definitions.StructuralSemantics
import Thesis.Proofs.exercise_2_21
import Thesis.Proofs.lemma_2_19
import Thesis.Proofs.lemma_2_5

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

  | comp ih1 ih2 h1 h2 =>
    rename_i S₁ S₂ s s' s''
    -- Exercise 2.21
    have h_comp_first_part := exercise_2_21 (S₂ := S₂) h1
    -- Transitivity
    exact small_step_star_trans h_comp_first_part h2

  | if_true h_cond h ih =>
    -- [if_true_sos]
    apply small_step_star.step
    · apply small_step.if_true h_cond
    · exact ih

  | if_false h_cond h ih =>
    -- [if_false_sos]
    apply small_step_star.step
    · apply small_step.if_false h_cond
    · exact ih

  | while_true h_cond h_body h_rest ih_body ih_loop =>
    rename_i b S s s' s''
    -- Exercise 2.21
    have h_after_ex21 := exercise_2_21 (S₂ := Stmt.loop b S) ih_body
    -- while_sos step
    apply small_step_star.step
    · exact small_step.while_unroll
    -- if_sos^tt step
    apply small_step_star.step
    · exact small_step.if_true h_cond
    -- Transitivity
    exact small_step_star_trans h_after_ex21 ih_loop

  | while_false h_cond =>
    -- while_sos step
    apply small_step_star.step
    · exact small_step.while_unroll
    -- if_sos^ff step
    apply small_step_star.step
    · exact small_step.if_false h_cond
    -- skip_sos step + reflexivity
    apply small_step_star.step
    · exact small_step.skip
    · exact small_step_star.refl


lemma sos_k_to_ns (S : Stmt) (s s' : State) (k : Nat) :
  (⟨S, s⟩ →ₛₒₛ[k] s') → (⟨S, s⟩ →ₙₛ s') := by
  -- Use strong induction on k to allow for arbitrary k1, k2 < k
  induction k using Nat.strongRecOn generalizing S s s'
  rename_i n ih
  intro h_k_step
  match n with
    | 0 =>
      -- Case k = 0: Vacuous as per text
      cases h_k_step
    | k₀ + 1 =>
      -- Case k = k0 + 1: This is where we "inspect the first step"
      cases h_k_step with
      | step h_first h_rest =>
        -- h_first: ⟨S, s⟩ →ₛₒₛ next_cfg
        -- h_rest : next_cfg →ₛₒₛ[k0] s'

        -- Now you can perform `cases h_first` to inspect the SOS rule tree
        cases h_first
        case ass x a =>
          -- Text: "The case [ass_sos]: Straightforward (and k0 = 0)"
          cases h_rest -- This must be refl because assignment terminates in 1 step
          apply big_step.ass

        case skip =>
          -- Text: "The case [skip_sos]: Straightforward (and k0 = 0)"
          cases h_rest
          apply big_step.skip

        case comp1 S1 S1' S2 s_next h_step_S1 =>
          -- [Step 1: Apply Lemma 2.19 to split the sequence]
          obtain ⟨s_mid, k₁, k₂, hk1, hk2, h_sum⟩ := seq_split h_rest

          -- [Step 4: Use the [comp_ns] rule to combine results]
          apply big_step.comp (s' := s_mid)
          case h_left =>
            -- [Step 2: Establish the derivation for S1]
            have h_s1_full : ⟨S1, s⟩ →ₛₒₛ[k₁ + 1] s_mid := small_step_k.step h_step_S1 hk1
            -- [Step 3a: Justify that k₁ + 1 is strictly smaller than the total]
            have h_k2_pos : k₂ > 0 := by
              cases k₂
              case zero => cases hk2
              case succ => linarith
            -- [Step 3b: Apply the Induction Hypothesis (IH)]
            apply ih (k₁ + 1) (by linarith) S1 s s_mid h_s1_full

          case h_right =>
            -- [Step 3: Apply the Induction Hypothesis (IH) for S2]
            apply ih k₂ (by linarith) S2 s_mid s' hk2

        case comp2 S1 S2 s_next h_step_s1 =>
          apply big_step.comp (s' := s_next)
          case h_left =>
            -- Unlike comp1, S1 terminates fully in this first step (S1' is skip)
            -- We apply the IH to a 1-step derivation instead of (k₁ + 1)
            have h_lt_one : 1 < k₀ + 1 := by
              cases k₀
              case zero => cases h_rest
              case succ => linarith

            apply ih 1 h_lt_one S1 s s_next
            exact small_step_k.step h_step_s1 small_step_k.refl

          case h_right =>
            -- In comp1, the second part takes k₂ steps; here, it takes the full remaining k₀ steps
            apply ih k₀ (by linarith) S2 s_next s' h_rest

        case if_true b S1 S2 h_cond =>
          -- First step: ⟨if b then S1 else S2, s⟩ → ⟨S1, s⟩
          -- The remaining derivation (h_rest) is ⟨S1, s⟩ →ₛₒₛ[k₀] s'
          apply big_step.if_true h_cond
          -- Since k₀ < k₀ + 1, the IH applies perfectly
          apply ih k₀ (by linarith) S1 s s' h_rest

        case if_false b S1 S2 h_cond =>
          -- First step: ⟨if b then S1 else S2, s⟩ → ⟨S1, s⟩
          -- The remaining derivation (h_rest) is ⟨S1, s⟩ →ₛₒₛ[k₀] s'
          apply big_step.if_false h_cond
          -- Since k₀ < k₀ + 1, the IH applies perfectly
          apply ih k₀ (by linarith) S2 s s' h_rest

        case while_unroll b S_body =>
          -- First step: ⟨while...⟩ → ⟨if b then (S; while...) else skip, s⟩
          -- We apply the IH to the resulting k0 steps starting from the 'if'
          have h_ns_if := ih k₀ (by linarith) _ _ _ h_rest
          -- Then use the bridge: if_ns → while_ns (via lemma_2_5.mp)
          apply (lemma_2_5 b S_body s s').mp
          exact h_ns_if


theorem sos_to_ns (S : Stmt) (s s' : State) :
  (⟨S, s⟩ →ₛₒₛ* s') → (⟨S, s⟩ →ₙₛ s') := by
  intro h
  -- 1. Convert star to a k-step relation
  obtain ⟨k, hk⟩ := star_to_small_step_k h
  -- 2. Call a helper lemma that works via induction on k
  exact sos_k_to_ns S s s' k hk

theorem ns_equivalent_sos (S : Stmt) (s s' : State) :
  (⟨S, s⟩ →ₙₛ s') ↔ (⟨ S, s⟩ →ₛₒₛ* s') := by
  apply Iff.intro
  case mp => exact ns_to_sos S s s'
  case mpr => exact sos_to_ns S s s'
