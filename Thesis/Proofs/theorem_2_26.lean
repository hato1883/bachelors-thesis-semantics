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

  | while_true hcond h_body h_rest ih_body ih_loop =>
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

        case comp1 S S1' S2 s_next h_step_S1 =>
          -- Text: "The cases [comp1_sos] and [comp2_sos]... apply Lemma 2.19"
          -- We go back to the original h_k_step and apply seq_split
          obtain ⟨s_mid, k₁, k₂, hk1, hk2, h_sum⟩ := seq_split h_rest
          apply big_step.comp (s' := s_mid)
          case h_left => -- Goal: ⟨S, s⟩ →ₙₛ s_mid
            -- We combine the very first step (h_step_s1) with the rest of S.
            have h_s_full : ⟨S, s⟩ →ₛₒₛ[k₁ + 1] s_mid := by
              apply small_step_k.step h_step_s1 hk1

            have h_k2_pos : k₂ > 0 := by
              -- Inversion on hk2: a 0-step derivation to a state s' is impossible for a Stmt
              cases k₂
              case zero => cases hk2 -- This should reach a contradiction
              case succ => linarith

            apply ih (k₁ + 1) (by linarith) _ _ _ h_s_full

          case h_right =>
            -- Goal: ⟨S2, s_mid⟩ →ₙₛ s'
            -- Use hk2: ⟨S2, s_mid⟩ →ₛₒₛ[k₂] s'
            apply ih k₂ (by linarith) S2 s_mid s' hk2

        case comp2 S1 S2 s_next h_step_s1 =>
          -- S1 has terminated in one step to s_next
          -- h_rest: ⟨S2, s_next⟩ →ₛₒₛ[k₀] s'
          apply big_step.comp (s' := s_next)
          case h_left =>
            -- 1. We need to prove 1 < k₀ + 1 to satisfy the IH
            -- As discussed, S2 must take at least 1 step to reach a state, so k₀ > 0.
            have h_lt_one : 1 < k₀ + 1 := by
              cases k₀
              case zero => cases h_rest -- Contradiction: S2 can't finish in 0 steps
              case succ => linarith

            -- 2. Apply IH for exactly 1 step
            apply ih 1 h_lt_one S1 s s_next

            -- 3. Construct a 1-step derivation: (first step) + (0 steps)
            exact small_step_k.step h_step_s1 small_step_k.refl

          case h_right =>
            -- Goal: ⟨S2, s_next⟩ →ₙₛ s'
            -- We have h_rest: ⟨S2, s_next⟩ →ₛₒₛ[k₀] s'
            -- And we know k₀ < k₀ + 1
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
          -- Then use the bridge: if_ns → while_ns
          rw [while_unroll]
          exact h_ns_if


theorem sos_to_ns (S : Stmt) (s s' : State) :
  (⟨S, s⟩ →ₛₒₛ* s') → (⟨S, s⟩ →ₙₛ s') := by
  intro h
  -- 1. Convert star to a k-step relation
  obtain ⟨k, hk⟩ := star_to_small_step_k h
  -- 2. Call a helper lemma that works via induction on k
  exact sos_k_to_ns S s s' k hk

theorem ns_equvivlent_sos (S : Stmt) (s s' : State) :
  (⟨S, s⟩ →ₙₛ s') ↔ (⟨ S, s⟩ →ₛₒₛ* s') := by
  apply Iff.intro
  case mp => exact ns_to_sos S s s'
  case mpr => exact sos_to_ns S s s'
