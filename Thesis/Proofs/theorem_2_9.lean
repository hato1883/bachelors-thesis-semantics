import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics

open While
open NaturalSemantics

/--
Determinism proof by induction on the first derivation tree.

Difference from pen-and-paper:
- Pen-and-paper proofs treat inversion implicitly ("the only rule that could derive ...").
- In Lean we make inversion explicit: after introducing the alternative derivation we
  `cases` on it to enumerate constructors and then use the induction hypotheses
  to discharge each branch.

Naming conventions used here:
- `h...`  : hypothesis/proof terms (e.g. `h_cond_true`).
- `ih...` : induction hypotheses (e.g. `ih_seq_left`).
- `s...`  : states (e.g. `s'`, `s''`).
- `h_deriv_alt` : the alternative derivation introduced by `intro`.
--/
theorem deterministic (S : Stmt) (s s' s'' : State) (h: ⟨S, s⟩ →ₙₛ s') :
  (⟨ S, s⟩ →ₙₛ s'')
  →
  (s' = s'') := by
  induction h
  generalizing s'' with
  -- verifying tree built using [assₙₛ] axiom
  | ass =>
    -- First explicit Lean-only inversion point (textbook keeps this implicit):
    -- introduce the alternative derivation, then invert it by constructor cases.
    intro h_deriv_alt
    cases h_deriv_alt with
    | ass =>
      rfl

  -- verifying tree built using [skipₙₛ] axiom
  | skip =>
    intro h_deriv_alt
    cases h_deriv_alt with
    | skip =>
      rfl

  -- verifying tree built using [compₙₛ] rule
  | comp h_left h_right ih_left ih_right =>
    -- original derivation gives an intermediate state for the left component
    -- and then the right component yields the final state. The only possible
    -- rule for another derivation of the composition is [compₙₛ], so invert
    -- the alternative derivation and apply the IHs in the same order as
    -- the pen-and-paper proof.
    intro h_deriv_alt
    cases h_deriv_alt with
    | comp h_alt_left h_alt_right =>
      -- apply IH to the first sub-derivation to align intermediate states
      have h_mid_eq := ih_left _ h_alt_left
      subst h_mid_eq
      -- apply IH to the second sub-derivation to conclude final equality
      exact ih_right _ h_alt_right

  -- verifying tree built using [ifᵗᵗₙₛ] rule
  | if_true h_cond_true h_deriv_then ih_then =>
    intro h_deriv_alt
    cases h_deriv_alt with
    | if_true _ h_deriv_then_alt =>
      exact ih_then _ h_deriv_then_alt
    | if_false h_cond_false_alt _ =>
      rw [h_cond_true] at h_cond_false_alt
      contradiction

  -- verifying tree built using [ifᶠᶠₙₛ] rule
  | if_false h_cond_false h_deriv_else ih_else =>
    intro h_deriv_alt
    cases h_deriv_alt with
    | if_false _ h_deriv_else_alt =>
      exact ih_else _ h_deriv_else_alt
    | if_true h_cond_true_alt _ =>
      rw [h_cond_false] at h_cond_true_alt
      contradiction

  -- verifying tree built using [whileᵗᵗₙₛ] rule
  | while_true h_cond_true h_deriv_body h_deriv_rest ih_while_body ih_while_rest =>
    intro h_deriv_alt
    cases h_deriv_alt with
    | while_false h_cond_false_alt =>
      rw [h_cond_true] at h_cond_false_alt
      contradiction
    | while_true _ h_deriv_body_alt h_deriv_rest_alt =>
      -- textbook [whileᵗᵗₙₛ]: align intermediate state via body IH, then apply loop IH
      have h_state_eq : _ = _ := ih_while_body _ h_deriv_body_alt
      subst h_state_eq
      exact ih_while_rest _ h_deriv_rest_alt

  -- verifying tree built using [ẃhileᶠᶠₙₛ] rule
  | while_false h_cond_false =>
    intro h_deriv_alt
    cases h_deriv_alt with
    | while_true h_cond_true_alt _ _ =>
      rw [h_cond_false] at h_cond_true_alt
      contradiction
    | while_false _ =>
      rfl
