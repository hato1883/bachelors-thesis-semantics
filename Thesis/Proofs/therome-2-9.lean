import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics

open While
open NaturalSemantics

/--
  Determinism proof by induction on the first derivation tree.

  Strategy alignment with literature:
  - Textbook prose says "the only rule that could derive ..." and treats that
    inversion step implicitly.
  - In Lean, that same step must be explicit: after introducing the second
    derivation, we perform `cases` on it to enumerate the possible constructors.
  - So each branch follows the same logical pattern as the book:
    induction case, inversion of the alternative derivation, then IH/contradiction.

  Naming scheme used in this file:
  - `h...`  : hypothesis/proof term (examples: `hCondTrue`, `hBodyAlt`, `hDerivSeqLeftAlt`).
  - `ih...` : induction hypothesis supplied by `induction` (examples: `ihSeqLeft`, `ihWhileRest`).
  - `s...`  : states (examples: `s`, `s'`, `s''`, `hStateEq`).
  - `hDerivAlt` : the second derivation provided after `intro`.
--/
theorem deterministic (S : Stmt) (s s' s'' : State) (h: ⟨S, s⟩ →ₙₛ s') :
  (⟨ S, s⟩ →ₙₛ s'')
  →
  (s' = s'') := by
  induction h generalizing s'' with
  -- verifying tree built using [assₙₛ] axiom
  | ass =>
    -- First explicit Lean-only inversion point (textbook keeps this implicit):
    -- introduce the alternative derivation, then invert it by constructor cases.
    intro hDerivAlt
    cases hDerivAlt with
    | ass =>
      rfl

  -- verifying tree built using [skipₙₛ] axiom
  | skip =>
    intro hDerivAlt
    cases hDerivAlt with
    | skip =>
      rfl

  -- verifying tree built using [compₙₛ] rule
  | seq _ _ ihSeqLeft ihSeqRight =>
    intro hDerivAlt
    cases hDerivAlt with
    | seq hDerivSeqLeftAlt hDerivSeqRightAlt =>
      -- textbook [compₙₛ]: first premises give equal intermediate state, then second premises give final equality
      have hStateEq : _ = _ := ihSeqLeft _ hDerivSeqLeftAlt
      subst hStateEq
      exact ihSeqRight _ hDerivSeqRightAlt

  -- verifying tree built using [ifᵗᵗₙₛ] rule
  | if_true hCondTrue hDerivThen ihThen =>
    intro hDerivAlt
    cases hDerivAlt with
    | if_true _ hDerivThenAlt =>
      exact ihThen _ hDerivThenAlt
    | if_false hCondFalseAlt _ =>
      rw [hCondTrue] at hCondFalseAlt
      contradiction

  -- verifying tree built using [ifᶠᶠₙₛ] rule
  | if_false hCondFalse hDerivElse ihElse =>
    intro hDerivAlt
    cases hDerivAlt with
    | if_false _ hDerivElseAlt =>
      exact ihElse _ hDerivElseAlt
    | if_true hCondTrueAlt _ =>
      rw [hCondFalse] at hCondTrueAlt
      contradiction

  -- verifying tree built using [whileᵗᵗₙₛ] rule
  | while_true hCondTrue hDerivBody hDerivRest ihWhileBody ihWhileRest =>
    intro hDerivAlt
    cases hDerivAlt with
    | while_false hCondFalseAlt =>
      rw [hCondTrue] at hCondFalseAlt
      contradiction
    | while_true _ hDerivBodyAlt hDerivRestAlt =>
      -- textbook [whileᵗᵗₙₛ]: align intermediate state via body IH, then apply loop IH
      have hStateEq : _ = _ := ihWhileBody _ hDerivBodyAlt
      subst hStateEq
      exact ihWhileRest _ hDerivRestAlt

  -- verifying tree built using [ẃhileᶠᶠₙₛ] rule
  | while_false hCondFalse =>
    intro hDerivAlt
    cases hDerivAlt with
    | while_true hCondTrueAlt _ _ =>
      rw [hCondFalse] at hCondTrueAlt
      contradiction
    | while_false _ =>
      rfl
