
import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics

open While
open NaturalSemantics

/--
  Semantic equivalence of while-loop and its one-step unrolling.

  Proof strategy (cf. literature):
  - The proof is bidirectional (iff):
    1. If ⟨while b do S, s⟩ →ₙₛ s', then ⟨if b then (S; while b do S) else skip, s⟩ →ₙₛ s'.
    2. If ⟨if b then (S; while b do S) else skip, s⟩ →ₙₛ s', then ⟨while b do S, s⟩ →ₙₛ s'.
  - In Lean, we must explicitly invert the derivation trees (using `cases`) where the textbook says "the derivation tree has one of two forms...".
  - The first explicit Lean-only inversion is marked below.

  Naming scheme:
  - `h...`  : hypothesis/proof term (e.g. `hCondTrue`, `hDerivWhileTrue`, `hDerivSeqRight`).
  - `hDeriv...Alt` : alternative derivation in the direction.
  - `s...`  : states (e.g. `s`, `s'`, `sMid`).
-/
lemma while_unroll (b : Bexp) (S : Stmt) (s s' : State) :
  (⟨Stmt.loop b S, s⟩ →ₙₛ s') ↔ (⟨Stmt.cond b (Stmt.sequence S (Stmt.loop b S)) Stmt.skip, s⟩ →ₙₛ s') := by
  apply Iff.intro
  -- Forward direction: while → if
  case mp =>
    intro hDerivWhile
    by_cases hCondTrue : 𝓑⟦b⟧ s = true
    case pos =>
      apply big_step.if_true
      · exact hCondTrue
      · -- First explicit Lean-only inversion: invert the while derivation tree.
        cases hDerivWhile with
        | while_true hCondTrue' hDerivSeqLeft hDerivWhileRest =>
          apply big_step.seq
          · exact hDerivSeqLeft
          · exact hDerivWhileRest
        | while_false hCondFalseAlt =>
          rw [hCondTrue] at hCondFalseAlt
          contradiction
    case neg =>
      cases hDerivWhile with
      | while_false hCondFalse =>
        apply big_step.if_false
        · exact hCondFalse
        · exact big_step.skip
      | while_true hCondTrue' _ _ =>
        contradiction
  -- Backward direction: if → while
  case mpr =>
    intro hDerivIf
    by_cases hCondTrue : 𝓑⟦b⟧ s = true
    case pos =>
      cases hDerivIf with
      | if_true hCondTrue' hDerivSeq =>
        cases hDerivSeq with
        | seq hDerivSeqLeft hDerivSeqRight =>
          rename_i sMid
          apply big_step.while_true
          · exact hCondTrue
          · exact hDerivSeqLeft
          · exact hDerivSeqRight
      | if_false hCondFalseAlt _ =>
        rw [hCondTrue] at hCondFalseAlt
        contradiction
    case neg =>
      cases hDerivIf with
      | if_true hCondTrue' _ =>
        contradiction
      | if_false hCondFalse hDerivSkip =>
        cases hDerivSkip
        apply big_step.while_false
        exact hCondFalse
