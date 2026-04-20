import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics

import Mathlib.Data.Part

namespace PartialSemantics

open While
open NaturalSemantics

/--
  Using Lean's native `Part` monad for partiality.
  This is cleaner for equivalence proofs.

  `Part α` represents a partial computation of type `α`:
  - `pure a` : terminates with value a
  - diverges : never terminates
-/
partial def eval : Stmt → State → Option State
  | Stmt.ass x a, s => some (s[x ↦ 𝓐⟦a⟧ s])
  | Stmt.skip, s => some s
  | Stmt.sequence S₁ S₂, s => do
      (eval S₁ s).bind (fun s' => eval S₂ s')
  | Stmt.cond b S₁ S₂, s =>
      if 𝓑⟦b⟧ s then eval S₁ s else eval S₂ s
  | Stmt.loop b S, s =>
      if 𝓑⟦b⟧ s then
        (eval S s).bind (fun s' => eval (Stmt.loop b S) s')
      else
        some s

example (x : Var) (a : Aexp) (s : State) :
  eval (Stmt.ass x a) s = some (s[x ↦ 𝓐⟦a⟧ s]) := by
  unfold eval
  decide

-- Soundness: NS implies evaluation succeeds
theorem ns_to_eval : ∀ (S : Stmt) (s s' : State),
  big_step S s s' → eval S s = some s' := by
  intro S s s' h
  induction h with
  | ass =>
      rename_i s x a
      -- Unfold eval definition
      show eval (Stmt.ass x a) s = some (s[x ↦ 𝓐⟦a⟧ s])
      unfold eval
      -- By definition of eval:
      -- eval (Stmt.ass x a) s = some (s[x ↦ 𝓐⟦a⟧ s])
      rfl
  | skip => rfl
  | seq h₁ h₂ ih₁ ih₂ =>
      simp [eval]
      rw [ih₁, ih₂]
  | if_true hb h ih =>
      simp [eval, hb, ih]
  | if_false hb h ih =>
      simp [eval, hb, ih]
  | while_true hb h₁ h₂ ih₁ ih₂ =>
      simp [eval, hb, ih₁, ih₂]
  | while_false hb =>
      simp [eval, hb]

-- Notation
notation "⟨" S "," s "⟩" " ⇝ " s' => eval S s = some s'

end PartialSemantics
