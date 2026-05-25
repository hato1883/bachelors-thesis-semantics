import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics
import Thesis.Definitions.StructuralSemantics
import Thesis.Proofs.theorem_2_9


import Mathlib.Data.Part

namespace PartialSemantics

open While
open NaturalSemantics
open StructuralSemantics

--            s' if S terminates in natural semantics
-- 𝓢ₙₛ⟦S⟧ = {
--            else undefined
noncomputable
def S_ns (S : Stmt) (s : State) : Part State :=
  { Dom := ∃ s', ⟨S, s⟩ →ₙₛ s',
    get := fun h => Classical.choose h }

--            s' if S terminates in structural semantics
-- 𝓢ₛₒₛ⟦S⟧ = {
--            else undefined
noncomputable
def S_sos (S : Stmt) (s : State) : Part State :=
  { Dom := ∃ s', small_step_star (Config.step S s) (Config.final s'),
    get := fun h => Classical.choose h }


theorem S_ns_spec {S s s'} :
  s' ∈ S_ns S s ↔ big_step S s s' := by
  unfold S_ns
  constructor
  · intro h
    simp at h
    cases h with
    | intro h_dom h_get =>
      -- h_dom : ∃ s', ⟨S,s⟩ →ₙₛ s'
      -- h_get : Classical.choose h_dom = s'

      -- We know the "chosen" value satisfies the big_step relation
      have h_chosen : ⟨S,s⟩ →ₙₛ (Classical.choose h_dom) := Classical.choose_spec h_dom

      -- Since s' is equal to the chosen value (h_get), we rewrite
      rw [← h_get]
      exact h_chosen
  · intro h
    -- Goal: s' ∈ { Dom := ..., get := ... }
    -- In Lean, membership in a Part is shown by providing the domain proof
    -- and showing the function's result equals s'.
    simp [Membership.mem]

    -- 1. Prove the domain is satisfied (there exists a result)
    let h_dom : ∃ s'', big_step S s s'' := ⟨s', h⟩
    exists h_dom

    -- 2. Prove that the 'choose' result is actually s'
    -- Since big_step is deterministic, and both (Classical.choose h_dom)
    -- and (s') satisfy the relation, they must be equal.
    dsimp
    apply deterministic S s
    · exact Classical.choose_spec h_dom
    · exact h

end PartialSemantics
