import Thesis.Definitions.While

import Lean.PrettyPrinter.Delaborator.Basic

namespace StructuralSemantics

open While

/--
  Structural Operational Semantics (Big-Step)
  Notation: " ⟨S, s⟩ →ₙₛ s' " and  " ⟨S, s⟩ ⇓ₙₛ s' "
  means executing S in state s results in state s'
--/

inductive Config where
  | step : Stmt → State → Config
  | final : State → Config

inductive small_step : Stmt → State → Config → Prop where
  -- [assₛₒₛ]
  | ass {s x a} :
      small_step (Stmt.ass x a) s (Config.final (s[x ↦ 𝒜⟦a⟧ s]))

  -- [skipₛₒₛ]
  | skip {s} :
      small_step Stmt.skip s (Config.final s)

  -- [comp1ₛₒₛ]
  | comp1 {S₁ S₁' S₂ s s'} :
      small_step S₁ s (Config.step S₁' s') →
      small_step (Stmt.sequence S₁ S₂) s (Config.step (Stmt.sequence S₁' S₂) s')

  -- [comp2ₛₒₛ]
  | comp2 {S₁ S₂ s s'} :
      small_step S₁ s (Config.final s') →
      small_step (Stmt.sequence S₁ S₂) s (Config.step S₂ s')

  -- [ifᵗᵗₛₒₛ]
  | if_true {b S₁ S₂ s} (h : ℬ⟦b⟧ s = true) :
      small_step (Stmt.cond b S₁ S₂) s (Config.step S₁ s)

  -- [ifᶠᶠₛₒₛ]
  | if_false {b S₁ S₂ s} (h : ℬ⟦b⟧ s = false) :
      small_step (Stmt.cond b S₁ S₂) s (Config.step S₂ s)

  -- [whileₛₒₛ]
  | while {b S s} :
      small_step (Stmt.loop b S) s (Config.step (Stmt.cond b (Stmt.sequence S (Stmt.loop b S)) Stmt.skip) s)

notation:40 "⟨" S "," s "⟩" " →ₛₒₛ " "⟨" S' "," s' "⟩" => small_step S s (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ " s' => small_step S s (Config.final s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ " "⟨" S' "," s' "⟩" => small_step S s (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ " s' => small_step S s (Config.final s')

@[app_unexpander Config.final]
def unexpandConfigFinal : Lean.PrettyPrinter.Unexpander
  | `($_ $s) => `($s)
  | _ => throw ()

@[app_unexpander Config.step]
def unexpandConfigStep : Lean.PrettyPrinter.Unexpander
  | `($_ $S $s) => `(⟨$S, $s⟩)
  | _ => throw ()

@[app_unexpander small_step]
def unexpandSmallStep : Lean.PrettyPrinter.Unexpander
  | `($_ $S $s $γ) => `(⟨$S,  $s⟩ →ₛₒₛ $γ)
  | _ => throw ()

end StructuralSemantics
