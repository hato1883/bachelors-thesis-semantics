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
      small_step (Stmt.ass x a) s (Config.final (s[x ↦ 𝓐⟦a⟧ s]))

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
  | if_true {b S₁ S₂ s} (h : 𝓑⟦b⟧ s = true) :
      small_step (Stmt.cond b S₁ S₂) s (Config.step S₁ s)

  -- [ifᶠᶠₛₒₛ]
  | if_false {b S₁ S₂ s} (h : 𝓑⟦b⟧ s = false) :
      small_step (Stmt.cond b S₁ S₂) s (Config.step S₂ s)

  -- [whileₛₒₛ]
  | while {b S s} :
      small_step (Stmt.loop b S) s (Config.step (Stmt.cond b (Stmt.sequence S (Stmt.loop b S)) Stmt.skip) s)


notation:40 "⟨" S "," s "⟩" " →ₛₒₛ " "⟨" S' "," s':40 "⟩" => small_step S s (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ " s':40 => small_step S s (Config.final s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ " "⟨" S' "," s':40 "⟩" => small_step S s (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ " s':40 => small_step S s (Config.final s')

/-
  small_step_k S s k γ :
  "⟨S, s⟩ →ₛₒₛⁿ[k] γ" means S in state s reaches γ in exactly k small steps.
  small_step_star S s γ :
  "⟨S, s⟩ →ₛₒₛ* γ" means S in state s reaches γ in finitely many (possibly zero) small steps.
-/


/-
  k-step and star-step relations for small-step semantics
  ⟨S, s⟩ →ₛₒₛⁿ[k] γ : exactly k small steps from (S, s) to γ
  ⟨S, s⟩ →ₛₒₛ* γ : any finite number of small steps from (S, s) to γ
-/
/-- k-step relation: γ₁ reaches γ₂ in exactly k steps -/
inductive small_step_k : Config → Nat → Config → Prop where
  | refl {γ} :
      small_step_k γ 0 γ
  | step {S s γ' γ'' k} :
      small_step S s γ' →
      small_step_k γ' k γ'' →
      small_step_k (Config.step S s) (k + 1) γ''

/-- Reflexive-transitive closure -/
inductive small_step_star : Config → Config → Prop where
  | refl {γ} :
      small_step_star γ γ
  | step {S s γ' γ''} :
      small_step S s γ' →
      small_step_star γ' γ'' →
      small_step_star (Config.step S s) γ''

-- k-step
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ[" k "] " "⟨" S' "," s':40 "⟩" => small_step_k (Config.step S s) k (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ[" k "] " s':40               => small_step_k (Config.step S s) k (Config.final s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ[" k "] " "⟨" S' "," s':40 "⟩" => small_step_k (Config.step S s) k (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ[" k "] " s':40               => small_step_k (Config.step S s) k (Config.final s')

-- star
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ* " "⟨" S' "," s':40 "⟩" => small_step_star (Config.step S s) (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ* " s':40               => small_step_star (Config.step S s) (Config.final s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ* " "⟨" S' "," s':40 "⟩" => small_step_star (Config.step S s) (Config.step S' s')
notation:40 "⟨" S "," s "⟩" " ⇓ₛₒₛ* " s':40               => small_step_star (Config.step S s) (Config.final s')

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
  | `($_ $S $s $c) =>
      match c with
      | `(⟨$S', $s'⟩) => `(⟨$S,  $s⟩ →ₛₒₛ ⟨$S', $s'⟩)
      | `($s')        => `(⟨$S,  $s⟩ →ₛₒₛ $s')
  | _ => throw ()

@[app_unexpander small_step_k]
def unexpandSmallStepK : Lean.PrettyPrinter.Unexpander
  | `($_ $c $k $c') =>
      match c, c' with
      | `(⟨$S, $s⟩), `(⟨$S', $s'⟩) => `(⟨$S,  $s⟩ →ₛₒₛ[$k] ⟨$S', $s'⟩)
      | `(⟨$S, $s⟩), `($s')        => `(⟨$S,  $s⟩ →ₛₒₛ[$k] $s')
      | _,           _             => throw ()
  | _ => throw ()

@[app_unexpander small_step_star]
def unexpandSmallStepStar : Lean.PrettyPrinter.Unexpander
  | `($_ $c $c') =>
      match c, c' with
      | `(⟨$S, $s⟩), `(⟨$S', $s'⟩) => `(⟨$S,  $s⟩ →ₛₒₛ* ⟨$S', $s'⟩)
      | `(⟨$S, $s⟩), `($s')        => `(⟨$S,  $s⟩ →ₛₒₛ* $s')
      | _,           _             => throw ()
  | _ => throw ()

-- @[app_unexpander small_step_star.step]
-- def unexpandSmallStepStarStep : Lean.PrettyPrinter.Unexpander
--   | `($_ (Config.step $S $s) (Config.step $S' $s')) => `(⟨$S,  $s⟩ →ₛₒₛ* ⟨$S', $s'⟩)
--   | `($_ (Config.step $S $s) (Config.final $s'))    => `(⟨$S,  $s⟩ →ₛₒₛ* $s')
--   | _ => throw ()

-- @[app_unexpander small_step_star.refl]
-- def unexpandSmallStepStarRefl : Lean.PrettyPrinter.Unexpander
--   | `($_ (Config.step $S $s) (Config.step $S' $s')) => `(⟨$S,  $s⟩ →ₛₒₛ* ⟨$S', $s'⟩)
--   | `($_ (Config.step $S $s) (Config.final $s'))    => `(⟨$S,  $s⟩ →ₛₒₛ* $s')
--   | _ => throw ()

end StructuralSemantics
