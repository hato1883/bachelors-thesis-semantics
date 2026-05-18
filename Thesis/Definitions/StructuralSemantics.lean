import Thesis.Definitions.While

import Lean.PrettyPrinter.Delaborator.Basic

namespace StructuralSemantics

open While


/-
  small_step_k S s k γ :
  "⟨S, s⟩ →ₛₒₛⁿ[k] γ" means S in state s reaches γ in exactly k small steps.
  small_step_star S s γ :
  "⟨S, s⟩ →ₛₒₛ* γ" means S in state s reaches γ in finitely many (possibly zero) small steps.
-/
set_option quotPrecheck false in
set_option hygiene false in
notation:40 "⟨" S "," s "⟩"
  " →ₛₒₛ " "⟨" S' "," s':40 "⟩" =>
  small_step S s (Config.step S' s')
set_option quotPrecheck false in
set_option hygiene false in
notation:40 "⟨" S "," s "⟩"
  " →ₛₒₛ " s':40 =>
  small_step S s (Config.final s')

-- k-step
set_option quotPrecheck false in
set_option hygiene false in
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ[" k "] " "⟨" S' "," s':40 "⟩" => small_step_k (Config.step S s) k (Config.step S' s')
set_option quotPrecheck false in
set_option hygiene false in
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ[" k "] " s':40                => small_step_k (Config.step S s) k (Config.final s')


-- star
set_option quotPrecheck false in
set_option hygiene false in
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ* " "⟨" S' "," s':40 "⟩" => small_step_star (Config.step S s) (Config.step S' s')
set_option quotPrecheck false in
set_option hygiene false in
notation:40 "⟨" S "," s "⟩" " →ₛₒₛ* " s':40                => small_step_star (Config.step S s) (Config.final s')


/--
  Structural Operational Semantics
  Notation: " ⟨S, s⟩ →ₙₛ s' " and  " ⟨S, s⟩ ⇓ₙₛ s' "
  means executing S in state s results in state s'
--/
inductive Config where
  | step : Stmt → State → Config
  | final : State → Config

/-
  Coercions to allow using `State` or `(Stmt × State)` where `Config` is expected.
  This makes Lean automatically convert `s : State` to `Config.final s` and
  `(S, s) : Stmt × State` to `Config.step S s`, avoiding annotation/casting issues
  when using the `→ₛₒₛ`, `→ₛₒₛ[k]`, and `→ₛₒₛ*` notations.
-/
instance : Coe State Config where
  coe s := Config.final s

instance : Coe (Stmt × State) Config where
  coe p := Config.step p.1 p.2

inductive small_step : Stmt → State → Config → Prop where
  -- [assₛₒₛ]
  | ass {s x a} :
    ⟨x :≡ a, s⟩ →ₛₒₛ s[x ↦ 𝓐⟦a⟧ s]

  -- [skipₛₒₛ]
  | skip {s} :
    ⟨Stmt.skip, s⟩ →ₛₒₛ s

  -- [comp1ₛₒₛ]
  | comp1 {S₁ S₁' S₂ s s'}
      (progress : ⟨S₁, s⟩ →ₛₒₛ  ⟨S₁', s'⟩) :
    ⟨S₁; S₂, s⟩ →ₛₒₛ  ⟨S₁'; S₂, s'⟩

  -- [comp2ₛₒₛ]
  | comp2 {S₁ S₂ s s'}
      (terminates : ⟨S₁, s⟩ →ₛₒₛ s') :
    ⟨S₁; S₂, s⟩ →ₛₒₛ ⟨S₂, s'⟩

  -- [ifᵗᵗₛₒₛ]
  | if_true {b S₁ S₂ s}
      (h_cond_true : 𝓑⟦b⟧ s = tt) :
    ⟨if b then S₁ else S₂, s⟩ →ₛₒₛ ⟨S₁, s⟩

  -- [ifᶠᶠₛₒₛ]
  | if_false {b S₁ S₂ s}
      (h_cond_false : 𝓑⟦b⟧ s = ff) :
    ⟨if b then S₁ else S₂, s⟩ →ₛₒₛ ⟨S₂, s⟩

  -- [whileₛₒₛ]
  | while_unroll {b S s} :
    ⟨while b then S, s⟩ →ₛₒₛ ⟨if b then (S; while b then S) else (Stmt.skip), s⟩


/-
  k-step and star-step relations for NS semantics
  ⟨S, s⟩ →ₛₒₛ[k] γ : exactly k small steps from (S, s) to γ
  ⟨S, s⟩ →ₛₒₛ* γ : any finite number of small steps from (S, s) to γ
-/
/-- k-step relation: γ₁ reaches γ₂ in exactly k steps -/
inductive small_step_k : Config → Nat → Config → Prop where
  | refl {γ} :
      small_step_k γ 0 γ
  | step {S s γ' γ'' k}
    (step : small_step S s γ')
    (rest : small_step_k γ' k γ'') :
      small_step_k (Config.step S s) (k+1) γ''

/-- Reflexive-transitive closure -/
inductive small_step_star : Config → Config → Prop where
  | refl {γ} :
      small_step_star γ γ
  | step {S s γ' γ''}
    (step : small_step S s γ')
    (rest : small_step_star γ' γ'') :
      small_step_star (Config.step S s) γ''

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
