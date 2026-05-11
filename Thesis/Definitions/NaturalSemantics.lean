import Thesis.Definitions.While

namespace NaturalSemantics

open While


-- Define the standard Nielson & Nielson notation
set_option quotPrecheck false in
set_option hygiene false in
notation:40 "⟨" S "," s "⟩" " →ₙₛ " s' => big_step S s s'

/--
  Natural Operational Semantics (Big-Step)
  Notation: " ⟨S, s⟩ →ₙₛ s' " and  " ⟨S, s⟩ ⇓ₙₛ s' "
  means executing S in state s results in state s'
--/
inductive big_step : Stmt → State → State → Prop where
  -- [assₙₛ] rule (axionom)
  | ass {s x a} :
      ⟨(Stmt.ass x a), s⟩ →ₙₛ (s[x ↦ 𝓐⟦a⟧ s])

  -- [skipₙₛ] rule (axionom)
  | skip {s} :
      ⟨Stmt.skip, s⟩ →ₙₛ s

  -- [compₙₛ] rule (given ⟨S₁, s⟩ → s' and ⟨S₂, s'⟩ → s'' we produce ⟨S, s⟩ → s'')
  | comp {S₁ S₂ s s' s''}
    (h_left  : ⟨S₁, s⟩ →ₙₛ s')
    (h_right : ⟨S₂, s'⟩ →ₙₛ s'') :
      ⟨(Stmt.composition S₁ S₂), s⟩ →ₙₛ s''

  -- [ifᵗᵗₙₛ] rule (given ⟨S₁, s⟩ → s' and 𝓑⟦b⟧ s = true we produce ⟨S, s⟩ → s')
  | if_true {b S₁ S₂ s s'} :
    (h_cond : 𝓑⟦b⟧ s = true) →
    (h_then : ⟨S₁, s⟩ →ₙₛ s') →
      ⟨(Stmt.cond b S₁ S₂), s⟩ →ₙₛ s'

  -- [ifᶠᶠₙₛ] rule (given ⟨S₂, s⟩ → s' and 𝓑⟦b⟧ s = false we produce ⟨S, s⟩ → s')
  | if_false {b S₁ S₂ s s'}
    (h_cond : 𝓑⟦b⟧ s = false)
    (h_else : ⟨S₂, s⟩ →ₙₛ s') :
      ⟨(Stmt.cond b S₁ S₂), s⟩ →ₙₛ s'

  -- [whileᵗᵗₙₛ] rule (given ⟨S', s⟩ → s', ⟨while b do S', s'⟩ → s'' and 𝓑⟦b⟧ s = true we produce ⟨S, s⟩ → s'')
  | while_true {b S s s' s''}
    (h_cond : 𝓑⟦b⟧ s = true)
    (h_step : ⟨S, s⟩ →ₙₛ s')
    (h_rest : ⟨(Stmt.loop b S), s'⟩ →ₙₛ s'') :
      ⟨(Stmt.loop b S), s⟩ →ₙₛ s''

  -- [whileᶠᶠₙₛ] rule (given 𝓑⟦b⟧ s = false we produce ⟨S, s⟩ → s)
  | while_false {b S' s}
    (h_cond : 𝓑⟦b⟧ s = false) :
      ⟨(Stmt.loop b S'), s⟩ →ₙₛ s

@[app_unexpander big_step] def unexpandBigStep : Lean.PrettyPrinter.Unexpander
  | `($_ $S $s $s') => `(⟨$S,  $s⟩ →ₙₛ $s')
  | _ => throw ()


end NaturalSemantics
