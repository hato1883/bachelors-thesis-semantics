import Thesis.Definitions.While

namespace NaturalSemantics

open While

/--
  Natural Operational Semantics (Big-Step)
  Notation: " ⟨S, s⟩ →ₙₛ s' " and  " ⟨S, s⟩ ⇓ₙₛ s' "
  means executing S in state s results in state s'
--/

inductive big_step : Stmt → State → State → Prop where
  -- [assₙₛ] rule (axionom)
  | ass {s x a} :
      big_step (Stmt.ass x a) s (s[x ↦ 𝓐⟦a⟧ s])

  -- [skipₙₛ] rule (axionom)
  | skip {s} :
      big_step Stmt.skip s s

  -- [compₙₛ] rule (given ⟨S₁, s⟩ → s' and ⟨S₂, s'⟩ → s'' we produce ⟨S, s⟩ → s'')
  | seq {S₁ S₂ s s' s''}
    (h_left  : big_step S₁ s  s')
    (h_right : big_step S₂ s' s'') :
      big_step (Stmt.sequence S₁ S₂) s s''

  -- [ifᵗᵗₙₛ] rule (given ⟨S₁, s⟩ → s' and 𝓑⟦b⟧ s = true we produce ⟨S, s⟩ → s')
  | if_true {b S₁ S₂ s s'} :
    (h_cond : 𝓑⟦b⟧ s = true) →
    (h_then : big_step S₁ s s') →
      big_step (Stmt.cond b S₁ S₂) s s'

  -- [ifᶠᶠₙₛ] rule (given ⟨S₂, s⟩ → s' and 𝓑⟦b⟧ s = false we produce ⟨S, s⟩ → s')
  | if_false {b S₁ S₂ s s'}
    (h_cond : 𝓑⟦b⟧ s = false)
    (h_else : big_step S₂ s s') :
      big_step (Stmt.cond b S₁ S₂) s s'

  -- [whileᵗᵗₙₛ] rule (given ⟨S', s⟩ → s', ⟨while b do S', s'⟩ → s'' and 𝓑⟦b⟧ s = true we produce ⟨S, s⟩ → s'')
  | while_true {b S s s' s''}
    (h_cond : 𝓑⟦b⟧ s = true)
    (h_step : big_step S s s')
    (h_rest : big_step (Stmt.loop b S) s' s'') :
      big_step (Stmt.loop b S) s s''

  -- [whileᶠᶠₙₛ] rule (given 𝓑⟦b⟧ s = false we produce ⟨S, s⟩ → s)
  | while_false {b S' s}
    (h_cond : 𝓑⟦b⟧ s = false) :
      big_step (Stmt.loop b S') s s

-- Define the standard Nielson & Nielson notation
notation:40 "⟨" S "," s "⟩" " →ₙₛ " s' => big_step S s s'
notation:40 "⟨" S "," s "⟩" " ⇓ₙₛ " s' => big_step S s s'

@[app_unexpander big_step] def unexpandBigStep : Lean.PrettyPrinter.Unexpander
  | `($_ $S $s $s') => `(⟨$S,  $s⟩ →ₙₛ $s')
  | _ => throw ()


end NaturalSemantics
