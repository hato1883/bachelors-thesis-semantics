import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics
import Thesis.Definitions.StructuralSemantics

open While

section ns
open NaturalSemantics

section example_2_1

example (s : State) :
  let S := Stmt.composition
    (Stmt.composition (Stmt.ass "x" 1) (Stmt.ass "y" 2))
    (Stmt.ass "z" 3)
  let s'   := s["x" ↦ 1]
  let s''  := s'["y" ↦ 2]
  let s''' := s''["z" ↦ 3]
  ⟨ S, s ⟩ →ₙₛ s''' := by
  -- 1. Breakdown the first sequence
  apply big_step.seq
  · -- Left side: (x := 1; y = 2)
    apply big_step.seq
    · -- x := 1
      apply big_step.ass
    · -- y := 2
      apply big_step.ass
  · -- Right side: z := 3
    -- simplify [x↦𝓐⟦1⟧ s][y↦𝓐⟦2⟧ s[x↦𝓐⟦1⟧ s] to [x↦1][y↦2]
    simp [Aexp_eval, Num_to_Z]
    apply big_step.ass

end example_2_1


section example_2_2

example :
  let S := Stmt.composition
    (Stmt.ass "y" 1)
    (Stmt.loop
      (Bexp.not (Bexp.eq "x" 1))
      (Stmt.composition
        (Stmt.ass "y" (Aexp.mul "y" "x"))
        (Stmt.ass "x" (Aexp.sub "x" 1)))
    )
  let s    := default_state["x" ↦ 3]
  let s'   := s["y" ↦ 6]
  let s''  := s'["x" ↦ 1]
  ⟨ S, s ⟩ →ₙₛ s'' := by
  -- 1. Breakdown the first sequence
  apply big_step.seq
  · -- Left side: y := 1
    apply big_step.ass
  · -- Right side: while ¬ (x = 1) do (y := y*x; x := x-1)
    -- simplify [x↦𝓐⟦1⟧ s][y↦𝓐⟦2⟧ s[x↦𝓐⟦1⟧ s] to [x↦1][y↦2]
    simp [Bexp_eval, Aexp_eval, Num_to_Z]
    apply big_step.while_true
    · -- 𝓑⟦¬(x=1)⟧ s[y↦1] = true
      simp [Bexp_eval]
    · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[y↦1]⟩ →ₙₛ s'
      apply big_step.seq
      · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
        apply big_step.ass
      · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
        apply big_step.ass
    · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
      apply big_step.while_true
      · -- 𝓑⟦¬(x=1)⟧ s[x↦2][y↦3] = true
        simp [Bexp_eval]
      · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[x↦2][y↦3]⟩ →ₙₛ s'
        apply big_step.seq
        · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
          apply big_step.ass
        · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
          apply big_step.ass
      · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
        -- Change default_state[x↦3][y↦1][y↦3][x↦2][y↦6][x↦1] to default_state[x↦1][y↦6]
        simp [assign_comm, assign_shadow]
        apply big_step.while_false
        · -- 𝓑⟦¬(x=1)⟧ s[x↦1][y↦6] = false
          simp [Bexp_eval]

end example_2_2


section example_2_2

example :
  let S := Stmt.composition
    (Stmt.ass "y" 1)
    (Stmt.loop
      (Bexp.not (Bexp.eq "x" 1))
      (Stmt.composition
        (Stmt.ass "y" (Aexp.mul "y" "x"))
        (Stmt.ass "x" (Aexp.sub "x" 1)))
    )
  let s    := default_state["x" ↦ 3]
  let s'   := s["y" ↦ 6]
  let s''  := s'["x" ↦ 1]
  ⟨ S, s ⟩ →ₙₛ s'' := by
  -- 1. Breakdown the first sequence
  apply big_step.seq
  · -- Left side: y := 1
    apply big_step.ass
  · -- Right side: z := 3
    -- simplify [x↦𝓐⟦1⟧ s][y↦𝓐⟦2⟧ s[x↦𝓐⟦1⟧ s] to [x↦1][y↦2]
    simp [Bexp_eval, Aexp_eval, Num_to_Z]
    apply big_step.while_true
    · -- 𝓑⟦¬(x=1)⟧ s[y↦1] = true
      simp [Bexp_eval]
    · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[y↦1]⟩ →ₙₛ s'
      apply big_step.seq
      · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
        apply big_step.ass
      · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
        apply big_step.ass
    · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
      apply big_step.while_true
      · -- 𝓑⟦¬(x=1)⟧ s[x↦2][y↦3] = true
        simp [Bexp_eval]
      · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[x↦2][y↦3]⟩ →ₙₛ s'
        apply big_step.seq
        · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
          apply big_step.ass
        · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
          apply big_step.ass
      · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
        -- Change default_state[x↦3][y↦1][y↦3][x↦2][y↦6][x↦1] to default_state[x↦1][y↦6]
        simp [assign_comm, assign_shadow]
        apply big_step.while_false
        · -- 𝓑⟦¬(x=1)⟧ s[x↦1][y↦6] = false
          simp [Bexp_eval]

end example_2_2

end ns

section sos
open StructuralSemantics

section example_2_14

def s₀ : State :=
  fun v => if v = "x" then 5 else if v = "y" then 7 else 0

def S : Stmt := (("z" :≡ "x"); "x" :≡ "y"); ("y" :≡ "z")

 example : ⟨S, s₀⟩ →ₛₒₛ ⟨("x" :≡ "y"); ("y" :≡ "z"), s₀["z"↦5]⟩ := by
  -- inner: z := x, s₀ ⇒ s₀[z↦5]
  apply small_step.comp1
  apply small_step.comp2
  apply small_step.ass

 example : ⟨("x" :≡ "y"); ("y" :≡ "z"), s₀["z"↦5]⟩ →ₛₒₛ ⟨"y" :≡ "z", (s₀["z"↦5])["x"↦7]⟩ := by
  apply small_step.comp2
  apply small_step.ass

 example : ⟨"y" :≡ "z", (s₀["z"↦5])["x"↦7]⟩ →ₛₒₛ ((s₀["z"↦5])["x"↦7])["y"↦5] := by
  apply small_step.ass

end example_2_14

section test

def s₁ : State :=
  fun v => if v = "x" then 5 else if v = "y" then 7 else 0

def S₁ : Stmt := (("z" :≡ "x"); "x" :≡ "y"); ("y" :≡ "z")

example : ⟨"y" :≡ "z", (s₀["z"↦5])["x"↦7]⟩ →ₛₒₛ ((s₀["z"↦5])["x"↦7])["y"↦5] := by
  apply small_step.ass

end test

end sos
