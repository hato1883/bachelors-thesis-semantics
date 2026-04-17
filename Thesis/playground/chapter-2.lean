import Thesis.Definitions.While
import Thesis.Definitions.NaturalSemantics

open While
open NaturalSemantics

section example_2_1

example (s : State) :
  let S := Stmt.sequence
    (Stmt.sequence (Stmt.ass "x" 1) (Stmt.ass "y" 2))
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
      rfl -- 𝒜⟦1⟧ s = 1 is true by definition
    · -- y := 2
      apply big_step.ass
      rfl -- 𝒜⟦2⟧ s = 2 is true by definition
  · -- Right side: z := 3
    -- simplify [x↦𝒜⟦1⟧ s][y↦𝒜⟦2⟧ s[x↦𝒜⟦1⟧ s] to [x↦1][y↦2]
    simp [Aexp_eval, Num_to_Z]
    apply big_step.ass
    rfl -- 𝒜⟦3⟧ s = 2 is true by definition

end example_2_1


section example_2_2

example :
  let S := Stmt.sequence
    (Stmt.ass "y" 1)
    (Stmt.loop
      (Bexp.not (Bexp.eq "x" 1))
      (Stmt.sequence
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
    rfl -- 𝒜⟦1⟧ s = 1 is true by definition
  · -- Right side: while ¬ (x = 1) do (y := y*x; x := x-1)
    -- simplify [x↦𝒜⟦1⟧ s][y↦𝒜⟦2⟧ s[x↦𝒜⟦1⟧ s] to [x↦1][y↦2]
    simp [Bexp_eval, Aexp_eval, Num_to_Z]
    apply big_step.while_true
    · -- ℬ⟦¬(x=1)⟧ s[y↦1] = true
      simp [Bexp_eval]
    · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[y↦1]⟩ →ₙₛ s'
      apply big_step.seq
      · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
        apply big_step.ass
        simp -- y * x = 3
        rfl
      · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
        apply big_step.ass
        simp -- x - 1 = 2
        rfl
    · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
      apply big_step.while_true
      · -- ℬ⟦¬(x=1)⟧ s[x↦2][y↦3] = true
        simp [Bexp_eval]
      · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[x↦2][y↦3]⟩ →ₙₛ s'
        apply big_step.seq
        · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
          apply big_step.ass
          simp -- y * x = 6
          rfl
        · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
          apply big_step.ass
          simp -- x - 1 = 1
          rfl
      · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
        -- Change default_state[x↦3][y↦1][y↦3][x↦2][y↦6][x↦1] to default_state[x↦1][y↦6]
        simp [assign_comm, assign_shadow]
        apply big_step.while_false
        · -- ℬ⟦¬(x=1)⟧ s[x↦1][y↦6] = false
          simp [Bexp_eval]

end example_2_2


section example_2_2

example :
  let S := Stmt.sequence
    (Stmt.ass "y" 1)
    (Stmt.loop
      (Bexp.not (Bexp.eq "x" 1))
      (Stmt.sequence
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
    rfl -- 𝒜⟦3⟧ s = 2 is true by definition
  · -- Right side: z := 3
    -- simplify [x↦𝒜⟦1⟧ s][y↦𝒜⟦2⟧ s[x↦𝒜⟦1⟧ s] to [x↦1][y↦2]
    simp [Bexp_eval, Aexp_eval, Num_to_Z]
    apply big_step.while_true
    · -- ℬ⟦¬(x=1)⟧ s[y↦1] = true
      simp [Bexp_eval]
    · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[y↦1]⟩ →ₙₛ s'
      apply big_step.seq
      · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
        apply big_step.ass
        simp -- y * x = 3
        rfl
      · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
        apply big_step.ass
        simp -- x - 1 = 2
        rfl
    · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
      apply big_step.while_true
      · -- ℬ⟦¬(x=1)⟧ s[x↦2][y↦3] = true
        simp [Bexp_eval]
      · -- ⟨y ":=" y ⋆ x ";" x ":=" x - 1, s[x↦2][y↦3]⟩ →ₙₛ s'
        apply big_step.seq
        · -- ⟨y ":=" y ⋆ x, s⟩ →ₙₛ s₁'
          apply big_step.ass
          simp -- y * x = 6
          rfl
        · -- ⟨x ":=" x - 1, s₁'⟩ →ₙₛ s'
          apply big_step.ass
          simp -- x - 1 = 1
          rfl
      · -- ⟨"while" ¬(x = 1) "do" y ":=" y * x ";" x ":=" x - 1, s'⟩ →ₙₛ s''
        -- Change default_state[x↦3][y↦1][y↦3][x↦2][y↦6][x↦1] to default_state[x↦1][y↦6]
        simp [assign_comm, assign_shadow]
        apply big_step.while_false
        · -- ℬ⟦¬(x=1)⟧ s[x↦1][y↦6] = false
          simp [Bexp_eval]

end example_2_2
