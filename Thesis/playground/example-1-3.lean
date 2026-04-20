import Thesis.Definitions.While
open While

section part_1_3

theorem n_total_mapping_z (n : While.Num) : ∃! (z : ℤ), 𝒩⟦n⟧ = z := by
  induction n with
  | zero =>
    rw [While.Num_to_Z]
    refine ⟨0, ?existence, ?uniqueness⟩
    case existence =>
      show 0 = 0
      rfl
    case uniqueness =>
      intro y hy
      symm
      exact hy
  | one =>
    rw [While.Num_to_Z]
    refine ⟨1, ?existence, ?uniqueness⟩
    case existence =>
      show 1 = 1
      rfl
    case uniqueness =>
      intro y hy
      symm
      exact hy
  | succ0 d hd =>
    rw [While.Num_to_Z]
    obtain ⟨z_d, h_prop, h_unique⟩ := hd
    refine ⟨2 * z_d, ?existence, ?uniqueness⟩
    case existence =>
      show 2 * 𝒩⟦d⟧ = 2 * z_d
      simp -- changes to ....
      exact h_prop
    case uniqueness =>
      intro y hy
      symm
      rw [h_prop] at hy
      exact hy
  | succ1 d hd =>
    rw [While.Num_to_Z]
    obtain ⟨z_d, h_prop, h_unique⟩ := hd
    refine ⟨2 * z_d + 1, ?existence, ?uniqueness⟩
    case existence =>
      show 2 * 𝒩⟦d⟧ + 1 = 2 * z_d + 1
      simp
      exact h_prop
    case uniqueness =>
      intro y hy
      symm
      rw [h_prop] at hy
      exact hy

end part_1_3

section part_1_6

  def s : State := default_state["x"↦3]
  #check 𝓐⟦"x" + 1⟧
  #eval 𝓐⟦"x" + 1⟧ s

end part_1_6


section part_1_8

  theorem aexp_total_mapping_z (a : Aexp) (s : State) : ∃! (z : ℤ), 𝓐⟦a⟧ s = z :=
    by sorry

end part_1_8
