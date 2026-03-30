import Mathlib

section question_1

  inductive Person where
    -- left blank

  def is_scrub (p : Person) : Bool := sorry

  def tlc_members : Set Person := sorry

  def can_get_love_from (p1 p2 : Person) : Bool := sorry

  def no_scrubs : Prop :=
    ∀ p t, t ∈ tlc_members ∧ is_scrub p → ¬ can_get_love_from t p

end question_1

section question_2

  inductive Player where
    -- left blank

  inductive Ball where
    -- left blank

  def players : Set Player := sorry

  def team_1 (p : Player) : Bool := sorry
  def team_2 (p : Player) : Bool := ¬ team_1 p

  def is_goal_keeper (p : Player) : Bool := sorry

  def past_halfway (p : Player) : Bool := sorry

  def p_dist_to_goal (p : Player) : Nat := sorry
  def b_dist_to_goal (p : Ball) : Nat := sorry

  -- (a) in the opponents’ half of the pitch;
  def in_opponent_half (p : Player) : Bool :=
    (team_1 p ∧ past_halfway p)
      ∨
    (team_2 p ∧ ¬ past_halfway p)

  -- (b) closer to the opponents’ goal than the ball is
  def is_closer_than_ball (b : Ball) (p : Player) : Bool :=
    (team_1 p ∧ (p_dist_to_goal p < b_dist_to_goal b))
      ∨
    (team_2 p ∧ (p_dist_to_goal p > b_dist_to_goal b))

  -- (c) closer to the opponents’ goal than the second-closest opponent
  def is_second_closest_player (p : Player) : Prop :=
    (team_1 p ∧ (∀ e : {n : players | team_2 n ∧ ¬ is_goal_keeper n}, (p_dist_to_goal p < p_dist_to_goal e)))
      ∨
    (team_2 p ∧ (∀ e : {n : players | team_1 n ∧ ¬ is_goal_keeper n}, (p_dist_to_goal p > p_dist_to_goal e)))

  def offside {b : Ball} (p : Player) : Prop :=
    in_opponent_half p
      ∧
    ( is_closer_than_ball b p ∧ is_second_closest_player p)

end question_2

section question_3

  variable (A B C : Prop)

  theorem conj_distrib_disj : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := by
    constructor
    -- Forward direction: A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
    · intro h
      have hA : A := h.left
      have hBC : B ∨ C := h.right
      cases hBC with
      | inl hB =>
          apply Or.inl
          exact ⟨hA, hB⟩
      | inr hC =>
          apply Or.inr
          exact ⟨hA, hC⟩

    -- Backward direction: (A ∧ B) ∨ (A ∧ C) → A ∧ (B ∨ C)
    · intro h
      cases h with
      | inl hAB =>
          have hA : A := hAB.left
          have hB : B := hAB.right
          exact ⟨hA, Or.inl hB⟩
      | inr hAC =>
          have hA : A := hAC.left
          have hC : C := hAC.right
          exact ⟨hA, Or.inr hC⟩

end question_3

section question_4

  variable (n : Nat)

  theorem divisable_by_six (n : ℕ) : ∃ k : ℕ, n^3 + 11 * n = 6 * k := by
    induction n with
    | zero =>
        use 0
        simp
    | succ n ih =>
        rcases ih with ⟨k, hk⟩
        rcases Nat.even_mul_succ_self n with ⟨t, ht⟩
        refine ⟨k + t + 2, ?_⟩
        calc
              (n + 1)^3 + 11 * (n + 1)
            = (n^3 + 11 * n) + 3 * (n * (n + 1)) + 12 :=  by ring
          _ = 6 * k          + 3 * (2 * t)       + 12 :=  by rw [hk, ht, ← Nat.two_mul t]
          _ = 6 * (k + t + 2) :=                          by ring

end question_4
