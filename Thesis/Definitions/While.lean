
import Mathlib

namespace While

  variable (n n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ : Num)   --- n will range over numerals, Num.
  variable (x x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : Var)   --- x will range over variables, Var.
  variable (a a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Aexp)  --- a will range over arithmetic expressions, Aexp.
  variable (b b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : Bexp)  --- b will range over boolean expressions, Bexp.
  variable (S S₀ S₁ S₂ S₃ S₄ S₅ S₆ S₇ S₈ S₉ : Stmt)  --- S will range over statements, Stmt.
  variable (s s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : State) --- s will range over states, State.


  inductive Num where
    | zero : Num             -- 0
    | one  : Num             -- 1
    | succ0 (n : Num) : Num  -- n 0
    | succ1 (n : Num) : Num  -- n 1

  -- Helper: Converts a standard Nat to your bitvector Num
  @[reducible]
  def natToNum : Nat → Num
    | 0 => Num.zero
    | 1 => Num.one
    | n + 2 =>
      if (n + 2) % 2 == 0
      then Num.succ0 (natToNum ((n + 2) / 2))
      else Num.succ1 (natToNum ((n + 2) / 2))

  -- This instance allows you to use literals like '5' or '0b101' as Num
  instance (n : Nat) : OfNat Num n where
    ofNat := natToNum n

  -- TODO: change to inductive instead of def so that proof 1.5 is needed
  def Num_to_Z : Num → ℤ
    | Num.zero    => 0
    | Num.one     => 1
    | Num.succ0 n => 2 * (Num_to_Z n)
    | Num.succ1 n => 2 * (Num_to_Z n) + 1

  notation "𝒩⟦" n "⟧" => Num_to_Z  n


  /-- Variables are represented as strings of letters and digits -/
  structure Var where
    name : String
    deriving BEq, Hashable, Repr, DecidableEq

  instance : Coe String Var where
    coe s := ⟨s⟩


  /-- A State maps variables to their integer values -/
  def State := Var → ℤ -- Gives notation s x = n, where (s : State) (x : Var) (n : Num)

  def default_state : State := fun _ => 0

  def assign (s : State) (x : Var) (z : ℤ) : State :=
    fun (v: Var) => if v = x then z else s v

  -- This allows you to write: s[x ↦ z]
  notation:max s "[" x "↦" z "]" => assign s x z

  --- arithmetic expressions
  inductive Aexp where
    | num (n : Num)          -- a := n
    | var (x : Var)          -- a := x
    | add (a₁ a₂ : Aexp)     -- a := a₁ + a₂
    | mul (a₁ a₂ : Aexp)     -- a := a₁ ⋆ a₂
    | sub (a₁ a₂ : Aexp)     -- a := a₁ - a₂

  instance : Add Aexp where
    add := Aexp.add

  instance : Mul Aexp where
    mul := Aexp.mul

  instance : Sub Aexp where
    sub := Aexp.sub

  -- 1. Allow Strings to be treated as Aexp (via Var)
  instance : Coe String Aexp where
    coe s := Aexp.var ⟨s⟩

  instance (n : Nat) : OfNat Aexp n where
    ofNat := Aexp.num (OfNat.ofNat n)

  /-- Semantic function for arithmetic expressions -/
  -- TODO: change to inductive instead of def so that proof 1.8 is needed
  def Aexp_eval : Aexp → State → ℤ
    | Aexp.num n, _ => 𝒩⟦n⟧
    | Aexp.var x, s => s x
    | Aexp.add a₁ a₂, s => Aexp_eval a₁ s + Aexp_eval a₂ s
    | Aexp.mul a₁ a₂, s => Aexp_eval a₁ s * Aexp_eval a₂ s
    | Aexp.sub a₁ a₂, s => Aexp_eval a₁ s - Aexp_eval a₂ s

  -- Traditional notation 𝒜⟦a⟧s → ℤ
  notation "𝒜⟦" a "⟧" => Aexp_eval a


  --- boolean expressions
  inductive Bexp where
    | true                   -- b := true
    | false                  -- b := false
    | eq  (a₁ a₂ : Aexp)     -- b := a₁ = a₂
    | le  (a₁ a₂ : Aexp)     -- b := a₁ ≤ a₂
    | not (b₁ : Bexp)        -- b := ¬b₁
    | and (b₁ b₂ : Bexp)     -- b := b₁ ∧ b₂

  instance : Coe Bool Bexp where
    coe b := if b then Bexp.true else Bexp.false

  /-- Semantic function for boolean expressions -/
  -- TODO: change to inductive instead of def so that proof 1.8 is needed
  def Bexp_eval : Bexp → State → Bool
    | Bexp.true,      _ => true
    | Bexp.false,     _ => false
    | Bexp.eq  a₁ a₂, s => (Aexp_eval a₁ s) == (Aexp_eval a₂ s)
    | Bexp.le  a₁ a₂, s => (Aexp_eval a₁ s) ≤  (Aexp_eval a₂ s)
    | Bexp.not b₁,    s => ¬ (Bexp_eval b₁ s)
    | Bexp.and b₁ b₂, s => (Bexp_eval b₁ s) ∧  (Bexp_eval b₂ s)

  -- Traditional notation ℬ⟦b⟧s → Bool
  notation "ℬ⟦" b "⟧" => Bexp_eval b


  --- statements
  inductive Stmt where
    | ass  (x : Var)  (a : Aexp)     -- S = n
    | skip                           -- S = x
    | sequence        (S₁ S₂ : Stmt) -- S = S₁; S₂
    | cond (b : Bexp) (S₁ S₂ : Stmt) -- S = if b then S₁ else S₂
    | loop (b : Bexp) (S₁ : Stmt)    -- S = while b then S₁

  -- infixr:90 " := " => Stmt.ass
  -- infixl:80 " ; " => Stmt.sequence

  -- Make variables print as just the string
  -- Unexpander for Var.mk (Antiquotation style)
  section tmp
  open Lean PrettyPrinter
  @[app_unexpander Var.mk] def unexpandVar : Unexpander
    | `($_ $name) =>
      match name.raw.isStrLit? with
      | some s =>
        -- This turns the string "x" into the identifier x
        let id := mkIdent s.toName
        return id
      | none => throw ()
    | _ => throw ()

  -- Unexpander for State assignment
  @[app_unexpander assign] def unexpandAssign : Lean.PrettyPrinter.Unexpander
    | `($_ $s $x $z) => `($s[$x ↦ $z])
    | _ => throw ()

  -- Unexpander for Stmt.ass
  -- This adds the ":=" for assignment
  @[app_unexpander Stmt.ass] def unexpandAss : Unexpander
    | `($_ $x $a) => `($x ":=" $a)
    | _ => throw ()

  -- Unexpander for Stmt.sequence
  -- This adds the ";" and the parentheses for nesting
  @[app_unexpander Stmt.sequence] def unexpandSeq : Lean.PrettyPrinter.Unexpander
    | `($_ $S1 $S2) => `(($S1 ";" $S2))
    | _ => throw ()

  -- Unexpander for Stmt.cond
  -- This adds the "if then else"
  @[app_unexpander Stmt.cond] def unexpandCond : Lean.PrettyPrinter.Unexpander
    | `($_ $b $S1 $S2) => `("if" $b "then" $S1 "else" $S2)
    | _ => throw ()

  -- Unexpander for Stmt.loop
  -- This adds the "while then"
  @[app_unexpander Stmt.loop] def unexpandLoop : Lean.PrettyPrinter.Unexpander
    | `($_ $b $S1) => `("while" $b "do" $S1)
    | _ => throw ()
  end tmp

  -- 1. If you update the same variable twice, only the last one matters.
  @[simp] theorem assign_shadow (s : State) (x : Var) (z1 z2 : ℤ) :
    s[x ↦ z1][x ↦ z2] = s[x ↦ z2] := by
    apply funext
    intro v
    simp [assign]
    split_ifs <;> rfl

  -- 2. If you update different variables, you can swap them to group them.
  @[simp]theorem assign_comm (s : State) (x1 x2 : Var) (z1 z2 : ℤ) (h : x1 ≠ x2) :
  s[x1 ↦ z1][x2 ↦ z2] = s[x2 ↦ z2][x1 ↦ z1] := by
    apply funext
    intro v
    simp [assign]
    split_ifs with h1 h2 <;> try rfl
    -- Only the contradiction case remains
    subst h1 h2 -- changes goal from x1 != x2 to v != v
    contradiction

  attribute [simp, reducible] Num_to_Z Aexp_eval Bexp_eval assign

end While
