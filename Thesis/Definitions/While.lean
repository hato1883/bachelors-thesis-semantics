
import Mathlib

namespace While

/-=============================-/
-- Syntactic Categories        --
/-=============================-/

inductive Num where
  | zero : Num             -- 0
  | one  : Num             -- 1
  | succ0 (n : Num) : Num  -- n 0
  | succ1 (n : Num) : Num  -- n 1

/-- Variables are represented as strings of letters and digits -/
structure Var where
  name : String
  deriving BEq, Hashable, Repr, DecidableEq

inductive Aexp where
  | num (n : Num)          -- a := n
  | var (x : Var)          -- a := x
  | add (a₁ a₂ : Aexp)     -- a := a₁ + a₂
  | mul (a₁ a₂ : Aexp)     -- a := a₁ ⋆ a₂
  | sub (a₁ a₂ : Aexp)     -- a := a₁ - a₂

inductive Bexp where
  | true                   -- b := true
  | false                  -- b := false
  | eq  (a₁ a₂ : Aexp)     -- b := a₁ = a₂
  | le  (a₁ a₂ : Aexp)     -- b := a₁ ≤ a₂
  | not (b₁ : Bexp)        -- b := ¬b₁
  | and (b₁ b₂ : Bexp)     -- b := b₁ ∧ b₂

inductive Stmt where
  | ass  (x : Var)  (a : Aexp)     -- S = n
  | skip                           -- S = x
  | sequence        (S₁ S₂ : Stmt) -- S = S₁; S₂
  | cond (b : Bexp) (S₁ S₂ : Stmt) -- S = if b then S₁ else S₂
  | loop (b : Bexp) (S₁ : Stmt)    -- S = while b then S₁


/-=============================-/
-- Semantic Domains            --
/-=============================-/

def State := Var → ℤ -- Gives notation s x = n, where (s : State) (x : Var) (n : Num)

def default_state : State := fun _ => 0


/-=============================-/
-- Semantic Functions         --
/-=============================-/

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

-- 1. Allow Strings to be treated as Aexp (via Var)
instance : Coe String Var where
  coe s := ⟨s⟩

instance : Coe String Aexp where
  coe s := Aexp.var ⟨s⟩

instance (n : Nat) : OfNat Aexp n where
  ofNat := Aexp.num (OfNat.ofNat n)

instance : Add Aexp where
  add := Aexp.add

instance : Mul Aexp where
  mul := Aexp.mul

instance : Sub Aexp where
  sub := Aexp.sub

instance : Coe Bool Bexp where
  coe b := if b then Bexp.true else Bexp.false


/-=============================-/
-- Semantic Equations         --
/-=============================-/

-- TODO: change to inductive instead of def so that proof 1.5 is needed
def Num_to_Z : Num → ℤ
  | Num.zero    => 0
  | Num.one     => 1
  | Num.succ0 n => 2 * (Num_to_Z n)
  | Num.succ1 n => 2 * (Num_to_Z n) + 1

notation "𝒩⟦" n "⟧" => Num_to_Z  n

-- TODO: change to inductive instead of def so that proof 1.8 is needed
def Aexp_eval : Aexp → State → ℤ
  | Aexp.num n, _ => 𝒩⟦n⟧
  | Aexp.var x, s => s x
  | Aexp.add a₁ a₂, s => Aexp_eval a₁ s + Aexp_eval a₂ s
  | Aexp.mul a₁ a₂, s => Aexp_eval a₁ s * Aexp_eval a₂ s
  | Aexp.sub a₁ a₂, s => Aexp_eval a₁ s - Aexp_eval a₂ s

notation "𝒜⟦" a "⟧" => Aexp_eval a

-- TODO: change to inductive instead of def so that proof 1.8 is needed
def Bexp_eval : Bexp → State → Bool
  | Bexp.true,      _ => true
  | Bexp.false,     _ => false
  | Bexp.eq  a₁ a₂, s => (Aexp_eval a₁ s) == (Aexp_eval a₂ s)
  | Bexp.le  a₁ a₂, s => (Aexp_eval a₁ s) ≤  (Aexp_eval a₂ s)
  | Bexp.not b₁,    s => ¬ (Bexp_eval b₁ s)
  | Bexp.and b₁ b₂, s => (Bexp_eval b₁ s) ∧  (Bexp_eval b₂ s)

notation "ℬ⟦" b "⟧" => Bexp_eval b

def assign (s : State) (x : Var) (z : ℤ) : State :=
  fun (v: Var) => if v = x then z else s v

notation:max s "[" x "↦" z "]" => assign s x z


/-=============================-/
-- Auxiliary Components       --
/-=============================-/

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


/-=============================-/
-- Notation & Lean 4 Helpers --
/-=============================-/

-- === Notation for While Syntax ===

-- Sequence (composition): S₁ ; S₂
infixl:80 "; " => While.Stmt.sequence

-- Assignment: x ≔ a (coloneqq, U+2254)
infixr:90 " :≡ " => While.Stmt.ass

-- Condition: if b then S₁ else S₂
notation "if " b:40 " then " S₁:40 " else " S₂:40 => While.Stmt.cond b S₁ S₂

-- While loop: while b do S
notation "while " b:40 " do " S:40 => While.Stmt.loop b S

-- === Arithmetic Expression Notation ===

-- Addition: a₁ ＋ a₂ (fullwidth plus U+FF0B)
infixl:65 " ＋ " => While.Aexp.add

-- Multiplication: a₁ ⋆ a₂ (star \star)
infixl:70 " ⋆ " => While.Aexp.mul

-- Subtraction: a₁ − a₂ (minus \minus)
infixl:65 " − " => While.Aexp.sub

-- === Boolean Expression Notation ===

-- Equality: a₁ ⩵ a₂ (equals with two dots U+2A75)
notation:50 a₁:51 " ⩵ " a₂:50 => While.Bexp.eq a₁ a₂

-- Less or equal: a₁ ⩽ a₂ (less or slanted equal U+2A7D)
notation:50 a₁:51 " ⩽ " a₂:50 => While.Bexp.le a₁ a₂

-- Not: ¬ b
prefix:75 "¬ " => While.Bexp.not

-- And: b₁ ∧ b₂
infixr:70 " ∧ " => While.Bexp.and

-- true/false
notation "𝕋" => While.Bexp.true
notation "𝔽" => While.Bexp.false

-- === End While Notation ===

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

@[app_unexpander assign] def unexpandAssign : Lean.PrettyPrinter.Unexpander
  | `($_ $s $x $z) => `($s[$x ↦ $z])
  | _ => throw ()

@[app_unexpander Stmt.ass] def unexpandAss : Unexpander
  | `($_ $x $a) => `($x  :≡  $a)
  | _ => throw ()

@[app_unexpander Stmt.skip] def unexpandSkip : Unexpander
  | `($_) => `(skip)

@[app_unexpander Aexp.num] def unexpandAexpNum : Unexpander
  | `($_ $n) => `($n)
  | _ => throw ()

@[app_unexpander Aexp.var] def unexpandAexpVar : Unexpander
  | `($_ $x) => `($x)
  | _ => throw ()

@[app_unexpander Aexp.add] def unexpandAexpAdd : Unexpander
  | `($_ $a₁ $a₂) => `($a₁  ＋  $a₂)
  | _ => throw ()

@[app_unexpander Aexp.mul] def unexpandAexpMul : Unexpander
  | `($_ $a₁ $a₂) => `($a₁  ⋆  $a₂)
  | _ => throw ()

@[app_unexpander Aexp.sub] def unexpandAexpSub : Unexpander
  | `($_ $a₁ $a₂) => `($a₁  −  $a₂)
  | _ => throw ()

@[app_unexpander Bexp.true] def unexpandBexpTrue : Unexpander
  | `(_) => `(𝕋)
  | _ => throw ()

@[app_unexpander Bexp.false] def unexpandBexpFalse : Unexpander
  | `(_) => `(𝔽)
  | _ => throw ()

@[app_unexpander Bexp.eq] def unexpandBexpEq : Unexpander
  | `($_ $a₁ $a₂) => `($a₁  ⩵  $a₂)
  | _ => throw ()

@[app_unexpander Bexp.le] def unexpandBexpLe : Unexpander
  | `($_ $a₁ $a₂) => `($a₁  ⩽  $a₂)
  | _ => throw ()

@[app_unexpander Bexp.not] def unexpandBexpNot : Unexpander
  | `($_ $b₁) => `(¬ $b₁)
  | _ => throw ()

@[app_unexpander Bexp.and] def unexpandBexpAnd : Unexpander
  | `($_ $b₁ $b₂) => `($b₁  ∧  $b₂)
  | _ => throw ()

@[app_unexpander Num.zero] def unexpandNumZero : Unexpander
  | `(_) => `(0)
  | _ => throw ()

@[app_unexpander Num.one] def unexpandNumOne : Unexpander
  | `(_) => `(1)
  | _ => throw ()

@[app_unexpander Stmt.sequence] def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($_ $S1 $S2) => `($S1 ; $S2)
  | _ => throw ()

@[app_unexpander Stmt.cond] def unexpandCond : Lean.PrettyPrinter.Unexpander
  | `($_ $b $S1 $S2) => `(ifₛ $b thenₛ $S1 elseₛ $S2)
  | _ => throw ()

@[app_unexpander Stmt.loop] def unexpandLoop : Lean.PrettyPrinter.Unexpander
  | `($_ $b $S1) => `(whileₛ $b doₛ $S1)
  | _ => throw ()
end tmp

-- Variables for convenience (optional, can be removed if not needed)
variable (n n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ : Num)
variable (x x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : Var)
variable (a a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Aexp)
variable (b b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : Bexp)
variable (S S₀ S₁ S₂ S₃ S₄ S₅ S₆ S₇ S₈ S₉ : Stmt)
variable (s s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : State)

end While
