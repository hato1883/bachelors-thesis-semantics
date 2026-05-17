
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
def Var := String
deriving instance DecidableEq for Var

inductive Aexp where
  | num (n : Num)          -- a := n
  | var (x : Var)          -- a := x
  | add (a₁ a₂ : Aexp)     -- a := a₁ + a₂
  | mul (a₁ a₂ : Aexp)     -- a := a₁ ⋆ a₂
  | sub (a₁ a₂ : Aexp)     -- a := a₁ - a₂

-- === Arithmetic Expression Notation ===
-- Addition: a₁ ＋ a₂ (fullwidth plus U+FF0B)
infixl:65 " ＋ " => While.Aexp.add

-- Multiplication: a₁ ⋆ a₂ (star \star)
infixl:70 " ⋆ " => While.Aexp.mul

-- Subtraction: a₁ − a₂ (minus \minus)
infixl:65 " − " => While.Aexp.sub


inductive Bexp where
  | true                   -- b := true
  | false                  -- b := false
  | eq  (a₁ a₂ : Aexp)     -- b := a₁ = a₂
  | le  (a₁ a₂ : Aexp)     -- b := a₁ ≤ a₂
  | not (b₁ : Bexp)        -- b := ¬b₁
  | and (b₁ b₂ : Bexp)     -- b := b₁ ∧ b₂

-- === Boolean Expression Notation ===
-- Equality: a₁ ⩵ a₂ (equals with two dots \eqeq)
notation:50 a₁:51 " ⩵ " a₂:50 => While.Bexp.eq a₁ a₂

-- Less or equal: a₁ ⩽ a₂ (less or slanted equal U+2A7D)
notation:50 a₁:51 " ⩽ " a₂:50 => While.Bexp.le a₁ a₂

-- Not: ¬ b
prefix:75 "not " => While.Bexp.not

-- And: b₁ ∧ b₂
infixr:35 " and " => While.Bexp.and

-- true/false
notation "true" => While.Bexp.true
notation "false" => While.Bexp.false


inductive Stmt where
  | ass  (x : Var)  (a : Aexp)     -- S = n
  | skip                           -- S = x
  | composition        (S₁ S₂ : Stmt) -- S = S₁; S₂
  | if (b : Bexp) (S₁ S₂ : Stmt) -- S = if b then S₁ else S₂
  | while (b : Bexp) (S₁ : Stmt)    -- S = while b then S₁

-- === Notation for While Syntax ===
-- Sequence (composition): S₁ ; S₂
infixl:80 "; " => While.Stmt.composition

-- Assignment: x ≔ a (coloneqq, U+2254)
infixr:90 " :≡ " => While.Stmt.ass

-- Condition: if b then S₁ else S₂
notation "if " b:40 " then " S₁:40 " else " S₂:40 => While.Stmt.if b S₁ S₂

-- While loop: while b do S
notation "while " b:40 " then " S:40 => While.Stmt.while b S


/-=============================-/
-- Semantic Domains            --
/-=============================-/

def State := Var → ℤ -- Gives notation s x = n, where (s : State) (x : Var) (n : Num)

def default_state : State :=
  fun _ => 0

def update (s : State) (x : Var) (v : ℤ) : State :=
  fun (y: Var) => if y = x then v else s y

notation:max s "[" x "↦" v "]" => update s x v

inductive T where
  | tt
  | ff
  deriving DecidableEq

notation "tt" => T.tt
notation "ff" => T.ff

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

set_option quotPrecheck false in
set_option hygiene false in
notation "𝒩⟦" n "⟧" => Num_eval  n

def Num_eval : Num → ℤ
  | Num.zero    => 0
  | Num.one     => 1
  | Num.succ0 n => 2 * 𝒩⟦n⟧
  | Num.succ1 n => 2 * 𝒩⟦n⟧ + 1

set_option quotPrecheck false in
set_option hygiene false in
notation "𝓐⟦" a "⟧" s:max => Aexp_eval a s

def Aexp_eval : Aexp → (State → ℤ)
  | .num n, _ => 𝒩⟦n⟧
  | .var x, s => s x
  | a₁ + a₂, s => 𝓐⟦a₁⟧s + 𝓐⟦a₂⟧s
  | a₁ ⋆ a₂, s => 𝓐⟦a₁⟧s * 𝓐⟦a₂⟧s
  | a₁ − a₂, s => 𝓐⟦a₁⟧s - 𝓐⟦a₂⟧s


set_option quotPrecheck false in
set_option hygiene false in
notation "𝓑⟦" b "⟧" s:max => Bexp_eval b s

def Bexp_eval : Bexp → (State → T)
  | true, _  => tt
  | false, _ => ff
  | a₁ ⩵ a₂,   s  =>
    if  𝓐⟦a₁⟧s == 𝓐⟦a₂⟧s then tt
    else ff
    -- -- if  𝓐⟦a₁⟧s == 𝓐⟦a₂⟧s then true else false
    -- match decEq (𝓐⟦a₁⟧s) (𝓐⟦a₂⟧s) with
    --     | Decidable.isTrue  _h_eq  => tt   -- if 𝓐⟦a₁⟧s = 𝓐⟦a₂⟧s
    --     | Decidable.isFalse _h_neq => ff   -- if 𝓐⟦a₁⟧s ≠ 𝓐⟦a₂⟧s
  | a₁ ⩽ a₂,   s  =>
    if  𝓐⟦a₁⟧s ≤  𝓐⟦a₂⟧s then tt
    else ff
    -- -- if  𝓐⟦a₁⟧s ≤  𝓐⟦a₂⟧s then true else false
    -- match (inferInstance : Decidable (𝓐⟦a₁⟧s ≤ 𝓐⟦a₂⟧s)) with
    --     | Decidable.isTrue  _h_leq => tt   -- if 𝓐⟦a₁⟧s ≤ 𝓐⟦a₂⟧s
    --     | Decidable.isFalse _h_gt  => ff   -- if 𝓐⟦a₁⟧s > 𝓐⟦a₂⟧s
  | not b₁,    s =>
    if  𝓑⟦b₁⟧s = tt then ff
    else tt
    -- -- if ¬ 𝓑⟦b₁⟧s then true else false
    -- match 𝓑⟦b₁⟧s with
    --   | tt => ff      -- if B[|b|]s = tt
    --   | ff => tt      -- if B[|b|]s = ff
  | b₁ and b₂, s =>
    if  𝓑⟦b₁⟧s = tt ∧ 𝓑⟦b₂⟧s = tt then tt
    else ff
    -- -- if   𝓑⟦b₁⟧s ∧  𝓑⟦b₂⟧s then true else false
    -- match 𝓑⟦b₁⟧s, 𝓑⟦b₂⟧s with
    --   | tt, tt => tt  -- if B[|b1|]s = tt and B[|b2|]s = tt
    --   | ff, tt => ff  -- if B[|b1|]s = ff and B[|b2|]s = tt
    --   | tt, ff => ff  -- if B[|b1|]s = tt and B[|b2|]s = ff
    --   | ff, ff => ff  -- if B[|b1|]s = ff and B[|b2|]s = ff


/-=============================-/
-- Auxiliary Components       --
/-=============================-/

-- 1. If you update the same variable twice, only the last one matters.
@[simp]
theorem update_shadow (s : State) (x : Var) (z1 z2 : ℤ) :
  s[x ↦ z1][x ↦ z2] = s[x ↦ z2] := by
  apply funext
  intro v
  repeat rw [update]
  split_ifs
  · rfl
  · rfl

-- 2. If you update different variables, you can swap them to group them.
@[simp]
theorem update_comm (s : State) (x y : Var) (z1 z2 : ℤ) (h : x ≠ y) :
  s[x ↦ z1][y ↦ z2] = s[y ↦ z2][x ↦ z1] := by
  apply funext
  intro v
  repeat rw [update]
  split_ifs with h1 h2
  -- h1 : v = y
  -- h2 : v = x
  · show z2 = z1
    subst h1 h2
    contradiction
  · show z2 = z2
    rfl
  · show z1 = z1
    rfl
  · show s v = s v
    rfl

attribute [simp, reducible] Num_eval Aexp_eval Bexp_eval update


/-=============================-/
-- Lean 4 Helpers --
/-=============================-/

-- Make variables print as just the string
-- Unexpander for Var.mk (Antiquotation style)
section tmp
open Lean PrettyPrinter

@[app_unexpander update] def unexpandUpdate : Lean.PrettyPrinter.Unexpander
  | `($_ $s $x $z) => `($s[$x ↦ $z])
  | _ => throw ()

@[app_unexpander T.tt] def unexpandTT : Unexpander
  | `($_) => `(tt)

@[app_unexpander T.ff] def unexpandFF : Unexpander
  | `($_) => `(ff)

@[app_unexpander Stmt.ass] def unexpandAss : Unexpander
  | `($_ $x $a) => `($x  :≡  $a)
  | _ => throw ()

@[app_unexpander Stmt.skip] def unexpandSkip : Unexpander
  | `($_) => `(skip)

@[app_unexpander Stmt.composition] def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($_ $S1 $S2) => `($S1; $S2)
  | _ => throw ()

@[app_unexpander Stmt.if] def unexpandCond : Lean.PrettyPrinter.Unexpander
  | `($_ $b $S1 $S2) => `(ifₛ $b thenₛ $S1 elseₛ $S2)
  | _ => throw ()

@[app_unexpander Stmt.while] def unexpandLoop : Lean.PrettyPrinter.Unexpander
  | `($_ $b $S1) => `(whileₛ $b doₛ $S1)
  | _ => throw ()

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
  | `(_) => `(true)
  | _ => throw ()

@[app_unexpander Bexp.false] def unexpandBexpFalse : Unexpander
  | `(_) => `(false)
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
end tmp

end While
