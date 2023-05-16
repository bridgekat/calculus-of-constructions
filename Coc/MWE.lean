import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

inductive Expr : Type
  | sort : Nat →         Expr
  | var  : Nat →         Expr
  | app  : Expr → Expr → Expr
  | lam  : Expr → Expr → Expr
  | pi   : Expr → Expr → Expr
deriving DecidableEq

def recursive : Nat → Nat → Nat → Nat
  | 0,     _, _ => 0
  | n + 1, m, k => recursive n (m + 1) k + 1

def Expr.shift : Expr → Nat → Nat → Expr
  | sort s,   _, _ => .sort s
  | var v,    n, m => if n <= v then .var (v + m) else .var v
  | app l r,  n, m => .app (Expr.shift l n m) (Expr.shift r n m)
  | lam t e,  n, m => .lam (Expr.shift t n m) (Expr.shift e (Nat.succ n) m)
  | pi t₁ t₂, n, m => .pi (Expr.shift t₁ n m) (Expr.shift t₂ (Nat.succ n) m)

open Expr
set_option pp.structureProjections false

-- notation e " ⟦" n:80 " ↦ " e':79 "⟧" => subst e n e'
notation e " ⟦" n:80 " ↟ " m:79 "⟧"  => shift e n m

theorem shift_le {v n m} (h : n ≤ v) : (var v) ⟦n ↟ m⟧ = var (v + m) := by
  unfold shift; split_ifs; eq_refl
