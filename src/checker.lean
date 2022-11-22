import data.sum.basic
import expr

namespace coc

open idx
open expr
open ctx

def expr.imax : nat → nat → nat
| 0 _ := 0
| _ 0 := 0
| a b := max a b

def expr.as_sort : expr → string ⊕ nat
| (sort s) := sum.inr s
| e        := sum.inl $ "expression " ++ e.show ++ " is not a sort"

def expr.as_pi : expr → string ⊕ (expr × expr)
| (pi t₁ t₂) := sum.inr (t₁, t₂)
| e          := sum.inl $ "expression " ++ e.show ++ " is not a function"

def ctx.length : ctx → nat
| nil        := nat.zero
| (cons _ Γ) := nat.succ (ctx.length Γ)

def ctx.nth : ctx → nat → string ⊕ expr
| nil        _       := sum.inl "undefined variable"
| (cons t Γ) 0       := sum.inr t
| (cons t Γ) (n + 1) := ctx.nth Γ n

/-- Check if a preterm is a well-formed term (1), type (2), proof (3) or formula (4).
    (1) Returns a well-formed expression of type `sort (n + 1)`, representing the type of the term;
    (2) Returns `sort (n + 1)` itself;
    (3) Returns a well-formed expression of type `sort 0`, representing the proposition it proves;
    (4) Returns `sort 0` itself. -/
meta def expr.check_rec : expr → Π (Γ Δ : ctx), string ⊕ expr
| (sort s)        Γ Δ := return (sort (s + 1))
| (var (bound b)) Γ Δ := Δ.nth b
| (var (free f))  Γ Δ := Γ.nth (Γ.length - 1 - f)
| (app l r)   Γ Δ := do
  { tl        ← l.check_rec Γ Δ,
    ⟨t₁, t₂⟩  ← tl.as_pi,
    tr        ← r.check_rec Γ Δ,
    if t₁.reduce = tr.reduce
    then return (t₂.make_replace r)
    else sum.inl $ "argument type mismatch: " ++ t₁.show ++ " != " ++ tr.show }
| (lam t e)   Γ Δ := do
  { t'        ← t.check_rec Γ Δ,
    _         ← t'.as_sort,
    t₂        ← e.check_rec Γ (cons t Δ),
    return (pi t t₂) }
| (pi t₁ t₂)  Γ Δ := do
  { t'        ← t₁.check_rec Γ Δ,
    s₁        ← t'.as_sort,
    t''       ← t₂.check_rec Γ (cons t₁ Δ),
    s₂        ← t''.as_sort,
    return (sort (expr.imax s₁ s₂)) }

meta def expr.check (e : expr) (Γ : ctx) : string ⊕ expr :=
  e.check_rec Γ nil

end coc
