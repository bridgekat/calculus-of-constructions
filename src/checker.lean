import data.sum.basic
import expr

namespace coc

open expr
open ctx

def expr.as_sort : expr → string ⊕ nat
| (sort s) := sum.inr s
| e        := sum.inl $ "expression " ++ e.show ++ " is not a sort"

def expr.as_pi : expr → string ⊕ (expr × expr)
| (pi t₁ t₂) := sum.inr (t₁, t₂)
| e          := sum.inl $ "expression " ++ e.show ++ " is not a function"

def ctx.try_nth : ctx → nat → string ⊕ expr
| []       n       := sum.inl $ "variable index overflowed by " ++ to_string n
| (t :: Γ) 0       := sum.inr t
| (t :: Γ) (n + 1) := ctx.try_nth Γ n

/-- Check if a preterm is a well-formed term (1), type (2), proof (3) or formula (4).
    (1) Returns a well-formed expression of type `sort (n + 1)`, representing the type of the term;
    (2) Returns `sort (n + 1)` itself;
    (3) Returns a well-formed expression of type `sort 0`, representing the proposition it proves;
    (4) Returns `sort 0` itself. -/
meta def expr.check : expr → Π (Γ : ctx), string ⊕ expr
| (sort s)    Γ := return (sort (s + 1))
| (var v)     Γ := do t <- Γ.try_nth v, return (t.shift 0 v.succ)
| (app l r)   Γ := do
  { tl        ← l.check Γ,
    ⟨t₁, t₂⟩  ← tl.as_pi,
    tr        ← r.check Γ,
    if t₁.reduce = tr.reduce
    then return (t₂.subst 0 r)
    else sum.inl $ "argument type mismatch: " ++ t₁.show ++ " != " ++ tr.show }
| (lam t e)   Γ := do
  { t'        ← t.check Γ,
    _         ← t'.as_sort,
    t₂        ← e.check (t :: Γ),
    return (pi t t₂) }
| (pi t₁ t₂)  Γ := do
  { t₁'       ← t₁.check Γ,
    s₁        ← t₁'.as_sort,
    t₂'       ← t₂.check (t₁ :: Γ),
    s₂        ← t₂'.as_sort,
    return (sort (max s₁ s₂)) }

end coc
