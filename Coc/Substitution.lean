import Mathlib.Tactic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Coc.Defs

namespace Coc
section

mutual
inductive Subs where
  | id : Subs
  | shift : Subs
  | cons : ES → Subs → Subs
  | comp : Subs → Subs → Subs

inductive ES where
  | sort : Nat →       ES
  | var  : Nat →       ES
  | app  : ES → ES →   ES
  | lam  : ES → ES →   ES
  | pi   : ES → ES →   ES
  | subs : ES → Subs → ES
end

-- TODO: mutual recursion and termination proof
def simplify : ES → ES
  | .subs (.sort s) _   => .sort s
  | .subs (.var 0)        (.cons h _) => h
  | .subs (.var (n + 1))  (.cons _ t) => simplify (.subs (.var n) t)
  | .subs (.var n) σ    => .subs (.var n) σ -- TODO
  | .subs (.app s t) σ  => simplify (.app (.subs s σ) (.subs t σ))
  | .subs (.lam t e) σ  => .lam (simplify (.subs t σ)) (.subs e (.cons (.var 0) (.comp σ .shift)))
  | .subs (.pi t₁ t₂) σ => .pi (simplify (.subs t₁ σ)) (.subs t₂ (.cons (.var 0) (.comp σ .shift)))
  | .subs (.subs e τ) σ => simplify (.subs e (.comp τ σ))
  | e                   => e -- TODO
termination_by _ e => e

end
end Coc
