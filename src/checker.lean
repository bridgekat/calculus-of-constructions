import data.sum.basic
import lemmas

namespace coc
section

open expr
open ctx

open small
open small_star
open small_eq
open has_type

local notation e ` ⟦` n ` ↦ ` e' `⟧` := expr.subst e n e'
local notation e ` ⟦` n ` ↟ ` m `⟧`  := expr.shift e n m
local notation e ` ~>* ` e'          := small_star e e'
local notation e ` ~~ ` e'           := small_eq e e'
local notation Γ ` ▷ ` e ` : ` t     := has_type Γ e t

/-- Performs applicative-order beta-reduction.
    If the original expression is well-typed, the resulting expression will have the same type.
    Note that this function is only a syntactic operation, and does not check well-formedness.
    It does not terminate on inputs like `(fun x => x x x) (fun x => x x x)`. -/
meta def expr.reduce : Π (e : expr), Σ' (e' : expr), e ~>* e'
| (sort s)   := ⟨sort s, ss_refl⟩
| (var v)    := ⟨var v, ss_refl⟩
| (app l r)  :=
  let ⟨l', hl⟩ := expr.reduce l,
      ⟨r', hr⟩ := expr.reduce r in
    match l', hl with
    | (lam t e), hl' :=
      let ⟨e', he⟩ := expr.reduce (e ⟦0 ↦ r'⟧) in
        ⟨e', small_star_trans (ss_step (small_star_app hl' hr) s_beta) he⟩
    | _,         _   := ⟨app l' r', small_star_app hl hr⟩
    end
| (lam t e)  :=
  let ⟨t', ht⟩ := expr.reduce t,
      ⟨e', he⟩ := expr.reduce e in
  ⟨lam t' e', small_star_lam ht he⟩
| (pi t₁ t₂) :=
  let ⟨t₁', ht₁⟩ := expr.reduce t₁,
      ⟨t₂', ht₂⟩ := expr.reduce t₂ in
    ⟨pi t₁' t₂', small_star_pi ht₁ ht₂⟩

/- Some helper functions. -/

def expr.as_sort : Π (e : expr), string ⊕ Σ' (n : nat), e = sort n
| (sort s) := sum.inr ⟨s, rfl⟩
| e        := sum.inl $ "expression " ++ e.show ++ " is not a sort"

def expr.as_pi : Π (e : expr), string ⊕ Σ' (t₁ t₂ : expr), e = pi t₁ t₂
| (pi t₁ t₂) := sum.inr ⟨t₁, t₂, rfl⟩
| e          := sum.inl $ "expression " ++ e.show ++ " is not a function"

def ctx.try_nth : Π (Γ : ctx) (n : nat), string ⊕ Σ' (e : expr), list.nth Γ n = option.some e
| []       n       := sum.inl $ "variable index overflowed by " ++ to_string n
| (t :: Γ) 0       := sum.inr ⟨t, rfl⟩
| (t :: Γ) (n + 1) := ctx.try_nth Γ n

/-- Check if a preterm is a well-formed term.
    Returns its type and the corresponding proof on success.
    It should terminate on any input, but there is no proof yet. -/
meta def expr.check : Π (e : expr) (Γ : ctx), string ⊕ Σ' (t : expr), Γ ▷ e : t
| (sort s)   Γ := return ⟨sort (s + 1), t_sort⟩
| (var v)    Γ := do ⟨t, h⟩ <- Γ.try_nth v, return ⟨t.shift 0 v.succ, t_var h⟩
| (app l r)  Γ := do
  { ⟨tl, htl⟩     ← l.check Γ,
    ⟨t₁, t₂, htt⟩ ← tl.as_pi,
    ⟨tr, htr⟩     ← r.check Γ,
    let ⟨t₁', ht₁'⟩ := t₁.reduce,
    let ⟨tr', htr'⟩ := tr.reduce,
    dite (t₁' = tr')
      (λ heq, return ⟨t₂.subst 0 r, t_app (t_conv
        (small_eq_pi (small_eq_of_small_stars (heq ▸ ht₁' : t₁ ~>* tr') htr') se_refl)
        (htt ▸ htl : Γ ▷ l : pi t₁ t₂)) htr⟩)
      (λ _, sum.inl $ "argument type mismatch: " ++ t₁.show ++ " != " ++ tr.show) }
| (lam t e)  Γ := do
  { ⟨t₂, ht₂⟩     ← e.check (t :: Γ),
    ⟨t', ht'⟩     ← (pi t t₂).check Γ,
    ⟨s, hs⟩       ← t'.as_sort,
    return ⟨pi t t₂, t_lam (hs ▸ ht' : Γ ▷ pi t t₂ : sort s) ht₂⟩ }
| (pi t₁ t₂) Γ := do
  { ⟨t₁', ht₁'⟩   ← t₁.check Γ,
    ⟨s₁, hs₁⟩     ← t₁'.as_sort,
    ⟨t₂', ht₂'⟩   ← t₂.check (t₁ :: Γ),
    ⟨s₂, hs₂⟩     ← t₂'.as_sort,
    return ⟨sort (max s₁ s₂), t_pi (hs₁ ▸ ht₁') (hs₂ ▸ ht₂')⟩ }

end
end coc
