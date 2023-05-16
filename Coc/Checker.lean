import data.sum.basic
import lemmas

namespace coc
section

open expr
open ctx
open small
open small_star
open defeq
open judgment_index
open judgment

set_option pp.beta true
set_option pp.structure_projections false

local notation e ` ⟦`:80 n:80 ` ↦ `:80 e':79 `⟧`:79 := subst e n e'
local notation e ` ⟦`:80 n:80 ` ↟ `:80 m:79 `⟧`:79  := shift e n m
local notation e ` ~> `:50 e':50                    := small e e'
local notation e ` ~>* `:50 e':50                   := small_star e e'
local notation e ` ~~ `:50 e':50                    := defeq e e'
local notation `▷ `:50 Γ:50                         := judgment (well_ctx Γ )
local notation Γ ` ▷ `:50 e:50 ` : `:50 t:50        := judgment (has_type Γ e t)

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
        ⟨e', small_star_trans (ss_step (app_small_star_aux hl' hr) s_beta) he⟩
    | _,         _   := ⟨app l' r', app_small_star_aux hl hr⟩
    end
| (lam t e)  :=
  let ⟨t', ht⟩ := expr.reduce t,
      ⟨e', he⟩ := expr.reduce e in
  ⟨lam t' e', lam_small_star_aux ht he⟩
| (pi t₁ t₂) :=
  let ⟨t₁', ht₁⟩ := expr.reduce t₁,
      ⟨t₂', ht₂⟩ := expr.reduce t₂ in
    ⟨pi t₁' t₂', pi_small_star_aux ht₁ ht₂⟩

/- Helper functions and auxiliary lemmas. -/

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

lemma expr.check_aux_1
  {Γ l tl} (htl : Γ ▷ l : tl) {t₁ t₂} (htt : tl = pi t₁ t₂) {r tr} (htr : Γ ▷ r : tr)
  {t₁'} (ht₁' : t₁ ~>* t₁') {tr'} (htr' : tr ~>* tr') (he : t₁' = tr') :
  (Γ ▷ app l r : t₂ ⟦0 ↦ r⟧) := by
{ substs htt he,
  have h₁ := has_type_conv_small_star htl (pi_small_star_aux ht₁' ss_refl),
  have h₂ := has_type_conv_small_star htr htr',
  exact t_app h₁ h₂ }

lemma expr.check_aux_2
  {Γ t t'} (ht' : Γ ▷ t : t') {s} (hs : t' = sort s) {e t₂} (ht₂ : t :: Γ ▷ e : t₂) :
  (Γ ▷ lam t e : pi t t₂) := by
{ subst hs,
  obtain ⟨s₂, hs₂⟩ := type_has_sort ht₂,
  exact t_lam (t_pi ht' hs₂) ht₂ }

/-- Check if a preterm is a well-formed term.
    Returns its type and the corresponding proof on success.
    It should terminate on any input, but there is no proof yet. -/
meta def expr.check : Π (e : expr) (Γ : ctx), ▷ Γ → string ⊕ Σ' (t : expr), Γ ▷ e : t
| (sort s)   Γ hw := return ⟨sort (s + 1), t_sort hw⟩
| (var v)    Γ hw := do ⟨t, h⟩ <- Γ.try_nth v, return ⟨t.shift 0 v.succ, t_var hw h⟩
| (app l r)  Γ hw := do
  { ⟨tl, htl⟩     ← l.check Γ hw,
    ⟨t₁, t₂, htt⟩ ← tl.as_pi,
    ⟨tr, htr⟩     ← r.check Γ hw,
    let ⟨t₁', ht₁'⟩ := t₁.reduce,
    let ⟨tr', htr'⟩ := tr.reduce,
    dite (t₁' = tr')
      (λ he, return ⟨t₂ ⟦0 ↦ r⟧, expr.check_aux_1 htl htt htr ht₁' htr' he⟩)
      (λ _, sum.inl $ "argument type mismatch: " ++ t₁.show ++ " != " ++ tr.show) }
| (lam t e)  Γ hw := do
  { ⟨t', ht'⟩     ← t.check Γ hw,
    ⟨s, hs⟩       ← t'.as_sort,
    ⟨t₂, ht₂⟩     ← e.check (t :: Γ) (c_cons (hs ▸ ht' : Γ ▷ t : sort s)),
    return ⟨pi t t₂, expr.check_aux_2 ht' hs ht₂⟩ }
| (pi t₁ t₂) Γ hw := do
  { ⟨t₁', ht₁'⟩   ← t₁.check Γ hw,
    ⟨s₁, hs₁⟩     ← t₁'.as_sort,
    ⟨t₂', ht₂'⟩   ← t₂.check (t₁ :: Γ) (c_cons (hs₁ ▸ ht₁' : Γ ▷ t₁ : sort s₁)),
    ⟨s₂, hs₂⟩     ← t₂'.as_sort,
    return ⟨sort (max s₁ s₂), t_pi (hs₁ ▸ ht₁') (hs₂ ▸ ht₂')⟩ }

/-- Check if a precontext is a well-formed context.
    Returns a proof on success. -/
meta def ctx.check : Π (Γ : ctx), string ⊕ Σ' (_ : unit), ▷ Γ
| []       := return ⟨(), c_nil⟩
| (t :: Γ) := do
  { ⟨_, hw⟩   ← ctx.check Γ,
    ⟨t', ht'⟩ ← t.check Γ hw,
    ⟨s, hs⟩   ← t'.as_sort,
    return ⟨(), c_cons (hs ▸ ht' : Γ ▷ t : sort s)⟩ }

end
end coc
