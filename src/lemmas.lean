import tactic
import expr

namespace coc
section

set_option pp.structure_projections false

open option
open idx
open expr

local notation e `⟦` r `/$⟧`    := subs e 0 r
local notation e ` ~> ` e'      := small e e'
local notation e ` ~>* ` e'     := small_star e e'
local notation Γ ` ⊢ ` e `: ` t := has_type Γ e t
local notation `⊢ ` Γ           := ctx_wf Γ

namespace closed

  /-- Lemmas for `closed e n`: `e` has at most `n` levels of unbound variables. -/
  lemma c_sort (s n)                                                  : closed (sort s) n        := trivial
  lemma c_bound {b n} (h : b < n)                                     : closed (var (bound b)) n := h
  lemma c_free (f n)                                                  : closed (var (free f)) n  := trivial
  lemma c_app {l r n} (hcl : closed l n) (hcr : closed r n)           : closed (app l r) n       := ⟨hcl, hcr⟩
  lemma c_lam {t e n} (hct : closed t n) (hce : closed e n.succ)      : closed (lam t e) n       := ⟨hct, hce⟩
  lemma c_pi {t₁ t₂ n} (hct₁ : closed t₁ n) (hct₂ : closed t₂ n.succ) : closed (pi t₁ t₂) n      := ⟨hct₁, hct₂⟩

  lemma c_weaken {e n n'} (hce : closed e n) (h : n <= n') : closed e n' :=
    @expr.rec (λ e, ∀ n n', n ≤ n' → closed e n → closed e n')
      (λ _ _ _ _ _, c_sort _ _)
      (λ v _ _ h,
        match v with
        | (bound b) := λ hcb, c_bound (nat.lt_of_lt_of_le hcb h)
        | (free f) := λ hcf, c_free _ _
        end)
      (λ _ _ hl hr _ _ h ⟨hcl, hcr⟩, ⟨hl _ _ h hcl, hr _ _ h hcr⟩)
      (λ _ _ ht he _ _ h ⟨hct, hce⟩, ⟨ht _ _ h hct, he _ _ (nat.succ_le_succ h) hce⟩)
      (λ _ _ ht₁ ht₂ _ _ h ⟨hct₁, hct₂⟩, ⟨ht₁ _ _ h hct₁, ht₂ _ _ (nat.succ_le_succ h) hct₂⟩)
      e n n' h hce

  lemma c_weaken₁ {e n} (hce : closed e n) : closed e n.succ :=
    c_weaken hce (nat.le_succ n)

end closed
open closed

/-- Substitution at the topmost level "closes" that level of unbound variables. -/
lemma subs.close {e e'} {n : nat} :
  closed e n.succ → closed e' n → closed (subs e n e') n := by
{ intros hce hce',
  induction e generalizing n,
  case sort : s { unfold subs },
  case var : v
  { unfold subs,
    cases v with b f,
    { change b < n.succ at hce,
      split_ifs with hif; injections; contradiction <|> skip,
      exact nat.lt_of_le_and_ne (nat.le_of_lt_succ hce) h, },
    { split_ifs; injections } },
  case app : l r hl hr { unfold subs, exact c_app (hl hce.1 hce') (hr hce.2 hce') },
  case lam : t e ht he { unfold subs, exact c_lam (ht hce.1 hce') (he hce.2 (c_weaken₁ hce')) },
  case pi : t₁ t₂ ht₁ ht₂ { unfold subs, exact c_lam (ht₁ hce.1 hce') (ht₂ hce.2 (c_weaken₁ hce')) } }

/-- Substitution at the topmost level 0 makes the term closed. -/
lemma subs.close₀ {e e'} : closed e 1 → closed e' 0 → closed (subs e 0 e') 0 :=
  subs.close

/-- `red1 e₁ e₂`: `e₁` reduces to `e₂` by contracting zero or more immediate, disjoint redexes. -/
inductive red1 : expr → expr → Prop
| r1_beta {t e r}         : red1 (app (lam t e) r) (e.subs 0 r)
| r1_sort (s)             :                             red1 (sort s) (sort s)
| r1_var  (v)             :                             red1 (var v) (var v)
| r1_app  {l l' r r'}     : red1 l l' → red1 r r' →     red1 (app l r) (app l' r')
| r1_lam  {t t' e e'}     : red1 t t' → red1 e e' →     red1 (lam t e) (lam t' e')
| r1_pi   {t₁ t₁' t₂ t₂'} : red1 t₁ t₁' → red1 t₂ t₂' → red1 (pi t₁ t₂) (pi t₁' t₂')
open red1

local notation e ` ~>₁ ` e' := red1 e e'

lemma red1.refl (e : expr) : e ~>₁ e :=
  @expr.rec_on (λ e, e ~>₁ e) e
    r1_sort r1_var (λ _ _, r1_app) (λ _ _, r1_lam) (λ _ _, r1_pi)

lemma red1.of_red1_left_rep
  {e e' e₁ : expr}
  (hce : closed e 0) (hce' : closed e' 0) (hce₁ : closed e₁ 0)
  (h : e ~>₁ e') :
  e⟦e₁/$⟧ ~>₁ e'⟦e₁/$⟧ := by
{ induction h,
  case r1_beta : t e r
  {  },
  case r1_sort : h
  { admit },
  case r1_var : h
  { admit },
  case r1_app : h_l h_l' h_r h_r' h_ᾰ h_ᾰ_1 h_ih_ᾰ h_ih_ᾰ_1
  { admit },
  case r1_lam : h_t h_t' h_e h_e' h_ᾰ h_ᾰ_1 h_ih_ᾰ h_ih_ᾰ_1
  { admit },
  case r1_pi : h_t₁ h_t₁' h_t₂ h_t₂' h_ᾰ h_ᾰ_1 h_ih_ᾰ h_ih_ᾰ_1
  { admit }}

lemma red1.confluent {e e₁ e₂ : expr} (h₁ : e ~>₁ e₁) (h₂ : e ~>₁ e₂) :
  ∃ e', (e₁ ~>₁ e') ∧ (e₂ ~>₁ e') := by
{ induction e generalizing e₁ e₂,
  case sort : s { cases h₁, cases h₂, use (sort s), exact ⟨r1_sort s, r1_sort s⟩, },
  case var : v { cases h₁, cases h₂, use (var v), exact ⟨r1_var v, r1_var v⟩ },
  case app : l r ihl ihr
  { cases h₁,
    case r1_app : l l₁ r r₁ hl₁ hr₁
    { cases h₂,
      case r1_beta : t e r
      { rcases hl₁ with _ | _ | _ | _ | @⟨t, t', e, e', ht, he⟩ | _,
        use e'.subs 0 r,
         },
      case r1_app : l l₂ r r₂ hl₂ hr₂
      { cases ihl hl₁ hl₂ with el hel,
        cases ihr hr₁ hr₂ with er her,
        use (app el er), exact ⟨r1_app hel.1 her.1, r1_app hel.2 her.2⟩ }}
  }
}

end
end coc
