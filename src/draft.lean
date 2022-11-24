import tactic
import expr

namespace coc
section

open idx
open expr

def expr.has_open : expr → nat → Prop
| (sort s)        n := false
| (var (bound b)) n := b = n
| (var (free f))  n := false
| (app l r)       n := expr.has_open l n ∨ expr.has_open r n
| (lam t e)       n := expr.has_open t n ∨ expr.has_open e n.succ
| (pi t₁ t₂)      n := expr.has_open t₁ n ∨ expr.has_open t₂ n.succ

def expr.closed : expr → nat → Prop
| (sort s)        n := true
| (var (bound b)) n := b < n
| (var (free f))  n := true
| (app l r)       n := expr.closed l n ∧ expr.closed r n
| (lam t e)       n := expr.closed t n ∧ expr.closed e n.succ
| (pi t₁ t₂)      n := expr.closed t₁ n ∧ expr.closed t₂ n.succ

structure cexpr (n : nat) : Type :=
  (e : expr) (hce : expr.closed e n)

open expr

/- Lemmas for `has_open e n`: `e` has variables unbound at `n`-th level. -/
namespace has_open
  lemma ho_bound {b n} (h : b = n) :                            has_open (var (bound b)) n := h
  lemma ho_app_left {l r n}          (hl : has_open l n) :      has_open (app l r) n       := or.inl hl
  lemma ho_app_right {l r n}         (hr : has_open r n) :      has_open (app l r) n       := or.inr hr
  lemma ho_lam_left {l r n}          (hl : has_open l n) :      has_open (lam l r) n       := or.inl hl
  lemma ho_lam_right {l r} {n : nat} (hr : has_open r n.succ) : has_open (lam l r) n       := or.inr hr
  lemma ho_pi_left {l r n}           (hl : has_open l n) :      has_open (pi l r) n        := or.inl hl
  lemma ho_pi_right {l r} {n : nat}  (hr : has_open r n.succ) : has_open (pi l r) n        := or.inr hr
end has_open
open has_open

/- Lemmas for `closed e n`: `e` has at most `n` levels of unbound variables. -/
namespace closed
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

lemma has_open.below_closed {e n n'} (ho : has_open e n') (hc : closed e n) : n' < n := by
{ induction e generalizing n n',
  case sort { unfold has_open at *, trivial },
  case var : v _ _ ho hc
  { rcases v with b | f,
    unfold has_open closed at *, rw ho at hc, exact hc,
    unfold has_open at *, trivial },
  case app : _ _ hl hr _ _ ho hc { cases ho, exact hl ho hc.1, exact hr ho hc.2 },
  case lam : _ _ ht he _ _ ho hc { cases ho, exact ht ho hc.1, exact nat.lt_of_succ_lt_succ (he ho hc.2) },
  case pi : _ _ ht₁ ht₂ _ _ ho hc { cases ho, exact ht₁ ho hc.1, exact nat.lt_of_succ_lt_succ (ht₂ ho hc.2) } }

lemma test : well_founded (nat.lt) :=
  ⟨λ n, by
  { induction n,
    case zero { apply acc.intro, intros x hx, exfalso, exact nat.not_lt_zero x hx },
    case succ : n ih
    { have h : ∀ x, x < n → acc nat.lt x := λ _, acc.inv ih,
      apply acc.intro,
      intros x hx,
      cases hx,
      case refl { exact ih },
      case step : y hy { apply h, exact nat.lt_of_succ_le hy } } }⟩

end
end coc
