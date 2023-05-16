import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Coc.Defs

namespace Coc
section

/-- Three-way comparison operator. -/
inductive Threeway (m n : Nat) : Prop
  | lt : m < n → Threeway m n
  | eq : m = n → Threeway m n
  | gt : n < m → Threeway m n

@[irreducible]
def threewayCompare (m n : Nat) : Threeway m n :=
  dite (m < n) Threeway.lt
    (dite (m = n) (fun h _ => Threeway.eq h)
      (fun h₁ h₂ => Threeway.gt
        (lt_of_le_of_ne (le_of_not_lt h₂)
          (fun h : n = m => h₁ h.symm))))

def Expr.hasOpen : Expr → Nat → Prop
  | sort _,   _ => false
  | var v,    n => v = n
  | app l r,  n => Expr.hasOpen l n ∨ Expr.hasOpen r n
  | lam t e,  n => Expr.hasOpen t n ∨ Expr.hasOpen e n.succ
  | pi t₁ t₂, n => Expr.hasOpen t₁ n ∨ Expr.hasOpen t₂ n.succ

def Expr.closed : Expr → Nat → Prop
  | sort _,   _ => true
  | var v,    n => v < n
  | app l r,  n => Expr.closed l n ∧ Expr.closed r n
  | lam t e,  n => Expr.closed t n ∧ Expr.closed e n.succ
  | pi t₁ t₂, n => Expr.closed t₁ n ∧ Expr.closed t₂ n.succ

structure CExpr (n : Nat) : Type :=
  e : Expr
  hce : Expr.closed e n

/- Lemmas for `hasOpen e n`: `e` has variables unbound at `n`-th level. -/
namespace hasOpen
  open Expr
  theorem var {v n} (h : v = n) :                             hasOpen (var v) n   := h
  theorem app_left {l r n}          (hl : hasOpen l n) :      hasOpen (app l r) n := .inl hl
  theorem app_right {l r n}         (hr : hasOpen r n) :      hasOpen (app l r) n := .inr hr
  theorem lam_left {l r n}          (hl : hasOpen l n) :      hasOpen (lam l r) n := .inl hl
  theorem lam_right {l r} {n : Nat} (hr : hasOpen r n.succ) : hasOpen (lam l r) n := .inr hr
  theorem pi_left {l r n}           (hl : hasOpen l n) :      hasOpen (pi l r) n  := .inl hl
  theorem pi_right {l r} {n : Nat}  (hr : hasOpen r n.succ) : hasOpen (pi l r) n  := .inr hr
end hasOpen
open hasOpen

/- Lemmas for `closed e n`: `e` has at most `n` levels of unbound variables. -/
namespace closed
  open Expr
  theorem sort (s n)                                                  : closed (sort s) n   := rfl
  theorem var {v n} (h : v < n)                                       : closed (var v) n    := h
  theorem app {l r n} (hcl : closed l n) (hcr : closed r n)           : closed (app l r) n  := ⟨hcl, hcr⟩
  theorem lam {t e n} (hct : closed t n) (hce : closed e n.succ)      : closed (lam t e) n  := ⟨hct, hce⟩
  theorem pi {t₁ t₂ n} (hct₁ : closed t₁ n) (hct₂ : closed t₂ n.succ) : closed (pi t₁ t₂) n := ⟨hct₁, hct₂⟩
  theorem weaken {e n n'} (hce : closed e n) (h : n <= n') : closed e n' :=
    @Expr.rec (fun e => ∀ n n', n ≤ n' → closed e n → closed e n')
      (fun _ _ _ _ _ => sort _ _)
      (fun _ _ _ h h' => var (lt_of_lt_of_le h' h))
      (fun _ _ hl hr _ _ h ⟨hcl, hcr⟩ => ⟨hl _ _ h hcl, hr _ _ h hcr⟩)
      (fun _ _ ht he _ _ h ⟨hct, hce⟩ => ⟨ht _ _ h hct, he _ _ (Nat.succ_le_succ h) hce⟩)
      (fun _ _ ht₁ ht₂ _ _ h ⟨hct₁, hct₂⟩ => ⟨ht₁ _ _ h hct₁, ht₂ _ _ (Nat.succ_le_succ h) hct₂⟩)
      e n n' h hce
  theorem weaken₁ {e n} (hce : closed e n) : closed e n.succ :=
    weaken hce (Nat.le_succ n)
end closed
open closed

theorem hasOpen.below_closed {e n n'} (ho : Expr.hasOpen e n') (hc : Expr.closed e n) : n' < n := by
  induction e generalizing n n' with
    | sort => unfold Expr.hasOpen at *; trivial
    | var => unfold Expr.hasOpen Expr.closed at *; rw [ho] at hc; exact hc
    | app _ _ hl hr => cases ho with | inl ho => exact hl ho hc.1 | inr ho => exact hr ho hc.2
    | lam _ _ ht he => cases ho with | inl ho => exact ht ho hc.1 | inr ho => exact Nat.lt_of_succ_lt_succ (he ho hc.2)
    | pi _ _ ht₁ ht₂ => cases ho with | inl ho => exact ht₁ ho hc.1 | inr ho => exact Nat.lt_of_succ_lt_succ (ht₂ ho hc.2)

theorem test : WellFounded (Nat.lt) := ⟨fun n => by
  induction n with
    | zero => apply Acc.intro; intros x hx; exfalso; exact Nat.not_lt_zero x hx
    | succ n ih =>
      have h : ∀ x, x < n → Acc Nat.lt x := fun _ => Acc.inv ih
      apply Acc.intro
      intros x hx
      cases hx with
        | refl => exact ih
        | step hy => exact h x hy⟩

#check @Classical.choice
#check @Classical.indefiniteDescription

end
end Coc
