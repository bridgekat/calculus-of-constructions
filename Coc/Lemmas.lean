import Mathlib.Tactic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Prod.Lex
import Coc.Defs

namespace Coc
section

/- Auxiliary arithmetic lemmas. -/

theorem Nat.order_aux_1 {a b : Nat} (h₁ : ¬a < b) (h₂ : ¬a = b) : (b < a) := lt_of_le_of_ne (Nat.le_of_not_lt h₁) (Ne.symm h₂)
theorem Nat.order_aux_2 {a b c : Nat} (h : a + b < c) : b < c := lt_of_le_of_lt (Nat.le_add_left b a) h
theorem Nat.order_aux_3 {a b c : Nat} (h : a + b < c) : a < c := lt_of_le_of_lt (Nat.le_add_right a b) h

theorem Nat.lt_add_left' (a b c : Nat) (h : a < b) : a < c + b := by
  exact lt_add_of_nonneg_of_lt (Nat.zero_le c) h

theorem Nat.lt_add_right' (a b c : Nat) (h : a < b) : a < b + c := by
  exact Nat.lt_add_right a b c h

theorem Nat.le_add_left' (a b c : Nat) (h : a ≤ b) : a ≤ c + b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  refine @Nat.le.intro _ _ (k + c) ?_
  rw [← Nat.add_assoc, hk, Nat.add_comm]

theorem Nat.le_add_right' (a b c : Nat) (h : a ≤ b) : a ≤ b + c := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  refine @Nat.le.intro _ _ (k + c) ?_
  rw [← Nat.add_assoc, hk]

/- Auxiliary list indexing lemmas. -/

theorem List.get?_aux_1 {α} (a b : List α) (n : Nat) (h : n < a.length) :
  List.get? (a ++ b) n = List.get? a n := by
  exact List.get?_append h

theorem List.get?_aux_2 {α} (a b : List α) (n : Nat) :
  List.get? (a ++ b) (a.length + n) = List.get? b n := by
  rw [Nat.add_comm, List.get?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel _ _]

theorem List.get?_aux_3 {α} (a : List α) (b : α) (c : List α) (n : Nat) (h : n < a.length) :
  List.get? (a ++ b :: c) n = List.get? a n := by
  exact List.get?_append h

theorem List.get?_aux_4 {α} (a : List α) (b : α) (c : List α) :
  List.get? (a ++ b :: c) a.length = some b := by
  rw [← Nat.zero_add a.length, List.get?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel _ _]; eq_refl

theorem List.get?_aux_5 {α} (a : List α) (b : α) (c : List α) (n : Nat) :
  List.get? (a ++ b :: c) (a.length + n.succ) = List.get? c n := by
  rw [Nat.add_comm, List.get?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel _ _]; eq_refl

namespace Expr
section

/- Notations. -/

scoped notation e " ⟦" n:80 " ↦ " e':79 "⟧" => subst e n e'
scoped notation e " ⟦" n:80 " ↟ " m:79 "⟧"  => shift e n m

/- Uninteresting `shift` lemmas for supporting case analysis. -/

theorem shift_le {v n m} (h : n ≤ v) : (var v) ⟦n ↟ m⟧ = var (v + m) := by
  unfold shift; split_ifs; eq_refl

theorem shift_gt {v n m} (h : v < n) : (var v) ⟦n ↟ m⟧ = var v := by
  unfold shift; split_ifs with hif; exfalso; exact not_le_of_lt h hif; eq_refl

/- Uninteresting `subst` lemmas for supporting case analysis. -/

theorem subst_lt {v n e'} (h : n < v) : (var v) ⟦n ↦ e'⟧ = var (Nat.pred v) := by
  unfold subst; split_ifs; eq_refl

theorem subst_eq {n e'} : (var n) ⟦n ↦ e'⟧ = e' ⟦0 ↟ n⟧ := by
  unfold subst; split_ifs with hif₁ hif₂
  . exfalso; exact Nat.lt_irrefl _ hif₁
  . eq_refl
  . exfalso; exact hif₂ rfl

theorem subst_gt {v n e'} (h : v < n) : (var v) ⟦n ↦ e'⟧ = var v := by
  unfold subst; split_ifs with hif₁ hif₂
  . exfalso; exact Nat.lt_irrefl _ (Nat.lt_trans h hif₁)
  . rw [hif₂] at h; exfalso; exact Nat.lt_irrefl _ h
  . eq_refl

/- How `shift` interacts with itself. -/

theorem shift_zero (e n) : e ⟦n ↟ 0⟧ = e := by
  induction e generalizing n
  case sort s => unfold shift; eq_refl
  case var v => cases v <;> unfold shift <;> split_ifs <;> simp
  case app l r ihl ihr => unfold shift; rw [ihl, ihr]
  case lam t e iht ihe => unfold shift; rw [iht, ihe]
  case pi t₁ t₂ iht₁ iht₂ => unfold shift; rw [iht₁, iht₂]

theorem shift_shift_disjoint_ind (e k a b c) : e ⟦(b + k) ↟ c⟧ ⟦k ↟ a⟧ = e ⟦k ↟ a⟧ ⟦(a + b + k) ↟ c⟧ := by
  induction e generalizing k
  case sort s => unfold shift; eq_refl
  case var v =>
    rcases (lt_or_le v k) with h₁ | h₁
    . rw [shift_gt (Nat.lt_add_left' _ _ _ h₁),
          shift_gt h₁,
          shift_gt (Nat.lt_add_left' _ _ _ h₁)]
    rcases (lt_or_le v (b + k)) with h₂ | h₂
    . rw [shift_gt h₂,
          shift_le h₁, Nat.add_comm, Nat.add_assoc,
          shift_gt (Nat.add_lt_add_left h₂ _)]
    . rw [shift_le h₂,
          shift_le (Nat.le_add_right' _ _ _ h₁),
          shift_le h₁, Nat.add_comm v a, Nat.add_assoc a b k,
          shift_le (Nat.add_le_add_left h₂ _), Nat.add_comm, Nat.add_assoc]
  case app l r ihl ihr => dsimp only [shift]; rw [ihl, ihr];
  case lam t e iht ihe => dsimp only [shift]; rw [iht, ← Nat.add_succ, ihe]; eq_refl
  case pi t₁ t₂ iht₁ iht₂ => dsimp only [shift]; rw [iht₁, ← Nat.add_succ, iht₂]; eq_refl

theorem shift_shift_disjoint (e a b c) : e ⟦b ↟ c⟧ ⟦0 ↟ a⟧ = e ⟦0 ↟ a⟧ ⟦(a + b) ↟ c⟧ :=
  shift_shift_disjoint_ind e 0 a b c

theorem shift_shift_overlap_ind (e k a b c) : e ⟦k ↟ (a + b)⟧ ⟦(a + k) ↟ c⟧ = e ⟦k ↟ (a + b + c)⟧ := by
  induction e generalizing k
  case sort s => dsimp only [shift]
  case var v =>
    rcases (lt_or_le v k) with h | h
    . rw [shift_gt h,
          shift_gt (Nat.lt_add_left' _ _ _ h),
          shift_gt h]
    . rw [shift_le h, Nat.add_comm a k, ← Nat.add_assoc,
          shift_le (Nat.le_add_right' _ _ _ (Nat.add_le_add_right h _)),
          shift_le h, ← Nat.add_assoc, ← Nat.add_assoc]
  case app l r ihl ihr => dsimp only [shift]; rw [ihl, ihr]
  case lam t e iht ihe => dsimp only [shift]; rw [iht, ← Nat.add_succ, ihe]
  case pi t₁ t₂ iht₁ iht₂ => dsimp only [shift]; rw [iht₁, ← Nat.add_succ, iht₂]

theorem shift_shift_overlap (e a b c) : e ⟦0 ↟ (a + b)⟧ ⟦a ↟ c⟧ = e ⟦0 ↟ (a + b + c)⟧ :=
  shift_shift_overlap_ind e 0 a b c

/- How `shift` and `subst` interact with each other. -/

theorem shift_subst_above_ind (e e' k n m) : e ⟦k ↟ n⟧ ⟦(n + m + k) ↦ e'⟧ = e ⟦(m + k) ↦ e'⟧ ⟦k ↟ n⟧ := by
  induction e generalizing k n m
  case sort s => dsimp only [shift, subst]
  case var v =>
    rcases lt_or_le v k with h₁ | h₁
    . rw [shift_gt h₁,
          subst_gt (Nat.lt_add_left' _ _ _ h₁),
          subst_gt (Nat.lt_add_left' _ _ _ h₁),
          shift_gt h₁]
    . rw [shift_le h₁]
      rcases Nat.lt_trichotomy v (m + k) with h₂ | h₂ | h₂
      . rw [subst_gt h₂, Nat.add_comm, Nat.add_assoc,
            subst_gt (Nat.add_lt_add_left h₂ _),
            shift_le h₁, Nat.add_comm]
      . rw [Nat.add_comm, Nat.add_assoc, h₂,
            subst_eq,
            subst_eq, Nat.add_comm, Nat.add_comm m k,
            shift_shift_overlap _ _ _ _]
      . cases v
        case zero => exfalso; exact Nat.not_lt_zero _ h₂
        case succ v =>
          rw [Nat.add_comm, Nat.add_assoc,
              subst_lt (Nat.add_lt_add_left h₂ _),
              subst_lt h₂, Nat.add_succ, Nat.pred_succ, Nat.pred_succ,
              shift_le (Nat.le_of_lt_succ (Nat.order_aux_2 h₂)), Nat.add_comm]
  case app l r hl hr => dsimp only [shift, subst]; rw [hl, hr]
  case lam t e ht he => dsimp only [shift, subst]; rw [ht, ← Nat.add_succ, he]; eq_refl
  case pi t₁ t₂ ht₁ ht₂ => dsimp only [shift, subst]; rw [ht₁, ← Nat.add_succ, ht₂]; eq_refl

theorem shift_subst_above (e e' n m) : e ⟦0 ↟ n⟧ ⟦(n + m) ↦ e'⟧ = e ⟦m ↦ e'⟧ ⟦0 ↟ n⟧ :=
  shift_subst_above_ind e e' 0 n m

theorem shift_subst_insi.ind (e e' k n m) : e ⟦k ↟ Nat.succ (n + m)⟧ ⟦(n + k) ↦ e'⟧ = e ⟦k ↟ (n + m)⟧ := by
  induction e generalizing k
  case sort s => dsimp only [shift, subst]
  case var v =>
    rcases lt_or_le v k with h₁ | h₁
    . rw [shift_gt h₁,
          shift_gt h₁,
          subst_gt (Nat.lt_add_left' _ _ _ h₁)]
    . rw [shift_le h₁,
          shift_le h₁, Nat.add_succ, ← Nat.add_assoc, Nat.add_comm n k,
          subst_lt (Nat.lt_succ_of_le (Nat.le_add_right' _ _ _ (Nat.add_le_add_right h₁ _))),
          Nat.pred_succ]
  case app l r hl hr => dsimp only [shift, subst]; rw [hl, hr]
  case lam t e ht he => dsimp only [shift, subst]; rw [ht, ← Nat.add_succ n k, he]
  case pi t₁ t₂ ht₁ ht₂ => dsimp only [shift, subst]; rw [ht₁, ← Nat.add_succ n k, ht₂]

theorem shift_subst_inside (e e' n m) : e ⟦0 ↟ Nat.succ (n + m)⟧ ⟦n ↦ e'⟧ = e ⟦0 ↟ (n + m)⟧ :=
  shift_subst_insi.ind e e' 0 n m

theorem shift_subst_below_ind (e e' k n m) : e ⟦Nat.succ (n + k) ↟ m⟧ ⟦k ↦ e' ⟦n ↟ m⟧⟧ = e ⟦k ↦ e'⟧ ⟦(n + k) ↟ m⟧ := by
  induction e generalizing k
  case sort s => dsimp only [shift, subst]
  case var v =>
    rcases Nat.lt_trichotomy v k with h₁ | h₁ | h₁
    . rw [shift_gt (Nat.lt_succ_of_lt (Nat.lt_add_left' _ _ _ h₁)),
          subst_gt h₁,
          subst_gt h₁,
          shift_gt (Nat.lt_add_left' _ _ _ h₁)]
    . rw [← h₁,
          shift_gt (Nat.lt_succ_of_le (Nat.le_add_left' _ _ _ (Nat.le_refl v))),
          subst_eq,
          subst_eq, Nat.add_comm,
          shift_shift_disjoint]
    . cases v;
      case zero => exfalso; exact Nat.not_lt_zero _ h₁
      case succ v =>
        rw [subst_lt h₁]
        rcases lt_or_le v (n + k) with h₂ | h₂
        . rw [shift_gt (Nat.succ_lt_succ h₂), Nat.pred_succ,
              subst_lt h₁,
              shift_gt h₂, Nat.pred_succ]
        . rw [shift_le (Nat.succ_le_succ h₂), Nat.pred_succ,
              subst_lt (Nat.lt_add_right' _ _ _ h₁), Nat.succ_add,
              shift_le h₂, Nat.pred_succ]
  case app l r ihl ihr => dsimp only [shift, subst]; rw [ihl, ihr]
  case lam t e iht ihe => dsimp only [shift, subst]; rw [iht, ← Nat.add_succ, ihe]
  case pi t₁ t₂ iht₁ iht₂ => dsimp only [shift, subst]; rw [iht₁, ← Nat.add_succ, iht₂]

theorem shift_subst_below (e e' n m) : e ⟦Nat.succ n ↟ m⟧ ⟦0 ↦ e' ⟦n ↟ m⟧⟧ = e ⟦0 ↦ e'⟧ ⟦n ↟ m⟧ :=
  shift_subst_below_ind e e' 0 n m

/- How `subst` interacts with itself. -/

theorem subst_subst_ind (e e₁ e₂ k n) : e ⟦Nat.succ (n + k) ↦ e₂⟧ ⟦k ↦ e₁ ⟦n ↦ e₂⟧⟧ = e ⟦k ↦ e₁⟧ ⟦(n + k) ↦ e₂⟧ := by
  induction e generalizing e₁ e₂ k n
  case sort s => dsimp only [subst]
  case var v =>
    rcases Nat.lt_trichotomy v k with h₁ | h₁ | h₁
    . rw [subst_gt h₁,
          subst_gt (Nat.lt_add_left' _ _ _ h₁),
          subst_gt (Nat.lt_succ_of_lt (Nat.lt_add_left' _ _ _ h₁)),
          subst_gt h₁]
    . rw [← h₁,
          subst_eq,
          subst_gt (Nat.lt_succ_of_le (Nat.le_add_left' _ _ _ (Nat.le_refl v))),
          subst_eq, Nat.add_comm,
          shift_subst_above _ _ _ _]
    . cases v
      case zero => exfalso; exact Nat.not_lt_zero _ h₁
      case succ v =>
        rcases Nat.lt_trichotomy v (n + k) with h₂ | h₂ | h₂
        . rw [subst_lt h₁, Nat.pred_succ,
              subst_gt h₂,
              subst_gt (Nat.succ_lt_succ h₂),
              subst_lt h₁, Nat.pred_succ]
        . rw [← h₂,
              subst_lt h₁, Nat.pred_succ,
              subst_eq,
              subst_eq, h₂, Nat.add_comm,
              shift_subst_inside]
        . rw [subst_lt h₁, Nat.pred_succ,
              subst_lt h₂,
              subst_lt (Nat.succ_lt_succ h₂), Nat.pred_succ,
              subst_lt (Nat.order_aux_2 h₂)]
  case app l r ihl ihr => dsimp only [subst]; rw [ihl, ihr]
  case lam t e iht ihe => dsimp only [subst]; rw [iht, ← Nat.add_succ, ihe]
  case pi t₁ t₂ iht₁ iht₂ => dsimp only [subst]; rw [iht₁, ← Nat.add_succ, iht₂]

theorem subst_subst (e e₁ e₂ n) : e ⟦(Nat.succ n) ↦ e₂⟧ ⟦0 ↦ e₁ ⟦n ↦ e₂⟧⟧ = e ⟦0 ↦ e₁⟧ ⟦n ↦ e₂⟧ :=
  subst_subst_ind e e₁ e₂ 0 n

/- Uninteresting `size` lemmas to support strong induction on `Expr`. -/

theorem size_wf : WellFounded (fun e₁ e₂ : Expr => size e₁ < size e₂) := (measure size).wf
theorem size_lt_size_app_l {l r} : size l < size (app l r) := Nat.lt_succ_of_le (Nat.le_add_right _ _)
theorem size_lt_size_app_r {l r} : size r < size (app l r) := Nat.lt_succ_of_le (Nat.le_add_left _ _)
theorem size_lt_size_lam_l {l r} : size l < size (lam l r) := Nat.lt_succ_of_le (Nat.le_add_right _ _)
theorem size_lt_size_lam_r {l r} : size r < size (lam l r) := Nat.lt_succ_of_le (Nat.le_add_left _ _)
theorem size_lt_size_pi_l {l r} : size l < size (pi l r) := Nat.lt_succ_of_le (Nat.le_add_right _ _)
theorem size_lt_size_pi_r {l r} : size r < size (pi l r) := Nat.lt_succ_of_le (Nat.le_add_left _ _)
theorem size_lt_size_app_lam_e {t e r} : size e < size (app (lam t e) r) :=
  Nat.lt_trans size_lt_size_lam_r size_lt_size_app_l

/-- The "one-step reduction" relation `Red1 e₁ e₂`:
    "`e₁` reduces to `e₂` by contracting zero or more immediate redexes." -/
inductive Red1 : Expr → Expr → Prop
| beta {t e e' r r'}   : Red1 e e' → Red1 r r' →     Red1 (app (lam t e) r) (e'⟦0 ↦ r'⟧)
| sort {s}             :                             Red1 (sort s) (sort s)
| var  {v}             :                             Red1 (var v) (var v)
| app  {l l' r r'}     : Red1 l l' → Red1 r r' →     Red1 (app l r) (app l' r')
| lam  {t t' e e'}     : Red1 t t' → Red1 e e' →     Red1 (lam t e) (lam t' e')
| pi   {t₁ t₁' t₂ t₂'} : Red1 t₁ t₁' → Red1 t₂ t₂' → Red1 (pi t₁ t₂) (pi t₁' t₂')

scoped notation e " ~>₁ " e':50 => Red1 e e'

theorem Red1.refl {e} : e ~>₁ e :=
  Expr.recOn e
    (fun _ => Red1.sort)
    (fun _ => Red1.var)
    (fun _ _ => Red1.app)
    (fun _ _ => Red1.lam)
    (fun _ _ => Red1.pi)

/-- Shifting respects one-step reduction. -/
theorem Red1.shift_ind (n e e' k) (h : e ~>₁ e') : e ⟦k ↟ n⟧ ~>₁ e' ⟦k ↟ n⟧ := by
  -- Strong induction on `e` generalising `e' k`.
  revert e e' k; intros e
  apply size_wf.induction e; intros e ih e' k h
  cases e
  case sort s => cases h; dsimp only [shift]; exact Red1.refl
  case var v => cases h; cases v <;> (try split_ifs) <;> exact Red1.refl
  case app l r =>
    cases h
    case beta t e e' r' he hr =>
      dsimp only [shift]; rw [← shift_subst_below]
      refine .beta (ih e ?_ _ _ ?_) (ih r ?_ _ _ ?_); assumption'
      exacts [size_lt_size_app_lam_e, size_lt_size_app_r]
    case app l' r' hl hr =>
      dsimp only [shift]; refine .app (ih l ?_ _ _ ?_) (ih r ?_ _ _ ?_); assumption'
      exacts [size_lt_size_app_l, size_lt_size_app_r]
  case lam t e =>
    cases h; dsimp only [shift]
    refine .lam (ih t ?_ _ _ ?_) (ih e ?_ _ _ ?_); assumption'
    exacts [size_lt_size_lam_l, size_lt_size_lam_r]
  case pi t₁ t₂ =>
    cases h; dsimp only [shift]
    refine .pi (ih t₁ ?_ _ _ ?_) (ih t₂ ?_ _ _ ?_); assumption'
    exacts [size_lt_size_pi_l, size_lt_size_pi_r]

theorem Red1.shift (n) {e e'} (h : e ~>₁ e') : e ⟦0 ↟ n⟧ ~>₁ e' ⟦0 ↟ n⟧ :=
  Red1.shift_ind n e e' 0 h

/-- Substitution respects one-step reduction. -/
theorem Red1.subst_ind {l l'} (hl : l ~>₁ l') {r r'} (hr : r ~>₁ r') (k) : l ⟦k ↦ r⟧ ~>₁ l' ⟦k ↦ r'⟧ := by
  -- Strong induction on `l₀` generalising `l₀' r₀ r₀' k`.
  revert l l' r r' k; intros l₀
  apply size_wf.induction l₀; intros l₀ ih l₀' hl₀ r₀ r₀' hr₀ k
  cases l₀
  case sort s => cases hl₀; dsimp only [subst]; exact .sort
  case var v =>
    cases hl₀; dsimp only [subst]
    split_ifs <;> try (exact Red1.refl)
    exact Red1.shift k hr₀
  case app l r =>
    cases hl₀
    case beta t e e' r' he hr =>
      dsimp only [subst]; rw [← subst_subst]
      refine .beta (ih e ?_ ?_ ?_ _) (ih r ?_ ?_ ?_ _); assumption'
      exacts [size_lt_size_app_lam_e, size_lt_size_app_r]
    case app l' r' hl hr =>
      dsimp only [subst]
      refine .app (ih l ?_ ?_ ?_ _) (ih r ?_ ?_ ?_ _); assumption'
      exacts [size_lt_size_app_l, size_lt_size_app_r]
  case lam t e =>
    cases hl₀; dsimp only [subst]
    refine .lam (ih t ?_ ?_ ?_ _) (ih e ?_ ?_ ?_ _); assumption'
    exacts [size_lt_size_lam_l, size_lt_size_lam_r]
  case pi t₁ t₂ =>
    cases hl₀; dsimp only [subst]
    refine .pi (ih t₁ ?_ ?_ ?_ _) (ih t₂ ?_ ?_ ?_ _); assumption'
    exacts [size_lt_size_pi_l, size_lt_size_pi_r]

theorem Red1.subst {l l'} (hl : l ~>₁ l') {r r'} (hr : r ~>₁ r') : l ⟦0 ↦ r⟧ ~>₁ l' ⟦0 ↦ r'⟧ :=
  Red1.subst_ind hl hr 0

/-- Confluence of one-step reduction. -/
theorem Red1.confluent {a b c} (hb : a ~>₁ b) (hc : a ~>₁ c) : ∃ d, (b ~>₁ d) ∧ (c ~>₁ d) := by
  -- Strong induction on `a` generalising `b c`.
  revert a b c; intros a
  apply size_wf.induction a; intros a ih b c hb hc
  cases a
  case sort s => cases hb; cases hc; use .sort s; exact ⟨.sort, .sort⟩
  case var v => cases hb; cases hc; use .var v; exact ⟨.var, .var⟩
  case app l r =>
    cases hb
    case beta t e eb rb heb hrb =>
      cases hc
      case beta ec rc hec hrc =>
        obtain ⟨e', _, _⟩ := ih e size_lt_size_app_lam_e heb hec
        obtain ⟨r', _, _⟩ := ih r size_lt_size_lam_r hrb hrc
        use e' ⟦0 ↦ r'⟧; refine ⟨Red1.subst ?_ ?_, Red1.subst ?_ ?_⟩; assumption'
      case app tec rc htec hrc =>
        rcases htec with _ | _ | _ | _ | @⟨t, tc, e, ec, htc, hec⟩ | _
        obtain ⟨e', _, _⟩ := ih e size_lt_size_app_lam_e heb hec
        obtain ⟨r', _, _⟩ := ih r size_lt_size_app_r hrb hrc
        use e' ⟦0 ↦ r'⟧; refine ⟨Red1.subst ?_ ?_, .beta ?_ ?_⟩; assumption'
    case app lb rb hlb hrb =>
      cases hc
      case beta t e ec rc hec hrc =>
        rcases hlb with _ | _ | _ | _ | @⟨t, tb, e, eb, htb, heb⟩ | _
        obtain ⟨e', _, _⟩ := ih e size_lt_size_app_lam_e heb hec
        obtain ⟨r', _, _⟩ := ih r size_lt_size_app_r hrb hrc
        use e' ⟦0 ↦ r'⟧; refine ⟨.beta ?_ ?_, Red1.subst ?_ ?_⟩; assumption'
      case app lc rc hlc hrc =>
        obtain ⟨l', _, _⟩ := ih l size_lt_size_app_l hlb hlc
        obtain ⟨r', _, _⟩ := ih r size_lt_size_app_r hrb hrc
        use .app l' r'; refine ⟨.app ?_ ?_, .app ?_ ?_⟩; assumption'
  case lam l r =>
    rcases hb with _ | _ | _ | _ | @⟨l, lb, r, rb, hlb, hrb⟩ | _
    rcases hc with _ | _ | _ | _ | @⟨l, lc, r, rc, hlc, hrc⟩ | _
    obtain ⟨l', _, _⟩ := ih l size_lt_size_lam_l hlb hlc
    obtain ⟨r', _, _⟩ := ih r size_lt_size_lam_r hrb hrc
    use .lam l' r'; refine ⟨.lam ?_ ?_, .lam ?_ ?_⟩; assumption'
  case pi l r =>
    rcases hb with _ | _ | _ | _ | _ | @⟨l, lb, r, rb, hlb, hrb⟩
    rcases hc with _ | _ | _ | _ | _ | @⟨l, lc, r, rc, hlc, hrc⟩
    obtain ⟨l', _, _⟩ := ih l size_lt_size_pi_l hlb hlc
    obtain ⟨r', _, _⟩ := ih r size_lt_size_pi_r hrb hrc
    use .pi l' r'; refine ⟨.pi ?_ ?_, .pi ?_ ?_⟩; assumption'

/-- Transitive closure of one-step reduction. -/
inductive RedN : Nat → Expr → Expr → Prop
| refl {e}          :                               RedN 0 e e
| step {n e₁ e₂ e₃} : RedN n e₁ e₂ → (Red1 e₂ e₃) → RedN (Nat.succ n) e₁ e₃

scoped notation e " ~>⟦" n:50 "⟧ " e':50 => RedN n e e'

theorem RedN_refl {e} : e ~>⟦0⟧ e :=
  .refl

theorem RedN_trans {n m e₁ e₂ e₃} (h₁ : e₁ ~>⟦n⟧ e₂) (h₂ : e₂ ~>⟦m⟧ e₃) : (e₁ ~>⟦n + m⟧ e₃) := by
  induction m generalizing e₃
  case zero      => cases h₂; exact h₁
  case succ m ih => rcases h₂ with _ | ⟨h₂₁, h₂₂⟩; exact .step (ih h₂₁) h₂₂

/-- Shifting respects n-step reduction. -/
theorem RedN_shift_ind {n e e'} (h : e ~>⟦n⟧ e') (s k) : e ⟦k ↟ s⟧ ~>⟦n⟧ e' ⟦k ↟ s⟧ := by
  induction n generalizing e'
  case zero      => cases h; exact .refl
  case succ n ih => rcases h with _ | ⟨h₁, h₂⟩; exact .step (ih h₁) (Red1.shift_ind _ _ _ _ h₂)

theorem RedN_shift {n e e'} (h : e ~>⟦n⟧ e') (s): e ⟦0 ↟ s⟧ ~>⟦n⟧ e' ⟦0 ↟ s⟧ :=
  RedN_shift_ind h s 0

/-- Substitution respects n-step reduction. -/
theorem RedN_subst_ind {n m l l'} (hl : l ~>⟦n⟧ l') {r r'} (hr : r ~>⟦m⟧ r') (k) : l ⟦k ↦ r⟧ ~>⟦n + m⟧ l' ⟦k ↦ r'⟧ := by
  induction n generalizing l'
  case zero =>
    cases hl
    rw [Nat.zero_add];
    induction m generalizing r'
    case zero =>
      cases hr; exact .refl
    case succ m ih =>
      rcases hr with _ | ⟨hr₁, hr₂⟩
      exact .step (ih hr₁) (Red1.subst_ind Red1.refl hr₂ _)
  case succ n ih =>
    rcases hl with _ | ⟨hl₁, hl₂⟩
    rw [Nat.succ_add]
    exact .step (ih hl₁) (Red1.subst_ind hl₂ Red1.refl _)

theorem RedN_subst {n m l l'} (hl : l ~>⟦n⟧ l') {r r'} (hr : r ~>⟦m⟧ r') : l ⟦0 ↦ r⟧ ~>⟦n + m⟧ l' ⟦0 ↦ r'⟧ :=
  RedN_subst_ind hl hr 0

/- Main part. -/
namespace RedNConfluent
section

/-
#check toLex
#check ofLex
#check (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
#check Prod.Lex.lt_iff
#check Prod.Lex.le_iff
#check Prod.Lex.left
#check Prod.Lex.right
-/

/-- Auxiliary grid structure for proving confluence of `RedN`. -/
structure Aux (n m : Nat) (a b c : Expr) (grid : Nat → Nat → Expr) (cur : Nat × Nat) : Prop :=
  (ha : grid 0 0 = a) (hb : grid n 0 = b) (hc : grid 0 m = c)
  (goDown (i j : Nat) : i < n → j ≤ m → j = 0 ∨ toLex (i.succ, j) ≤ toLex cur → (grid i j ~>₁ grid i.succ j))
  (goRight (i j : Nat) : i ≤ n → j < m → i = 0 ∨ toLex (i, j.succ) ≤ toLex cur → (grid i j ~>₁ grid i j.succ))

/-- The grid update function. -/
def update (grid : Nat → Nat → Expr) (i j : Nat) (e : Expr) : Nat → Nat → Expr :=
  fun i' j' => if i' = i then (if j' = j then e else grid i' j') else grid i' j'

theorem update_eq {g i j e} : update g i j e i j = e := by
  unfold update; split_ifs <;> trivial

theorem update_ne_fst {g i j e i' j'} (h : i' ≠ i) : update g i j e i' j' = g i' j' := by
  unfold update; split_ifs <;> trivial

theorem update_ne_snd {g i j e i' j'} (h : j' ≠ j) : update g i j e i' j' = g i' j' := by
  unfold update; split_ifs <;> trivial

/-- Fill the zeroth row and column. -/
theorem init {n m a b c} (hb : a ~>⟦n⟧ b) (hc : a ~>⟦m⟧ c) : ∃ g, Aux n m a b c g (0, 0) := by
  induction n generalizing b c
  case zero =>
    -- Zeroth row
    rcases hb with hb | _
    induction m generalizing c
    case zero =>
      cases hc; use fun _ _ => a; apply Aux.mk <;> try eq_refl
      intros _ _ h; exfalso; exact Nat.not_lt_zero _ h
      intros _ _ _ h; exfalso; exact Nat.not_lt_zero _ h
    case succ m ihm =>
      rcases hc with _ | @⟨n, c₁, c₂, c₃, hc₁, hc₂⟩
      obtain ⟨g, ha, hb, hc, goDown, goRight⟩ := ihm hc₁
      use update g 0 m.succ c; apply Aux.mk
      . rw [update_ne_snd (Nat.succ_ne_zero _).symm]; exact ha
      . rw [update_ne_snd (Nat.succ_ne_zero _).symm]; exact ha
      . rw [update_eq]
      . intros i j hi hj h; exfalso; exact Nat.not_lt_zero _ hi
      . intros i j hi hj h
        rw [update_ne_snd (ne_of_lt hj), Nat.eq_zero_of_le_zero hi]
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | hj
        . rw [update_ne_snd (ne_of_lt (Nat.succ_lt_succ hj))]
          apply goRight 0 j; exact Nat.zero_le _; exact hj; left; eq_refl;
        . rw [hj, update_eq, hc]; exact hc₂
    -- Zeroth column; the rest we don't care now
  case succ n ihn =>
    rcases hb with _ | @⟨m, b₁, b₂, b₃, hb₁, hb₂⟩
    obtain ⟨g, ha, hb, hc, goDown, goRight⟩ := ihn hb₁ hc
    use update g n.succ 0 b; apply Aux.mk
    . rw [update_ne_fst (Nat.succ_ne_zero _).symm]; exact ha
    . rw [update_eq]
    . rw [update_ne_fst (Nat.succ_ne_zero _).symm]; exact hc
    . intros i j hi hj h
      rcases h with h | h
      . rw [h, update_ne_fst (ne_of_lt hi)]
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | hi
        . rw [update_ne_fst (ne_of_lt (Nat.succ_lt_succ hi))]
          apply goDown i 0; exact hi; exact Nat.zero_le _; left; eq_refl
        . rw [hi, update_eq, hb]; exact hb₂
      . rw [Prod.Lex.le_iff] at h
        rcases h with h | ⟨h₁, h₂⟩
        . exfalso; exact Nat.not_lt_zero _ h
        . exfalso; exact Nat.succ_ne_zero _ h₁
    . intros i j hi hj h
      rcases h with h | h
      . rw [h]; apply goRight 0 j; exact Nat.zero_le _; exact hj; left; eq_refl
      . rw [Prod.Lex.le_iff] at h
        rcases h with h | ⟨h₁, h₂⟩
        . exfalso; exact Nat.not_lt_zero _ h
        . exfalso; exact Nat.not_succ_le_zero _ h₂

/-- Fill the rest of the grid. -/
theorem traverse {n m a b c g} (h : Aux n m a b c g (0, 0)) : ∀ cur, ∃ g', Aux n m a b c g' cur := by
  -- Induction on the lexical ordering of `cur`.
  intros cur; apply (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction cur; rintro ⟨i, j⟩ ih

  rcases i with _ | i
  -- Zeroth row (already done in `init`, we just need to move cursor)
  obtain ⟨ha, hb, hc, goDown, goRight⟩ := h
  refine ⟨g, ha, hb, hc, ?_, ?_⟩
  intros i' j' hi' hj' h; refine (goDown i' j' hi' hj' ?_)
  rw [Prod.Lex.le_iff] at h
  rcases h with h | h | ⟨h₁, h₂⟩
  . exact .inl h
  . exfalso; exact Nat.not_lt_zero _ h
  . exfalso; exact Nat.succ_ne_zero _ h₁
  intros i' j' hi' hj' h; refine (goRight i' j' hi' hj' ?_)
  rw [Prod.Lex.le_iff] at h
  rcases h with h | h | ⟨h₁, h₂⟩
  . exact .inl h
  . exfalso; exact Nat.not_lt_zero _ h
  . exact .inl h₁

  rcases j with _ | j
  -- Zeroth column (already done in `init`, we just need to move cursor)
  replace ih := ih (i, m) (Prod.Lex.left _ _ (Nat.lt_succ_self i))
  obtain ⟨g, ha, hb, hc, goDown, goRight⟩ := ih; refine ⟨g, ha, hb, hc, ?_, ?_⟩
  intros i' j' hi' hj' h; refine (goDown i' j' hi' hj' ?_)
  . rw [Prod.Lex.le_iff] at h
    rcases h with h | h | ⟨h₁, h₂⟩
    . exact .inl h
    . right; rw [Prod.Lex.le_iff]
      rcases (lt_or_eq_of_le (Nat.le_of_lt_succ h)) with h | h
      . exact .inl h
      . exact .inr ⟨h, hj'⟩
    . left; replace h₂ : j' = 0 := Nat.eq_zero_of_le_zero h₂; rw [h₂]
  . intros i' j' hi' hj' h; refine (goRight i' j' hi' hj' ?_)
    rw [Prod.Lex.le_iff] at h
    rcases h with h | h | ⟨h₁, h₂⟩
    . exact .inl h
    . right; rw [Prod.Lex.le_iff]
      rcases (lt_or_eq_of_le (Nat.le_of_lt_succ h)) with h | h
      . exact .inl h
      . exact .inr ⟨h, hj'⟩
    . exfalso; exact Nat.not_succ_le_zero _ h₂

  -- Inductive case.
  replace ih := ih (i.succ, j) (Prod.Lex.right _ (Nat.lt_succ_self j))
  obtain ⟨g, ha, hb, hc, goDown, goRight⟩ := ih

  rcases (lt_or_le i n) with hi | hi; swap
  -- `i` overflow (no modification)
  . refine ⟨g, ha, hb, hc, ?_, ?_⟩
    . intros i' j' hi' hj' h; refine (goDown i' j' hi' hj' ?_)
      rw [Prod.Lex.le_iff]; right; left
      exact Nat.succ_lt_succ (Nat.lt_of_lt_of_le hi' hi)
    . intros i' j' hi' hj' h; refine (goRight i' j' hi' hj' ?_)
      rw [Prod.Lex.le_iff]; right; left
      exact Nat.lt_succ_of_le (Nat.le_trans hi' hi)

  rcases (lt_or_le j m) with hj | hj; swap
  -- `j` overflow (no modification)
  . refine ⟨g, ha, hb, hc, ?_, ?_⟩
    . intros i' j' hi' hj' h; refine (goDown i' j' hi' hj' ?_)
      rw [Prod.Lex.le_iff] at h
      rcases h with h | h | ⟨h₁, h₂⟩
      . exact .inl h
      . right; rw [Prod.Lex.le_iff]; left; exact h
      . right; rw [Prod.Lex.le_iff]; right; exact ⟨h₁, Nat.le_trans hj' hj⟩
    . intros i' j' hi' hj' h; refine (goRight i' j' hi' hj' ?_)
      rw [Prod.Lex.le_iff] at h
      rcases h with h | h | ⟨h₁, h₂⟩
      . exact .inl h
      . right; rw [Prod.Lex.le_iff]; left; exact h
      . right; rw [Prod.Lex.le_iff]; right; exact ⟨h₁, Nat.le_trans hj' hj⟩

  -- The only "interesting" case (but still trivial intuitively)...
  let a' := g i j; let b' := g i.succ j; let c' := g i j.succ
  have hab' : (a' ~>₁ b') := goDown i j hi (Nat.le_of_lt hj) (.inr ?_); swap
  . rw [Prod.Lex.le_iff]; right; exact ⟨rfl, Nat.le_refl _⟩
  have hac' : (a' ~>₁ c') := goRight i j (Nat.le_of_lt hi) hj (.inr ?_); swap
  . rw [Prod.Lex.le_iff]; left; exact Nat.lt_succ_self _
  obtain ⟨d', hbd', hcd'⟩ := Red1.confluent hab' hac'

  -- Modify grid, prove invariants.
  use update g i.succ j.succ d'
  apply Aux.mk
  . rw [update_ne_fst (Nat.succ_ne_zero _).symm]; exact ha
  . rw [update_ne_snd (Nat.succ_ne_zero _).symm]; exact hb
  . rw [update_ne_fst (Nat.succ_ne_zero _).symm]; exact hc
  . intros i' j' hi' hj' h
    rw [Prod.Lex.le_iff] at h
    rcases h with h | h | ⟨h₁, h₂⟩
    . rw [h, update_ne_snd (Nat.succ_ne_zero _).symm, update_ne_snd (Nat.succ_ne_zero _).symm]
      exact goDown i' 0 hi' (Nat.zero_le _) (.inl rfl)
    . dsimp only [Prod.fst] at h
      rw [update_ne_fst (ne_of_lt h), update_ne_fst (ne_of_lt (Nat.lt_of_succ_lt h))]
      refine goDown i' j' hi' hj' ?_; right; rw [Prod.Lex.le_iff]; exact .inl h
    . dsimp only [Prod.fst, Prod.snd] at h₁ h₂
      replace h₁ := Nat.succ.inj h₁
      rcases (lt_or_eq_of_le h₂) with h₂ | h₂
      . rw [h₁, update_ne_snd (ne_of_lt h₂), update_ne_snd (ne_of_lt h₂)]
        apply goDown i j' hi hj'; right; rw [Prod.Lex.le_iff]
        exact .inr ⟨rfl, Nat.le_of_lt_succ h₂⟩
      . rw [h₁, h₂, update_ne_fst (Nat.succ_ne_self _).symm, update_eq]; exact hcd'
  . intros i' j' hi' hj' h
    rw [Prod.Lex.le_iff] at h
    rcases h with h | h | ⟨h₁, h₂⟩
    . rw [h, update_ne_fst (Nat.succ_ne_zero _).symm, update_ne_fst (Nat.succ_ne_zero _).symm]
      exact goRight 0 j' (Nat.zero_le _) hj' (.inl rfl)
    . dsimp only [Prod.fst] at h
      rw [update_ne_fst (ne_of_lt h), update_ne_fst (ne_of_lt h)]
      refine goRight i' j' hi' hj' ?_; right; rw [Prod.Lex.le_iff]; exact .inl h
    . dsimp only [Prod.fst, Prod.snd] at h₁ h₂
      replace h₂ := Nat.le_of_succ_le_succ h₂
      rw [h₁, update_ne_snd (ne_of_lt (Nat.lt_succ_of_le h₂))]
      rcases (lt_or_eq_of_le h₂) with h₂ | h₂
      . rw [update_ne_snd (ne_of_lt (Nat.succ_lt_succ h₂))]
        apply goRight i.succ j' (Nat.succ_le_of_lt hi) hj'; right; rw [Prod.Lex.le_iff]
        exact .inr ⟨rfl, Nat.succ_le_of_lt h₂⟩
      . rw [h₂, update_eq]; exact hbd'

/-- Extract conclusion from a filled grid. -/
theorem final {n m a b c g} (h : Aux n m a b c g (n, m)) : ∃ d, (b ~>⟦m⟧ d) ∧ (c ~>⟦n⟧ d) := by
  obtain ⟨ha, hb, hc, goDown, goRight⟩ := h
  use g n m
  apply And.intro
  -- Last row
  . suffices : ∀ j, j ≤ m → (b ~>⟦j⟧ g n j); exact this m (Nat.le_refl _)
    intros j
    induction j
    case zero => intros ih; rw [hb]; exact .refl
    case succ j hj =>
      intros ih; apply RedN.step (e₂ := g n j); exact hj (Nat.le_of_succ_le ih)
      apply goRight; exact Nat.le_refl _; exact Nat.lt_of_succ_le ih
      right; exact Prod.Lex.right _ ih
  -- Last column
  . suffices : ∀ i, i ≤ n → (c ~>⟦i⟧ g i m); exact this n (Nat.le_refl _)
    intros i
    induction i
    case zero => intros ih; rw [hc]; exact .refl
    case succ i hi =>
      intros ih; apply RedN.step (e₂ := g i m); exact hi (Nat.le_of_succ_le ih)
      apply goDown; exact Nat.lt_of_succ_le ih; exact Nat.le_refl _
      right; rcases eq_or_lt_of_le ih with h | h; rw [h]; exact Prod.Lex.left _ _ (Nat.lt_of_succ_le h)

end
end RedNConfluent

/-- Confluence of n-step reduction. -/
theorem red_n_confluent {n m a b c} (hb : a ~>⟦n⟧ b) (hc : a ~>⟦m⟧ c) : ∃ d, (b ~>⟦m⟧ d) ∧ (c ~>⟦n⟧ d) :=
  let ⟨_, aux₁⟩ := RedNConfluent.init hb hc
  let ⟨_, aux₂⟩ := RedNConfluent.traverse aux₁ (n, m)
  RedNConfluent.final aux₂

scoped notation e " ~> " e':50  => Small e e'
scoped notation e " ~>* " e':50 => SmallStar e e'
scoped notation e " ~~ " e':50  => Defeq e e'

/- Reduction lemmas. -/

instance coeSmallToSmallStar {e₁ e₂} : Coe (Small e₁ e₂) (SmallStar e₁ e₂) := ⟨.step .refl⟩
instance coeSmallToDefeq {e₁ e₂} : Coe (Small e₁ e₂) (Defeq e₁ e₂) := ⟨.step⟩

@[trans] theorem SmallStar.trans {e₁ e₂ e₃} (h₁ : e₁ ~>* e₂) (h₂ : e₂ ~>* e₃) : (e₁ ~>* e₃) := by
  induction h₂
  case refl             => exact h₁
  case step _ _ _ h₃ ih => exact .step ih h₃

theorem app_small_star_aux {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : app l r ~>* app l' r' :=
  @SmallStar.trans (app l r) (app l' r) (app l' r')
    (SmallStar.recOn hl .refl $ fun _ h ih => .step ih (.appLeft h))
    (SmallStar.recOn hr .refl $ fun _ h ih => .step ih (.appRight h))

theorem lam_small_star_aux {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : lam l r ~>* lam l' r' :=
  @SmallStar.trans (lam l r) (lam l' r) (lam l' r')
    (SmallStar.recOn hl .refl $ fun _ h ih => .step ih (.lamLeft h))
    (SmallStar.recOn hr .refl $ fun _ h ih => .step ih (.lamRight h))

theorem pi_small_star_aux {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : pi l r ~>* pi l' r' :=
  @SmallStar.trans (pi l r) (pi l' r) (pi l' r')
    (SmallStar.recOn hl .refl $ fun _ h ih => .step ih (.piLeft h))
    (SmallStar.recOn hr .refl $ fun _ h ih => .step ih (.piRight h))

/- Equivalence of formulations. -/

theorem Red1.of_Small {e₁ e₂} (h : e₁ ~> e₂) : (e₁ ~>₁ e₂) :=
  h.recOn
    (.beta .refl .refl)
    (fun _ ihl => .app ihl .refl)
    (fun _ ihr => .app .refl ihr)
    (fun _ ihl => .lam ihl .refl)
    (fun _ ihr => .lam .refl ihr)
    (fun _ ihl => .pi ihl .refl)
    (fun _ ihr => .pi .refl ihr)

theorem SmallStar.of_red_1 {e₁ e₂} (h : e₁ ~>₁ e₂) : e₁ ~>* e₂ := by
  induction h
  case beta t _ _ _ _ _ _ ihe ihr => exact .step (app_small_star_aux (lam_small_star_aux .refl ihe) ihr) .beta
  case sort _ => exact .refl
  case var _ => exact .refl
  case app _ _ _ _ _ _ ihl ihr => exact app_small_star_aux ihl ihr
  case lam _ _ _ _ _ _ ihl ihr => exact lam_small_star_aux ihl ihr
  case pi _ _ _ _ _ _ ihl ihr => exact pi_small_star_aux ihl ihr

theorem RedN.of_small_star {e₁ e₂} (h : e₁ ~>* e₂) : ∃ n, (e₁ ~>⟦n⟧ e₂) := by
  induction h
  case refl => exact ⟨_, .refl⟩
  case step e₃ h₁ h₂ ih => rcases ih with ⟨n, ih⟩; exact ⟨_, .step ih (Red1.of_Small h₂)⟩

theorem SmallStar.of_red_n {e₁ e₂ n} (h : e₁ ~>⟦n⟧ e₂) : e₁ ~>* e₂ := by
  induction h
  case refl e => exact .refl
  case step n e₁ e₂ e₃ h₁ h₂ ih => exact SmallStar.trans ih (SmallStar.of_red_1 h₂)

/-- Shifting respects Small-step reduction. -/
theorem SmallStar.shift_ind {e e'} (h : e ~>* e') (s k) : e ⟦k ↟ s⟧ ~>* e' ⟦k ↟ s⟧ :=
  let ⟨n, hn⟩ := RedN.of_small_star h; SmallStar.of_red_n (RedN_shift_ind hn s k)

theorem SmallStar.shift {e e'} (h : e ~>* e') (s): e ⟦0 ↟ s⟧ ~>* e' ⟦0 ↟ s⟧ :=
  SmallStar.shift_ind h s 0

/-- Substitution respects Small-step reduction. -/
theorem SmallStar.subst_ind {l l'} (hl : l ~>* l') {r r'} (hr : r ~>* r') (k) : l ⟦k ↦ r⟧ ~>* l' ⟦k ↦ r'⟧ :=
  let ⟨nl, hnl⟩ := RedN.of_small_star hl
  let ⟨nr, hnr⟩ := RedN.of_small_star hr
  SmallStar.of_red_n (RedN_subst_ind hnl hnr k)

theorem SmallStar.subst {l l'} (hl : l ~>* l') {r r'} (hr : r ~>* r') : l ⟦0 ↦ r⟧ ~>* l' ⟦0 ↦ r'⟧ :=
  SmallStar.subst_ind hl hr 0

/-- Confluence of Small-step reduction. -/
theorem SmallStar.confluent {a b c} (hb : a ~>* b) (hc : a ~>* c) : ∃ d, (b ~>* d) ∧ (c ~>* d) :=
  let ⟨n, hb'⟩ := RedN.of_small_star hb
  let ⟨m, hc'⟩ := RedN.of_small_star hc
  let ⟨d, hbd', hcd'⟩ := red_n_confluent hb' hc'
  ⟨d, SmallStar.of_red_n hbd', SmallStar.of_red_n hcd'⟩

/-- A term is in "normal form" iff there is no other term it reduces to. -/
def isNormal (e : Expr) : Prop := ∀ e', ¬ (e ~> e')

theorem SmallStar.eq_self_of_is_normal {e e'} (hn : isNormal e) (h: e ~>* e') : e = e' := by
  induction h
  case refl => eq_refl
  case step e₂ e₃ h₁ h₂ ih => replace hn := hn e₃; rw [ih] at hn; exfalso; exact hn h₂

/-- If a term has a normal form, it must be unique. -/
theorem SmallStar.normal_unique {e e₁ e₂} (h₁ : e ~>* e₁) (hn₁ : isNormal e₁) (h₂ : e ~>* e₂) (hn₂ : isNormal e₂) :
  e₁ = e₂ := by
  obtain ⟨e', h₁', h₂'⟩ := SmallStar.confluent h₁ h₂
  cases h₁'
  case refl =>
    rw [SmallStar.eq_self_of_is_normal hn₂ h₂']
  case step _ h' h'' =>
    rw [← SmallStar.eq_self_of_is_normal hn₁ h'] at h''
    exfalso; exact hn₁ _ h''

/- Auxiliary definitional equality lemmas. -/

theorem app_defeq_aux {l l' r r'} (hl : l ~~ l') (hr : r ~~ r') : app l r ~~ app l' r' :=
  @Defeq.trans (app l r) (app l' r) (app l' r')
    (Defeq.recOn hl .refl (.step ∘ .appLeft) (fun _ => .symm) (fun _ _ => .trans))
    (Defeq.recOn hr .refl (.step ∘ .appRight) (fun _ => .symm) (fun _ _ => .trans))

theorem lam_defeq_aux {l l' r r'} (hl : l ~~ l') (hr : r ~~ r') : lam l r ~~ lam l' r' :=
  @Defeq.trans (lam l r) (lam l' r) (lam l' r')
    (Defeq.recOn hl .refl (.step ∘ .lamLeft) (fun _ => .symm) (fun _ _ => .trans))
    (Defeq.recOn hr .refl (.step ∘ .lamRight) (fun _ => .symm) (fun _ _ => .trans))

theorem pi_defeq_aux {l l' r r'} (hl : l ~~ l') (hr : r ~~ r') : pi l r ~~ pi l' r' :=
  @Defeq.trans (pi l r) (pi l' r) (pi l' r')
    (Defeq.recOn hl .refl (.step ∘ .piLeft) (fun _ => .symm) (fun _ _ => .trans))
    (Defeq.recOn hr .refl (.step ∘ .piRight) (fun _ => .symm) (fun _ _ => .trans))

/-- Reduction respects definitional equality. -/
theorem Defeq.of_small_star {e₁ e₂} (h : e₁ ~>* e₂) : e₁ ~~ e₂ :=
  SmallStar.recOn h
    .refl
    (fun _ h ih => .trans ih (.step h))

instance coeSmallStarToDefeq {e₁ e₂} : Coe (SmallStar e₁ e₂) (Defeq e₁ e₂) :=
  ⟨Defeq.of_small_star⟩

theorem Defeq.of_small_stars {e₁ e₂ e} (h₁ : e₁ ~>* e) (h₂ : e₂ ~>* e) : e₁ ~~ e₂ :=
  .trans (h₁ : e₁ ~~ e) (.symm (h₂ : e₂ ~~ e))

theorem SmallStar.of_defeq {e₁ e₂} (h : e₁ ~~ e₂) : ∃ e, (e₁ ~>* e) ∧ (e₂ ~>* e) := by
  induction h
  case refl e => exact ⟨e, .refl, .refl⟩
  case step e₁ e₂ h => exact ⟨e₂, .step .refl h, .refl⟩
  case symm e₁ e₂ h ih => obtain ⟨e, ih₁, ih₂⟩ := ih; exact ⟨e, ih₂, ih₁⟩
  case trans e₁ e₂ e₃ hb hc ihb ihc =>
    obtain ⟨b, ihb₁, ihb₂⟩ := ihb
    obtain ⟨c, ihc₁, ihc₂⟩ := ihc
    obtain ⟨d, hd₁, hd₂⟩ := SmallStar.confluent ihb₂ ihc₁
    exact ⟨d, SmallStar.trans ihb₁ hd₁, SmallStar.trans ihc₂ hd₂⟩

/-- Two terms are definitionally equal iff they reduce to some same term. -/
theorem Defeq.iff_small_star {e₁ e₂} : (e₁ ~~ e₂) ↔ ∃ e, (e₁ ~>* e) ∧ (e₂ ~>* e) :=
  ⟨SmallStar.of_defeq, (fun ⟨e, he₁, he₂⟩ => Defeq.of_small_stars he₁ he₂)⟩

/-- Shifting respects definitional equality. -/
theorem Defeq.shift_ind {e e'} (h : e ~~ e') (s k) : e ⟦k ↟ s⟧ ~~ e' ⟦k ↟ s⟧ :=
  let ⟨e', h'₁, h'₂⟩ := SmallStar.of_defeq h
  Defeq.of_small_stars (SmallStar.shift_ind h'₁ _ _) (SmallStar.shift_ind h'₂ _ _)

theorem Defeq.shift {e e'} (h : e ~~ e') (s): e ⟦0 ↟ s⟧ ~~ e' ⟦0 ↟ s⟧ :=
  Defeq.shift_ind h s 0

/-- Substitution respects definitional equality. -/
theorem Defeq.subst_ind {l l'} (hl : l ~~ l') {r r'} (hr : r ~~ r') (k) : l ⟦k ↦ r⟧ ~~ l' ⟦k ↦ r'⟧ :=
  let ⟨el', hl'₁, hl'₂⟩ := SmallStar.of_defeq hl
  let ⟨er', hr'₁, hr'₂⟩ := SmallStar.of_defeq hr
  Defeq.of_small_stars (SmallStar.subst_ind hl'₁ hr'₁ _) (SmallStar.subst_ind hl'₂ hr'₂ _)

theorem Defeq_subst {l l'} (hl : l ~~ l') {r r'} (hr : r ~~ r') : l ⟦0 ↦ r⟧ ~~ l' ⟦0 ↦ r'⟧ :=
  Defeq.subst_ind hl hr 0

/- Auxiliary universe lemmas (for proving the unique typing theorem). -/

theorem sort_normal {s e} (h : sort s ~>* e) : e = sort s := by
  induction h;
  case refl => eq_refl
  case step _ _ _ _ ih => obtain ⟨s', ih⟩ := ih; rw [ih] at h; cases h

theorem eq_of_sort_defeq {s s'} (h : sort s ~~ sort s') : s = s' := by
  obtain ⟨e', h₁, h₂⟩ := SmallStar.of_defeq h
  have hi := sort_normal h₁
  have hi' := sort_normal h₂
  injection (eq.trans hi.symm hi')

/- Auxiliary pi lemmas (for proving the unique typing theorem). -/

theorem pi_normal {l r e} (h : pi l r ~>* e) : ∃ l' r', e = pi l' r' := by
  induction' h
    exact ⟨l, r, rfl⟩
    obtain ⟨l', r', ih⟩ := ih, rw ih at h
    cases' h, exacts [⟨e, t₂, rfl⟩, ⟨t₁, e, rfl⟩]

theorem SmallStar.of_pi_SmallStar.{l l' r r'} (h : pi l r ~>* pi l' r') : (l ~>* l') ∧ (r ~>* r') := by
  induction' h
  case .refl   exact ⟨.refl, .refl⟩
  case .step : e₂ h₁ h₂ ih
    obtain ⟨l'', r'', h''⟩ := pi_normal h₁
    rw h'' at h₂, cases' h₂
      obtain ⟨hl, hr⟩ := ih h'', exact ⟨.step hl h₂, hr⟩
      obtain ⟨hl, hr⟩ := ih h'', exact ⟨hl, .step hr h₂⟩

theorem Defeq_of_pi_Defeq {l l' r r'} (h : pi l r ~~ pi l' r') : (l ~~ l') ∧ (r ~~ r') := by
  obtain ⟨e, h₁, h₂⟩ := SmallStar.of_defeq h
  obtain ⟨l'', r'', he⟩ := pi_normal h₁
  rw he at h₁ h₂
  have hi := SmallStar.of_pi_SmallStar.h₁
  have hi' := SmallStar.of_pi_SmallStar.h₂
  exact ⟨Defeq.of_small_star. hi.1 hi'.1, Defeq.of_small_star. hi.2 hi'.2⟩

scoped notation `▷ `:50 Γ:50                  := judgment (well_ctx Γ)
scoped notation Γ ` ▷ `:50 e:50 ` : `:50 t:50 := judgment (has_type Γ e t)

/-- Typing judgment implies context well-formedness. -/
theorem well_ctx_of_has_type {Γ e t} (h : Γ ▷ e : t) : ▷ Γ := by
  induction' h; assumption

/-- Every well-formed (typeable) term has a unique type, up to definitional equality. -/
theorem has_type_unique {Γ e t} (h : Γ ▷ e : t) {t'} (h' : Γ ▷ e : t') : t ~~ t' := by
  revert_all, intros Γ₀ e₀ t₀ h₀ t' h'
  induction' h₀
  case t_conv : Γ e t₁ t₂ s hc ht he iht ihe
    exact .trans (.symm hc) (ihe h')
  case t_sort : Γ n h ih
    clear ih
    induction' h'
    case t_conv : _ _ _ _ hc' _ _ _ ih'   exact .trans (ih' h) hc'
    case t_sort :   eq_refl
  case t_var : Γ n t h ht ih
    clear ih
    induction' h'
    case t_conv : _ _ _ _ hc' _ _ _ ih'   exact .trans (ih' h ht) hc'
    case t_var : _ _ _ _ ht' _   injection eq.trans ht.symm ht' with ht, rw ht
  case t_app : Γ l r t₁ t₂ hl hr ihl ihr
    induction' h'
    case t_conv : _ _ _ _ hc' _ _ _ ih'   exact .trans (ih' hl hr (λ _, ihl) (λ _, ihr)) hc'
    case t_app : _ _ _ _ _ h' _ _ _   exact Defeq_subst (Defeq_of_pi_Defeq (ihl h')).2 .refl
  case t_lam : Γ t₁ t₂ s e hs he iht ihe
    induction' h'
    case t_conv : _ _ _ _ hc' _ _ _ ih'   exact .trans (ih' hs he (λ _, iht) (λ _, ihe)) hc'
    case t_lam : _ _ _ _ _ _ he' _ _   exact pi_defeq_aux .refl (ihe he')
  case t_pi : Γ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
    induction' h'
    case t_conv : _ _ _ _ hc' _ _ _ ih'   exact .trans (ih' ht₁ ht₂ (λ _, iht₁) (λ _, iht₂)) hc'
    case t_pi : _ _ _ _ _ ht₁' ht₂' _ _
      rw [eq_of_sort_defeq (iht₁ ht₁'), eq_of_sort_defeq (iht₂ ht₂')]

/- Auxiliary functions and related lemmas. -/

def ctx_shift : ctx → Nat → ctx
| []       _ := []
| (t :: Γ) n := (t ⟦Γ.length ↟ n⟧) :: ctx_shift Γ n

def ctx_subst : ctx → Expr → ctx
| []       _ := []
| (t :: Γ) e := (t ⟦Γ.length ↦ e⟧) :: ctx_subst Γ e

scoped notation `∥`:79 Γ:79 `∥`:79       := list.length Γ
scoped notation Γ ` ⟦↦↦ `:80 e:79 `⟧`:79 := ctx_subst Γ e
scoped notation Γ ` ⟦↟↟ `:80 n:79 `⟧`:79 := ctx_shift Γ n

theorem ctx_shift_length (Γ e) : ∥Γ ⟦↟↟ e⟧∥ = ∥Γ∥ := by
  induction Γ with t Γ ih
    unfold ctx_shift
    unfold ctx_shift list.length at *, rw ih

theorem ctx_shift_nth {Γ n e} (h : list.nth Γ n = option.some e) {m} (h' : n.succ + m = ∥Γ∥) (k) :
  list.nth (Γ ⟦↟↟ k⟧) n = option.some (e ⟦m ↟ k⟧) := by
  induction Γ with t Γ ih generalizing n
    unfold list.nth at h, injection h
    unfold ctx_shift at ih ⊢
    cases n with n
      unfold list.nth list.length at *, injection h with h
      rw [Nat.one_add, Nat.add_one] at h', injection h' with h'
      rw [h, h']
      unfold list.nth list.length at *
      rw [Nat.add_one, Nat.succ_add] at h', injection h' with h'
      exact ih h h'

theorem ctx_subst_length (Γ e) : ∥Γ ⟦↦↦ e⟧∥ = ∥Γ∥ := by
  induction Γ with t Γ ih
    unfold ctx_subst
    unfold ctx_subst list.length at *, rw ih

theorem ctx_subst_nth {Γ n e} (h : list.nth Γ n = option.some e) {m} (h' : n.succ + m = ∥Γ∥) (e') :
  list.nth (Γ ⟦↦↦ e'⟧) n = option.some (e ⟦m ↦ e'⟧) := by
  induction Γ with t Γ ih generalizing n
    unfold list.nth at h, injection h
    unfold ctx_subst at ih ⊢
    cases n with n
      unfold list.nth list.length at *, injection h with h
      rw [Nat.one_add, Nat.add_one] at h', injection h' with h'
      rw [h, h']
      unfold list.nth list.length at *
      rw [Nat.add_one, Nat.succ_add] at h', injection h' with h'
      exact ih h h'

/- How typing interacts with shifting. -/

/-- Lean 3 does not have good specialised support for mutually inductive types.
    To carry out proofs using mutual induction, we have to define both motives beforehand. -/
def judgment_shift_ind_type : judgment_index → Prop
| (well_ctx Γ₀)     := ∀ {Γ' Γ} (h₀ : Γ₀ = Γ' ++ Γ) {Δ} (hw : ▷ Δ ++ Γ), ▷ Γ' ⟦↟↟ ∥Δ∥⟧ ++ Δ ++ Γ
| (has_type Γ₀ e t) := ∀ {Γ' Γ} (h₀ : Γ₀ = Γ' ++ Γ) {Δ} (hw : ▷ Δ ++ Γ), Γ' ⟦↟↟ ∥Δ∥⟧ ++ Δ ++ Γ ▷ e ⟦∥Γ'∥ ↟ ∥Δ∥⟧ : t ⟦∥Γ'∥ ↟ ∥Δ∥⟧

/-- The mutual induction proof itself. -/
theorem judgment_shift_ind {i : judgment_index} (h : judgment i) : judgment_shift_ind_type i := by
  induction h
  case c_nil
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw
    rw list.nil_eq_append_iff at h₀
    rw h₀.1 at ⊢, rw h₀.2 at hw ⊢
    exact hw
  case c_cons : Γ₀ t s ht iht
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw
    cases Γ' with t' Γ' ih'
      unfold ctx_shift, exact hw
      rw list.cons_append at h₀, injection h₀ with h₁ h₂
      rw ← h₁ at h₀ ⊢, clear h₁ t'
      rw h₂ at ht iht, clear h₂ h₀ Γ₀
      specialize iht rfl hw, unfold shift at iht
      unfold ctx_shift
      exact c_cons iht
  case t_conv : Γ₀ e t t' s hc ht he iht ihe
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw, rw h₀ at *, clear h₀ Γ₀
    specialize iht rfl hw, unfold shift at iht
    specialize ihe rfl hw
    exact t_conv (Defeq.shift_ind hc _ _) iht ihe
  case t_sort : Γ₀ n hw' ih
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw, rw h₀ at *, clear h₀ Γ₀
    specialize ih rfl hw
    unfold shift, exact t_sort ih
  case t_var : Γ₀ n t hw' ht ih
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw, rw h₀ at *, clear h₀ Γ₀
    specialize ih rfl hw
    rcases lt_or_le n ∥Γ'∥ with h₁ | h₁
      rw shift_gt h₁
      obtain ⟨m, hm⟩ := Nat.le.dest (Nat.succ_le_of_lt h₁)
      have := shift_shift_disjoint t n.succ m ∥Δ∥
      rw hm at this, rw ← this, clear this
      refine t_var ih _
      have h₂ := h₁, rw ← @ctx_shift_length Γ' ∥Δ∥ at h₂
      rw [list.append_assoc, list.nth_aux_1 _ _ _ h₂]
      rw list.nth_aux_1 _ _ _ h₁ at ht
      exact ctx_shift_nth ht hm _
      rw shift_le h₁
      obtain ⟨m, hm⟩ := Nat.le.dest h₁
      have := shift_shift_overlap t ∥Γ'∥ m.succ ∥Δ∥
      rw [Nat.add_succ, hm] at this, rw [this, Nat.succ_add], clear this
      refine t_var ih _
      have h₂ := hm, rw ← @ctx_shift_length Γ' ∥Δ∥ at h₂
      rw [← h₂, list.append_assoc, Nat.add_assoc, list.nth_aux_2, Nat.add_comm, list.nth_aux_2]
      rw [← hm, list.nth_aux_2] at ht
      exact ht
  case t_app : Γ₀ l r t₁ t₂ hl hr ihl ihr
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw, rw h₀ at *, clear h₀ Γ₀
    specialize ihl rfl hw
    specialize ihr rfl hw
    unfold shift at *
    have := shift_subst_below_ind t₂ r 0 ∥Γ'∥ ∥Δ∥
    rw Nat.add_zero at this, rw ← this, clear this
    exact t_app ihl ihr
  case t_lam : Γ₀ t₁ t₂ s e hs he iht ihe
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw, rw h₀ at *, clear h₀ Γ₀
    specialize iht rfl hw
    rw ← list.cons_append at he ihe
    specialize ihe rfl hw, unfold ctx_shift at ihe
    unfold shift at *
    exact t_lam iht ihe
  case t_pi : Γ₀ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
    unfold judgment_shift_ind_type at *, intros Γ' Γ h₀ Δ hw, rw h₀ at *, clear h₀ Γ₀
    specialize iht₁ rfl hw
    rw ← list.cons_append at ht₂ iht₂
    specialize iht₂ rfl hw, unfold ctx_shift at iht₂
    unfold shift at *
    exact t_pi iht₁ iht₂

theorem well_ctx_shift_ind {Γ' Γ} (h : ▷ Γ' ++ Γ) {Δ} (hw : ▷ Δ ++ Γ) :
  (▷ Γ' ⟦↟↟ ∥Δ∥⟧ ++ Δ ++ Γ) :=
    judgment_shift_ind h rfl hw

theorem has_type_shift_ind {Γ' Γ e t} (h : Γ' ++ Γ ▷ e : t) {Δ} (hw : ▷ Δ ++ Γ) :
  (Γ' ⟦↟↟ ∥Δ∥⟧ ++ Δ ++ Γ ▷ e ⟦∥Γ'∥ ↟ ∥Δ∥⟧ : t ⟦∥Γ'∥ ↟ ∥Δ∥⟧) :=
    judgment_shift_ind h rfl hw

theorem has_type_shift {Γ e t} (h : Γ ▷ e : t) {Δ} (hw : ▷ Δ ++ Γ) :
  (Δ ++ Γ ▷ e ⟦0 ↟ ∥Δ∥⟧ : t ⟦0 ↟ ∥Δ∥⟧) := by
  rw ← list.nil_append Γ at h
  have := has_type_shift_ind h hw
  unfold ctx_shift list.length at this
  rw list.nil_append at this
  exact this

/- How typing interacts with substitution. -/

/-- Lean 3 does not have good specialised support for mutually inductive types.
    To carry out proofs using mutual induction, we have to define both motives beforehand. -/
def judgment_subst_ind_type : judgment_index → Prop
| (well_ctx Γ₀)      := ∀ {Γ t Δ} (h₀ : Γ₀ = Γ ++ t :: Δ) {r} (hr : Δ ▷ r : t), ▷ Γ ⟦↦↦ r⟧ ++ Δ
| (has_type Γ₀ l t₂) := ∀ {Γ t₁ Δ} (h₀ : Γ₀ = Γ ++ t₁ :: Δ) {r} (hr : Δ ▷ r : t₁), Γ ⟦↦↦ r⟧ ++ Δ ▷ l ⟦∥Γ∥ ↦ r⟧ : t₂ ⟦∥Γ∥ ↦ r⟧

/-- The mutual induction proof itself. -/
theorem judgment_subst_ind {i : judgment_index} (h : judgment i) : judgment_subst_ind_type i := by
  induction h
  case c_nil
    unfold judgment_subst_ind_type at *, intros Γ t Δ h₀ r hr
    rw list.nil_eq_append_iff at h₀, injection h₀.2
  case c_cons : Γ₀ t s ht iht
    unfold judgment_subst_ind_type at *, intros Γ t' Δ h₀ r hr
    cases Γ with t'' Γ ih'
      unfold ctx_subst, exact well_ctx_of_has_type hr
      rw list.cons_append at h₀, injection h₀ with h₁ h₂
      rw ← h₁ at h₀ ⊢, clear h₁ t''
      rw h₂ at ht iht, clear h₂ h₀ Γ₀
      specialize iht rfl hr, unfold subst at iht
      unfold ctx_subst
      exact c_cons iht
  case t_conv : Γ₀ e t t' s hc ht he iht ihe
    unfold judgment_subst_ind_type at *, intros Γ t₁ Δ h₀ r hr, rw h₀ at *, clear h₀ Γ₀
    specialize iht rfl hr, unfold subst at iht
    specialize ihe rfl hr
    exact t_conv (Defeq.subst_ind hc .refl _) iht ihe
  case t_sort : Γ₀ n hw ih
    unfold judgment_subst_ind_type at *, intros Γ t₁ Δ h₀ r hr, rw h₀ at *, clear h₀ Γ₀
    specialize ih rfl hr
    unfold subst, exact t_sort ih
  case t_var : Γ₀ n t hw ht ih
    unfold judgment_subst_ind_type at *, intros Γ t₁ Δ h₀ r hr, rw h₀ at *, clear h₀ Γ₀
    specialize ih rfl hr
    rcases Nat.lt_trichotomy ∥Γ∥ n with h₁ | h₁ | h₁
      cases n with n,   exfalso, exact Nat.not_lt_zero _ h₁
      rw [subst_lt h₁]
      obtain ⟨m, hm⟩ := Nat.le.dest (Nat.le_of_lt_succ h₁)
      have := @shift_subst_inside t r ∥Γ∥ m.succ, rw [Nat.add_succ, hm] at this
      rw [this, Nat.pred_succ], clear this
      refine t_var ih _
      have := hm, rw [← @ctx_subst_length Γ r] at this
      rw [← this, list.nth_aux_2], clear this
      rw [← hm, ← Nat.add_succ, list.nth_aux_2] at ht
      exact ht
      have := @shift_subst_inside t r n 0, rw [Nat.add_zero] at this
      rw [h₁, subst_eq, this], clear this
      rw [← h₁, list.nth_aux_4] at ht, injection ht with ht, rw ht at hr
      have := has_type_shift hr ih, rw [ctx_subst_length, h₁] at this
      exact this
      rw [subst_gt h₁]
      obtain ⟨m, hm⟩ := Nat.le.dest (Nat.succ_le_of_lt h₁)
      rw [← hm, shift_subst_above]
      refine t_var ih _
      rw [list.nth_aux_3 _ _ _ _ h₁] at ht
      rw [← @ctx_subst_length Γ r] at h₁
      rw [list.nth_aux_1 _ _ _ h₁]
      exact ctx_subst_nth ht hm _
  case t_app : Γ₀ l r t₁ t₂ hl hr ihl ihr
    unfold judgment_subst_ind_type at *, intros Γ t₁' Δ h₀ r' hr', rw h₀ at *, clear h₀ Γ₀
    specialize ihl rfl hr'
    specialize ihr rfl hr'
    unfold subst at ihl ⊢, rw ← subst_subst
    exact t_app ihl ihr
  case t_lam : Γ₀ t₁ t₂ s e hs he iht ihe
    unfold judgment_subst_ind_type at *, intros Γ t₁' Δ h₀ r hr, rw h₀ at *, clear h₀ Γ₀
    specialize iht rfl hr
    rw ← list.cons_append at he ihe
    specialize ihe rfl hr, unfold ctx_subst at ihe
    unfold subst at iht ⊢
    exact t_lam iht ihe
  case t_pi : Γ₀ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
    unfold judgment_subst_ind_type at *, intros Γ t₁' Δ h₀ r hr, rw h₀ at *, clear h₀ Γ₀
    specialize iht₁ rfl hr
    rw ← list.cons_append at ht₂ iht₂
    specialize iht₂ rfl hr, unfold ctx_subst at iht₂
    unfold subst at iht₁ iht₂ ⊢
    exact t_pi iht₁ iht₂

theorem well_ctx_subst_ind {Γ t Δ} (h : ▷ Γ ++ t :: Δ) {r} (hr : Δ ▷ r : t) :
  (▷ Γ ⟦↦↦ r⟧ ++ Δ) :=
    judgment_subst_ind h rfl hr

theorem has_type_subst_ind {Γ t₁ Δ l t₂} (h : Γ ++ t₁ :: Δ ▷ l : t₂) {r} (hr : Δ ▷ r : t₁) :
  (Γ ⟦↦↦ r⟧ ++ Δ ▷ l ⟦∥Γ∥ ↦ r⟧ : t₂ ⟦∥Γ∥ ↦ r⟧) :=
    judgment_subst_ind h rfl hr

theorem has_type_subst {t₁ Γ l t₂} (h : t₁ :: Γ ▷ l : t₂) {r} (hr : Γ ▷ r : t₁) :
  (Γ ▷ l ⟦0 ↦ r⟧ : t₂ ⟦0 ↦ r⟧) := by
  rw ← list.nil_append (t₁ :: Γ) at h
  have := has_type_subst_ind h hr
  unfold ctx_subst at this
  rw list.nil_append at this
  exact this

/-- The weakening rule. -/
theorem has_type_of_ctx_cons {Γ e t} (h : Γ ▷ e : t) {t' s} (ht : Γ ▷ t' : sort s) :
  (t' :: Γ) ▷ e ⟦0 ↟ 1⟧ : t ⟦0 ↟ 1⟧ :=
    @has_type_shift _ _ _ h [t'] (c_cons ht)

/-- Every entry in a well-formed context has type `sort n`. -/
theorem has_sort_of_well_ctx_nth {Γ} (hw : ▷ Γ) {n t} (h : list.nth Γ n = option.some t) :
  ∃ s, (Γ ▷ t ⟦0 ↟ n.succ⟧ : sort s) := by
  induction Γ with t' Γ ih generalizing n
    injection h
    cases n with n
      injection h with h, subst h, clear h
      rcases hw with _ | @⟨Γ, t, s, ht⟩ | _
      have := has_type_of_ctx_cons ht ht, unfold shift at this
      exact ⟨s, this⟩
      unfold list.nth at h
      rcases hw with _ | @⟨Γ, t, s, ht⟩ | _
      specialize ih (well_ctx_of_has_type ht) h
      rcases ih with ⟨s, hs⟩
      have := has_type_of_ctx_cons hs ht, unfold shift at this
      have h' := shift_shift_overlap t 0 n.succ 1, rw zero_add at h', rw h' at this
      exact ⟨s, this⟩

/-- Auxiliary proposition for proving the classification lemma. -/
def has_sort_aux_type : ctx → Expr → Prop
| Γ (sort s)   := (∃ s', Γ ▷ sort s : sort s')
| Γ (var v)    := (∃ s, Γ ▷ var v : sort s)
| Γ (app l r)  := (∃ s, Γ ▷ app l r : sort s)
| Γ (lam t e)  := (∃ s, Γ ▷ lam t e : sort s)
| Γ (pi t₁ t₂) :=
  (∃ s, Γ ▷ pi t₁ t₂ : sort s) ∧
  has_sort_aux_type Γ t₁ ∧
  has_sort_aux_type (t₁ :: Γ) t₂

theorem has_sort_aux_elim {Γ e} (h : has_sort_aux_type Γ e) : ∃ s, Γ ▷ e : sort s := by
  cases e
  case sort : s   exact h
  case var : v   exact h
  case app : l r   exact h
  case lam : t e   exact h
  case pi : t₁ t₂   exact h.1

theorem has_sort_aux_pi {Γ t₁ t₂ t} (h : Γ ▷ pi t₁ t₂ : t) : (∃ s, Γ ▷ t₁ : sort s) ∧ (∃ s, t₁ :: Γ ▷ t₂ : sort s) := by
  induction' h
  case t_conv : _ _ _ _ hc _ _ _ ihe   exact ihe
  case t_pi : _ _ s₁ _ s₂ ht₁ ht₂ _ _   exact ⟨⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩⟩

/-- Need this to recover typing judgments on RHS of pi's. -/
theorem has_sort_aux {Γ e} (h : ∃ s, Γ ▷ e : sort s) : has_sort_aux_type Γ e := by
  induction e generalizing Γ
  case sort : s   exact h
  case var : v   exact h
  case app : l r ihl ihr   exact h
  case lam : t e iht ihe   exact h
  case pi : t₁ t₂ iht₁ iht₂
    split,   exact h
    obtain ⟨s, hs⟩ := h
    obtain ⟨h₁, h₂⟩ := has_sort_aux_pi hs
    split,   exact iht₁ h₁,   exact iht₂ h₂

/-- Classification lemma: the "type" assigned to any term must have type `sort n`. -/
theorem type_has_sort {Γ e t} (h : Γ ▷ e : t) : ∃ s, (Γ ▷ t : sort s) := by
  induction' h
  case t_conv : Γ e t t' s hc ht he iht ihe   exact ⟨s, ht⟩
  case t_sort : Γ n hw ih   exact ⟨_, t_sort hw⟩
  case t_var : Γ n t hw ht ih   exact has_sort_of_well_ctx_nth hw ht
  case t_app : Γ l r t₁ t₂ hl hr ihl ihr
    obtain ⟨s, hs⟩ := has_sort_aux_elim (has_sort_aux ihl).2.2
    have := has_type_subst hs hr, unfold subst at this
    exact ⟨s, this⟩
  case t_lam : Γ t₁ t₂ s e hs he iht ihe   exact ⟨s, hs⟩
  case t_pi : Γ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂   exact ⟨_, t_sort (well_ctx_of_has_type ht₁)⟩

/-- As a consequence, every well-formed term is either:
    (1) a sort
    (2) a type that is not a sort
    (3) a term that is not a type. -/
def is_sort (Γ : ctx) (e : Expr) : Prop := ∃ s, e = sort s
def is_type (Γ : ctx) (e : Expr) : Prop := ∃ s, Γ ▷ e : sort s
def is_term (Γ : ctx) (e : Expr) : Prop := ∃ t, Γ ▷ e : t ∧ ∃ s, Γ ▷ t : sort s

/- Auxiliary typing judgment lemmas. -/

theorem app_has_type_aux {Γ l r t} (h : Γ ▷ app l r : t) :
  ∃ t₁ t₂, (Γ ▷ l : pi t₁ t₂) ∧ (Γ ▷ r : t₁) ∧ (t ~~ t₂ ⟦0 ↦ r⟧) := by
  induction' h
  case t_conv : _ _ _ _ hc _ _ _ ihe
    obtain ⟨t₁, t₂, ih₁, ih₂, ih₃⟩ := ihe
    exact ⟨t₁, t₂, ih₁, ih₂, .trans (.symm hc) ih₃⟩,
  case t_app : _ _ _ t₁ t₂ hl hr _ _
    exact ⟨t₁, t₂, hl, hr, .refl⟩

theorem lam_has_type_aux {Γ t₁ e t} (h : Γ ▷ lam t₁ e : t) :
  ∃ t₂ s, (Γ ▷ pi t₁ t₂ : sort s) ∧ (t₁ :: Γ ▷ e : t₂) ∧ (t ~~ pi t₁ t₂) := by
  induction' h
  case t_conv : _ _ _ _ hc _ _ _ ihe
    obtain ⟨t₂, s, ih₁, ih₂, ih₃⟩ := ihe
    exact ⟨t₂, s, ih₁, ih₂, .trans (.symm hc) ih₃⟩
  case t_lam : _ _  t₂ s _ ht₁ ht₂ _ _
    exact ⟨t₂, s, ht₁, ht₂, .refl⟩

theorem pi_has_type_aux {Γ t₁ t₂ t} (h : Γ ▷ pi t₁ t₂ : t) :
  ∃ s₁ s₂, (Γ ▷ t₁ : sort s₁) ∧ (t₁ :: Γ ▷ t₂ : sort s₂) ∧ (t ~~ sort (max s₁ s₂)) := by
  induction' h
  case t_conv : _ _ _ _ hc _ _ _ ihe
    obtain ⟨s₁, s₂, ih₁, ih₂, ih₃⟩ := ihe
    exact ⟨s₁, s₂, ih₁, ih₂, .trans (.symm hc) ih₃⟩
  case t_pi : _ _ s₁ _ s₂ ht₁ ht₂ _ _
    exact ⟨s₁, s₂, ht₁, ht₂, .refl⟩

/-- Auxiliary relation for proving the type preservation lemma. -/
inductive derived_ctx : ctx → ctx → Prop
| dc_nil                :                                                    derived_ctx [] []
| dc_cons {t t' Γ Γ' s} : (t ~~ t') → (Γ' ▷ t : sort s) → derived_ctx Γ Γ' → derived_ctx (t :: Γ) (t' :: Γ')
open derived_ctx

scoped notation Γ ` ~~dc `:50 Γ':50 := derived_ctx Γ Γ'

/-- A well-formed context derives itself. -/
theorem derived_ctx_self {Γ} (hw : ▷ Γ) : Γ ~~dc Γ := by
  induction Γ with t Γ ih
    exact dc_nil
    rcases hw with _ | @⟨Γ, t, s, ht⟩
    exact dc_cons .refl ht (ih (well_ctx_of_has_type ht))

/-- A term has the same type under derived contexts. -/
theorem has_type_of_derived_ctx {Γ e t} (h : Γ ▷ e : t) {Γ'} (hw : ▷ Γ') (hc : Γ ~~dc Γ') : (Γ' ▷ e : t) := by
  induction' h
  case t_conv : Γ e t t' s hc' ht he iht ihe
    exact t_conv hc' (iht hw hc) (ihe hw hc)
  case t_sort : Γ n hw' ih
    clear ih, exact t_sort hw
  case t_var : Γ n t hw' ht ih
    clear ih
    induction' hc
    case dc_nil   cases ht
    case dc_cons : u u' Γ Γ' s hc hx hc' ih
      rcases hw with _ | @⟨Γ', u', s', hu'⟩
      rcases hw' with _ | @⟨Γ, u, s, hu⟩
      cases n with n
        clear ih
        injection ht with this, subst this, clear ht
        have := has_type_of_ctx_cons hx hu', unfold shift at this
        refine t_conv (Defeq.shift (.symm hc) _) this _, clear this
        exact t_var (c_cons hu') rfl
        unfold list.nth at ht
        specialize ih (well_ctx_of_has_type hu') (well_ctx_of_has_type hu) ht
        have h := has_type_of_ctx_cons ih hu'
        rw [shift_le (Nat.zero_le _)] at h
        have := shift_shift_overlap t 0 n.succ 1, rw Nat.zero_add at this, rw this at h, clear this
        exact h
  case t_app : Γ l r t₁ t₂ hl hr ihl ihr
    exact t_app (ihl hw hc) (ihr hw hc)
  case t_lam : Γ t₁ t₂ s e hs he iht ihe
    specialize iht hw hc
    obtain ⟨s, hs⟩ := has_sort_aux_elim (has_sort_aux ⟨s, iht⟩).2.1
    specialize ihe (c_cons hs) (dc_cons .refl hs hc)
    exact t_lam iht ihe
  case t_pi : Γ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
    specialize iht₁ hw hc
    specialize iht₂ (c_cons iht₁) (dc_cons .refl iht₁ hc)
    exact t_pi iht₁ iht₂

/-- Prepending definitionally equal types to a context gives the same type for any term. -/
theorem has_type_of_derived_ctx_aux {u Γ e t}
  (h : u :: Γ ▷ e : t) {u'} (hc : u ~~ u') {s} (h' : Γ ▷ u' : sort s) :
  (u' :: Γ ▷ e : t) := by
  rcases (well_ctx_of_has_type h) with _ | @⟨Γ, u, s', hu⟩
  have := dc_cons hc hu (derived_ctx_self (well_ctx_of_has_type h'))
  exact has_type_of_derived_ctx h (c_cons h') this

/-- Small-step reduction preserves type. -/
theorem has_type_Small {Γ e t} (h : Γ ▷ e : t) {e'} (h' : e ~> e') : (Γ ▷ e' : t) := by
  induction' h'
  case s_beta : t₁ e r
    obtain ⟨t₁', t₂', h₁, h₂, h₃⟩ := app_has_type_aux h
    obtain ⟨s, hs⟩ := type_has_sort h, clear h
    refine t_conv (.symm h₃) hs _, clear h₃ hs s t
    obtain ⟨t₂, s, h₃, h₄, h₅⟩ := lam_has_type_aux h₁
    obtain ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩ := has_sort_aux_pi h₃, clear h₃ s
    obtain ⟨s, hs⟩ := type_has_sort h₁, clear h₁
    obtain ⟨⟨s₁', hs₁'⟩, ⟨s₂', hs₂'⟩⟩ := has_sort_aux_pi hs, clear hs s
    obtain ⟨hc₁, hc₂⟩ := Defeq_of_pi_Defeq h₅, clear h₅
    have := has_type_subst hs₂' h₂, unfold subst at this
    refine t_conv (.symm (Defeq_subst hc₂ .refl)) this _, clear this
    exact has_type_subst h₄ (t_conv hc₁ hs₁ h₂)
  case s_app_left : l l' r hl ihl
    obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := app_has_type_aux h
    obtain ⟨s, hs⟩ := type_has_sort h, clear h
    refine t_conv (.symm h₃) hs _, clear h₃ hs s t
    exact t_app (ihl h₁) h₂
  case s_app_right : l r r' hr ihr
    obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := app_has_type_aux h
    obtain ⟨s, hs⟩ := type_has_sort h, clear h
    replace h₃ := .trans h₃ (Defeq_subst .refl (.step hr))
    refine t_conv (.symm h₃) hs _, clear h₃ hs s t
    exact t_app h₁ (ihr h₂)
  case s_lam_left : t₁ t₁' e ht iht
    obtain ⟨t₂, s, h₁, h₂, h₃⟩ := lam_has_type_aux h
    obtain ⟨s, hs⟩ := type_has_sort h, clear h
    replace h₃ := .trans h₃ (pi_defeq_aux (.step ht) .refl)
    refine t_conv (.symm h₃) hs _, clear h₃ hs s t
    obtain ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩ := has_sort_aux_pi h₁, clear h₁ s
    exact t_lam (t_pi (iht hs₁)
      (has_type_of_derived_ctx_aux hs₂ ht (iht hs₁)))
      (has_type_of_derived_ctx_aux h₂ ht (iht hs₁))
  case s_lam_right : t₁ e e' he ihe
    obtain ⟨t₂, s, h₁, h₂, h₃⟩ := lam_has_type_aux h
    obtain ⟨s, hs⟩ := type_has_sort h, clear h
    refine t_conv (.symm h₃) hs _, clear h₃ hs s t
    exact t_lam h₁ (ihe h₂)
  case s_pi_left : t₁ t₁' t₂ ht₁ iht₁
    obtain ⟨s₁, s₂, h₁, h₂, h₃⟩ := pi_has_type_aux h
    obtain ⟨s, hs⟩ := type_has_sort h, clear h
    refine t_conv (.symm h₃) hs _, clear h₃ hs s t
    exact t_pi (iht₁ h₁) (has_type_of_derived_ctx_aux h₂ ht₁ (iht₁ h₁))
  case s_pi_right : t₁ t₂ t₂' ht₂ iht₂
    obtain ⟨s₁, s₂, h₁, h₂, h₃⟩ := pi_has_type_aux h
    obtain ⟨s, hs⟩ := type_has_sort h, clear h
    refine t_conv (.symm h₃) hs _, clear h₃ hs s t
    exact t_pi h₁ (iht₂ h₂)

theorem has_type_SmallStar.{Γ e t} (h : Γ ▷ e : t) {e'} (h' : e ~>* e') : (Γ ▷ e' : t) := by
  induction h'
  case .refl : e   exact h
  case .step : e₁ e₂ e₃ h₁ h₂ ih   exact has_type_Small (ih h) h₂

/-- Equal, well-formed terms have the same type. -/
theorem has_type_Defeq {Γ e t} (h : Γ ▷ e : t) {e' t'} (h' : Γ ▷ e' : t') (hc : e ~~ e') : t ~~ t' :=
  let ⟨e'', h₁, h₁'⟩ := SmallStar.of_defeq hc in
    let h₂ := has_type_SmallStar.h h₁, h₂' := has_type_SmallStar.h' h₁' in
      has_type_unique h₂ h₂'

/-- Simplified conversion rule. -/
theorem has_type_conv_SmallStar.{Γ e t} (h : Γ ▷ e : t) {t'} (h' : t ~>* t') : (Γ ▷ e : t') := by
  obtain ⟨s, hs⟩ := type_has_sort h
  exact t_conv (Defeq.of_small_star. h' .refl) (has_type_SmallStar.hs h') h

-/

end
end Expr

end
end Coc
