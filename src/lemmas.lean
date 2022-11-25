import tactic
import data.prod.lex
import expr

namespace coc
section

set_option pp.structure_projections false

local notation e ` ⟦` n ` ↦ ` e' `⟧`  := expr.subst e n e'
local notation e ` ⟦` n ` ↟ ` m `⟧`   := expr.shift e n m
local notation e ` ~> ` e'            := small e e'
local notation e ` ~>* ` e'           := small_star e e'
local notation Γ ` ⊢ ` e `: ` t       := has_type Γ e t
local notation `⊢ ` Γ                 := ctx_wf Γ

/- Auxiliary arithmetic lemmas. -/

lemma nat.order_aux_1 {a b : nat} (h₁ : ¬a < b) (h₂ : ¬a = b) : (b < a) := ne.lt_of_le (ne.symm h₂) (le_of_not_gt h₁)
lemma nat.order_aux_2 {a b c : nat} (h : a + b < c) : b < c := lt_of_le_of_lt (nat.le_add_left b a) h
lemma nat.order_aux_3 {a b c : nat} (h : a + b < c) : a < c := lt_of_le_of_lt (nat.le_add_right a b) h
lemma nat.le_add_left' (a b c : ℕ) (h : a ≤ b) : a ≤ c + b := le_add_left h
lemma nat.le_add_right' (a b c : ℕ) (h : a ≤ b) : a ≤ b + c := le_add_right h

-- #check @nat.le.intro
-- #check @nat.le.dest

namespace expr
section

open idx

/- Uninteresting `shift` lemmas for supporting case analysis. -/

lemma shift_le {v n m} (h : n ≤ v) : var (bound v) ⟦n ↟ m⟧ = var (bound (v + m)) := by
{ unfold shift, split_ifs, refl }

lemma shift_gt {v n m} (h : v < n) : var (bound v) ⟦n ↟ m⟧ = var (bound v) := by
{ unfold shift, split_ifs with hif, exfalso, exact not_le_of_lt h hif, refl }

/- Uninteresting `subst` lemmas for supporting case analysis. -/

lemma subst_lt {v n e'} (h : n < v) : var (bound v) ⟦n ↦ e'⟧ = var (bound (nat.pred v)) := by
{ unfold subst, split_ifs, refl }

lemma subst_eq {n e'} : var (bound n) ⟦n ↦ e'⟧ = e' ⟦0 ↟ n⟧ := by
{ unfold subst, split_ifs with hif, { exfalso, exact nat.lt_irrefl _ hif }, refl }

lemma subst_gt {v n e'} (h : v < n) : var (bound v) ⟦n ↦ e'⟧ = var (bound v) := by
{ unfold subst, split_ifs with hif₁ hif₂,
  { exfalso, exact nat.lt_irrefl _ (nat.lt_trans h hif₁) },
  { rw hif₂ at h, exfalso, exact nat.lt_irrefl _ h },
  refl }

/- How `shift` interacts with itself. -/

lemma shift_zero (e n) : e ⟦n ↟ 0⟧ = e := by
{ induction e generalizing n,
  case sort : s { unfold shift },
  case var : v { cases v; unfold shift; split_ifs; simp },
  case app : l r ihl ihr { unfold shift, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold shift, rw [iht, ihe] },
  case pi : t₁ t₂ iht₁ iht₂ { unfold shift, rw [iht₁, iht₂] } }

lemma shift_shift_disjoint_ind (e k a b c) : e ⟦(b + k) ↟ c⟧ ⟦k ↟ a⟧ = e ⟦k ↟ a⟧ ⟦(a + b + k) ↟ c⟧ := by
{ induction e generalizing k,
  case sort : s { unfold shift },
  case var : v
  { cases v, swap, { unfold shift },
    rcases (lt_or_le v k) with h₁ | h₁,
    { rw [shift_gt (nat.lt_add_left _ _ _ h₁),
          shift_gt h₁,
          shift_gt (nat.lt_add_left _ _ _ h₁)] },
    rcases (lt_or_le v (b + k)) with h₂ | h₂,
    { rw [shift_gt h₂,
          shift_le h₁, nat.add_comm, nat.add_assoc,
          shift_gt (nat.add_lt_add_left h₂ _)] },
    { rw [shift_le h₂,
          shift_le (nat.le_add_right' _ _ _ h₁),
          shift_le h₁, nat.add_comm v a, nat.add_assoc a b k,
          shift_le (nat.add_le_add_left h₂ _), nat.add_comm, nat.add_assoc] } },
  case app : l r ihl ihr { unfold shift, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold shift, rw [iht, ← nat.add_succ, ihe], refl },
  case pi : t₁ t₂ iht₁ iht₂ { unfold shift, rw [iht₁, ← nat.add_succ, iht₂], refl } }

lemma shift_shift_disjoint (e a b c) : e ⟦b ↟ c⟧ ⟦0 ↟ a⟧ = e ⟦0 ↟ a⟧ ⟦(a + b) ↟ c⟧ :=
  shift_shift_disjoint_ind e 0 a b c

lemma shift_shift_overlap_ind (e k a b c) : e ⟦k ↟ (a + b)⟧ ⟦(a + k) ↟ c⟧ = e ⟦k ↟ (a + b + c)⟧ := by
{ induction e generalizing k,
  case sort : s { unfold shift },
  case var : v
  { cases v, swap, { unfold shift },
    rcases (lt_or_le v k) with h | h,
    { rw [shift_gt h,
          shift_gt (nat.lt_add_left _ _ _ h),
          shift_gt h] },
    { rw [shift_le h, nat.add_comm a k, ← nat.add_assoc,
          shift_le (nat.le_add_right' _ _ _ (nat.add_le_add_right h _)),
          shift_le h, ← nat.add_assoc, ← nat.add_assoc] } },
  case app : l r ihl ihr { unfold shift, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold shift, rw [iht, ← nat.add_succ, ihe], },
  case pi : t₁ t₂ iht₁ iht₂ { unfold shift, rw [iht₁, ← nat.add_succ, iht₂] } }

lemma shift_shift_overlap (e a b c) : e ⟦0 ↟ (a + b)⟧ ⟦a ↟ c⟧ = e ⟦0 ↟ (a + b + c)⟧ :=
  shift_shift_overlap_ind e 0 a b c

/- How `shift` and `subst` interact with each other. -/

lemma shift_subst_above_ind (e e' k n m) : e ⟦k ↟ n⟧ ⟦(n + m + k) ↦ e'⟧ = e ⟦(m + k) ↦ e'⟧ ⟦k ↟ n⟧ := by
{ induction e generalizing k n m,
  case sort : s { unfold shift subst },
  case var : v
  { cases v, swap, { unfold shift subst },
    rcases (lt_or_le v k) with h₁ | h₁,
    { rw [shift_gt h₁,
          subst_gt (nat.lt_add_left _ _ _ h₁),
          subst_gt (nat.lt_add_left _ _ _ h₁),
          shift_gt h₁] },
    { rw shift_le h₁,
      rcases (nat.lt_trichotomy v (m + k)) with h₂ | h₂ | h₂,
      { rw [subst_gt h₂, nat.add_comm, nat.add_assoc,
            subst_gt (nat.add_lt_add_left h₂ _),
            shift_le h₁, nat.add_comm] },
      { rw [nat.add_comm, nat.add_assoc, h₂,
            subst_eq,
            subst_eq, nat.add_comm, nat.add_comm m k,
            shift_shift_overlap _ _ _ _] },
      { cases v, { exfalso, exact nat.not_lt_zero _ h₂, },
        rw [nat.add_comm, nat.add_assoc,
            subst_lt (nat.add_lt_add_left h₂ _),
            subst_lt h₂, nat.add_succ, nat.pred_succ, nat.pred_succ,
            shift_le (nat.le_of_lt_succ (nat.order_aux_2 h₂)), nat.add_comm] } } },
  case app : l r hl hr { unfold shift subst, rw [hl, hr] },
  case lam : t e ht he { unfold shift subst, rw [ht, ← nat.add_succ, he], refl },
  case pi : t₁ t₂ ht₁ ht₂ { unfold shift subst, rw [ht₁, ← nat.add_succ, ht₂], refl } }

lemma shift_subst_above (e e' n m) : e ⟦0 ↟ n⟧ ⟦(n + m) ↦ e'⟧ = e ⟦m ↦ e'⟧ ⟦0 ↟ n⟧ :=
  shift_subst_above_ind e e' 0 n m

lemma shift_subst_inside_ind (e e' k n m) : e ⟦k ↟ nat.succ (n + m)⟧ ⟦(n + k) ↦ e'⟧ = e ⟦k ↟ (n + m)⟧ := by
{ induction e generalizing k,
  case sort : s { unfold shift subst },
  case var : v
  { cases v, swap, { unfold shift subst },
    rcases (lt_or_le v k) with h₁ | h₁,
    { rw [shift_gt h₁,
          shift_gt h₁,
          subst_gt (nat.lt_add_left _ _ _ h₁)] },
    { rw [shift_le h₁,
          shift_le h₁, nat.add_succ, ← nat.add_assoc, nat.add_comm n k,
          subst_lt (nat.lt_succ_of_le (nat.le_add_right' _ _ _ (nat.add_le_add_right h₁ _))),
          nat.pred_succ] } },
  case app : l r hl hr { unfold shift subst, rw [hl, hr] },
  case lam : t e ht he { unfold shift subst, rw [ht, ← nat.add_succ n k, he] },
  case pi : t₁ t₂ ht₁ ht₂ { unfold shift subst, rw [ht₁, ← nat.add_succ n k, ht₂] } }

lemma shift_subst_inside (e e') {n m} : e ⟦0 ↟ nat.succ (n + m)⟧ ⟦n ↦ e'⟧ = e ⟦0 ↟ (n + m)⟧ :=
  shift_subst_inside_ind e e' 0 n m

lemma shift_subst_below_ind (e e' k n m) : e ⟦nat.succ (n + k) ↟ m⟧ ⟦k ↦ e' ⟦n ↟ m⟧⟧ = e ⟦k ↦ e'⟧ ⟦(n + k) ↟ m⟧ := by
{ induction e generalizing k,
  case sort : s { unfold shift subst },
  case var : v
  { cases v, swap, { unfold shift subst },
    rcases (nat.lt_trichotomy v k) with h₁ | h₁ | h₁,
    { rw [shift_gt (nat.lt_succ_of_lt (nat.lt_add_left _ _ _ h₁)),
          subst_gt h₁,
          subst_gt h₁,
          shift_gt (nat.lt_add_left _ _ _ h₁)] },
    { rw [← h₁,
          shift_gt (nat.lt_succ_of_le (nat.le_add_left' _ _ _ (nat.le_refl v))),
          subst_eq,
          subst_eq, nat.add_comm,
          shift_shift_disjoint] },
    { cases v, { exfalso, exact nat.not_lt_zero _ h₁ },
      rw subst_lt h₁,
      rcases (lt_or_le v (n + k)) with h₂ | h₂,
      { rw [shift_gt (nat.succ_lt_succ h₂), nat.pred_succ,
            subst_lt h₁,
            shift_gt h₂, nat.pred_succ] },
      { rw [shift_le (nat.succ_le_succ h₂), nat.pred_succ,
            subst_lt (nat.lt_add_right _ _ _ h₁), nat.succ_add,
            shift_le h₂, nat.pred_succ] } } },
  case app : l r ihl ihr { unfold shift subst, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold shift subst, rw [iht, ← nat.add_succ, ihe],  },
  case pi : t₁ t₂ iht₁ iht₂ { unfold shift subst, rw [iht₁, ← nat.add_succ, iht₂] } }

lemma shift_subst_below (e e' n m) : e ⟦nat.succ n ↟ m⟧ ⟦0 ↦ e' ⟦n ↟ m⟧⟧ = e ⟦0 ↦ e'⟧ ⟦n ↟ m⟧ :=
  shift_subst_below_ind e e' 0 n m

/- How `subst` interacts with itself. -/

lemma subst_subst_ind (e e₁ e₂ k n) : e ⟦nat.succ (n + k) ↦ e₂⟧ ⟦k ↦ e₁ ⟦n ↦ e₂⟧⟧ = e ⟦k ↦ e₁⟧ ⟦(n + k) ↦ e₂⟧ := by
{ induction e generalizing e₁ e₂ k n,
  case sort : s { unfold subst },
  case var : v
  { cases v, swap, { unfold subst },
    rcases (nat.lt_trichotomy v k) with h₁ | h₁ | h₁,
    { rw [subst_gt h₁,
          subst_gt (nat.lt_add_left _ _ _ h₁),
          subst_gt (nat.lt_succ_of_lt (nat.lt_add_left _ _ _ h₁)),
          subst_gt h₁] },
    { rw [← h₁,
          subst_eq,
          subst_gt (nat.lt_succ_of_le (nat.le_add_left' _ _ _ (nat.le_refl v))),
          subst_eq, nat.add_comm,
          shift_subst_above _ _ _ _] },
    { cases v, { exfalso, exact nat.not_lt_zero _ h₁ },
      rcases (nat.lt_trichotomy v (n + k)) with h₂ | h₂ | h₂,
      { rw [subst_lt h₁, nat.pred_succ,
            subst_gt h₂,
            subst_gt (nat.succ_lt_succ h₂),
            subst_lt h₁, nat.pred_succ] },
      { rw [← h₂,
            subst_lt h₁, nat.pred_succ,
            subst_eq,
            subst_eq, h₂, nat.add_comm,
            shift_subst_inside] },
      { rw [subst_lt h₁, nat.pred_succ,
            subst_lt h₂,
            subst_lt (nat.succ_lt_succ h₂), nat.pred_succ,
            subst_lt (nat.order_aux_2 h₂)] } } },
  case app : l r ihl ihr { unfold subst, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold subst, rw [iht, ← nat.add_succ, ihe] },
  case pi : t₁ t₂ iht₁ iht₂ { unfold subst, rw [iht₁, ← nat.add_succ, iht₂] } }

lemma subst_subst (e e₁ e₂ n) : e ⟦(nat.succ n) ↦ e₂⟧ ⟦0 ↦ e₁ ⟦n ↦ e₂⟧⟧ = e ⟦0 ↦ e₁⟧ ⟦n ↦ e₂⟧ :=
  subst_subst_ind e e₁ e₂ 0 n

/- Uninteresting `size` lemmas to support strong induction on `expr`. -/

lemma size_wf : well_founded (λ e₁ e₂ : expr, size e₁ < size e₂) := measure_wf size
lemma size_lt_size_app_l {l r} : size l < size (app l r) := by { unfold size, rw [← nat.add_succ], simp }
lemma size_lt_size_app_r {l r} : size r < size (app l r) := by { unfold size, rw [nat.add_comm, ← nat.add_succ], simp }
lemma size_lt_size_lam_l {l r} : size l < size (lam l r) := by { unfold size, rw [← nat.add_succ], simp }
lemma size_lt_size_lam_r {l r} : size r < size (lam l r) := by { unfold size, rw [nat.add_comm, ← nat.add_succ], simp }
lemma size_lt_size_pi_l {l r} : size l < size (pi l r) := by { unfold size, rw [← nat.add_succ], simp }
lemma size_lt_size_pi_r {l r} : size r < size (pi l r) := by { unfold size, rw [nat.add_comm, ← nat.add_succ], simp }
lemma size_lt_size_app_lam_e {t e r} : size e < size (app (lam t e) r) :=
  nat.lt_trans size_lt_size_lam_r size_lt_size_app_l

/-- The "one-step reduction" relation `red_1 e₁ e₂`:
    "`e₁` reduces to `e₂` by contracting zero or more immediate redexes."
    See: https://archive-pml.github.io/martin-lof/pdfs/An-Intuitionistic-Theory-of-Types-1972.pdf -/
inductive red_1 : expr → expr → Prop
| r1_beta {t e e' r r'}   : red_1 e e' → red_1 r r' →     red_1 (app (lam t e) r) (e'⟦0 ↦ r'⟧)
| r1_sort {s}             :                               red_1 (sort s) (sort s)
| r1_var  {v}             :                               red_1 (var v) (var v)
| r1_app  {l l' r r'}     : red_1 l l' → red_1 r r' →     red_1 (app l r) (app l' r')
| r1_lam  {t t' e e'}     : red_1 t t' → red_1 e e' →     red_1 (lam t e) (lam t' e')
| r1_pi   {t₁ t₁' t₂ t₂'} : red_1 t₁ t₁' → red_1 t₂ t₂' → red_1 (pi t₁ t₂) (pi t₁' t₂')
open red_1

local notation e ` ~>₁ ` e'       := red_1 e e'

lemma red_1_refl {e} : e ~>₁ e :=
  @expr.rec_on (λ e, e ~>₁ e) e
    (λ _, r1_sort) (λ _, r1_var) (λ _ _, r1_app) (λ _ _, r1_lam) (λ _ _, r1_pi)

lemma red_1_shift_ind (n e e' k) (h : e ~>₁ e') : e ⟦k ↟ n⟧ ~>₁ e' ⟦k ↟ n⟧ := by
{ -- Strong induction on `e` generalising `e' k h`.
  revert_after e, apply size_wf.induction e, intros e ih, intros,
  cases e,
  case sort : s { cases h, unfold shift, exact red_1_refl },
  case var : v { cases h, cases v; split_ifs <|> skip; exact red_1_refl },
  case app : l r
  { cases h,
    case r1_beta : t e e' r r' he hr
    { unfold shift, rw ← shift_subst_below,
      refine r1_beta (ih e _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_lam_e, size_lt_size_app_r] },
    case r1_app : l l' r r' hl hr
    { unfold shift, refine r1_app (ih l _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_l, size_lt_size_app_r] } },
  case lam : t e
  { cases h, unfold shift,
    refine r1_lam (ih t _ _ _ _) (ih e _ _ _ _), assumption',
    exacts [size_lt_size_lam_l, size_lt_size_lam_r] },
  case pi : t₁ t₂
  { cases h, unfold shift,
    refine r1_pi (ih t₁ _ _ _ _) (ih t₂ _ _ _ _), assumption',
    exacts [size_lt_size_pi_l, size_lt_size_pi_r] } }

lemma red_1_shift (n) {e e'} (h : e ~>₁ e') : e ⟦0 ↟ n⟧ ~>₁ e' ⟦0 ↟ n⟧ :=
  red_1_shift_ind n e e' 0 h

lemma red_1_subst_ind {l l'} (hl : l ~>₁ l') {r r'} (hr : r ~>₁ r') (k) : l ⟦k ↦ r⟧ ~>₁ l' ⟦k ↦ r'⟧ := by
{ -- Strong induction on `l₀` generalising `l₀' hl₀ r₀ r₀' hr₀ k`.
  revert_after l, apply size_wf.induction l, intros l₀ ih l₀' hl₀ r₀ r₀' hr₀ k,
  cases l₀,
  case sort : s { cases hl₀, unfold subst, exact r1_sort },
  case var : v
  { cases v; cases hl₀; unfold subst, swap, apply r1_var,
    split_ifs; exact red_1_refl <|> skip,
    exact red_1_shift k hr₀ },
  case app : l r
  { cases hl₀,
    case r1_beta : t e e' r r' he hr
    { unfold subst, rw ← subst_subst,
      refine r1_beta (ih e _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_lam_e, size_lt_size_app_r] },
    case r1_app : l l' r r' hl hr
    { unfold subst,
      refine r1_app (ih l _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_l, size_lt_size_app_r] } },
  case lam : t e
  { cases hl₀, unfold subst,
    refine r1_lam (ih t _ _ _ _) (ih e _ _ _ _), assumption',
    exacts [size_lt_size_lam_l, size_lt_size_lam_r] },
  case pi : t₁ t₂
  { cases hl₀, unfold subst,
    refine r1_pi (ih t₁ _ _ _ _) (ih t₂ _ _ _ _), assumption',
    exacts [size_lt_size_pi_l, size_lt_size_pi_r] } }

lemma red_1_subst {l l'} (hl : l ~>₁ l') {r r'} (hr : r ~>₁ r') : l ⟦0 ↦ r⟧ ~>₁ l' ⟦0 ↦ r'⟧ :=
  red_1_subst_ind hl hr 0

/-- Confluence of one-step reduction. -/
lemma red_1_confluent {a b c} (hb : a ~>₁ b) (hc : a ~>₁ c) : ∃ d, (b ~>₁ d) ∧ (c ~>₁ d) := by
{ -- Strong induction on `a` generalising `b c hb hc`.
  revert_after a, apply size_wf.induction a, intros a ih, intros,
  cases a,
  case sort : s { cases hb, cases hc, use (sort s), exact ⟨r1_sort, r1_sort⟩, },
  case var : v { cases hb, cases hc, use (var v), exact ⟨r1_var, r1_var⟩ },
  case app : l r
  { cases hb,
    case r1_beta : t e eb r rb heb hrb
    { cases hc,
      case r1_beta : t e ec r rc hec hrc
      { rcases (ih e size_lt_size_app_lam_e heb hec) with ⟨e', _, _⟩,
        rcases (ih r size_lt_size_lam_r hrb hrc) with ⟨r', _, _⟩,
        use (e' ⟦0 ↦ r'⟧), refine ⟨red_1_subst _ _, red_1_subst _ _⟩, assumption' },
      case r1_app : tec r rc htec hrc
      { rcases htec with _ | _ | _ | _ | @⟨t, tc, e, ec, htc, hec⟩ | _,
        rcases (ih e size_lt_size_app_lam_e heb hec) with ⟨e', _, _⟩,
        rcases (ih r size_lt_size_app_r hrb hrc) with ⟨r', _, _⟩,
        use (e' ⟦0 ↦ r'⟧), refine ⟨red_1_subst _ _, r1_beta _ _⟩, assumption' } },
    case r1_app : te teb r rb hteb hrb
    { cases hc,
      case r1_beta : t e ec r rc hec hrc
      { rcases hteb with _ | _ | _ | _ | @⟨t, tb, e, eb, htb, heb⟩ | _,
        rcases (ih e size_lt_size_app_lam_e heb hec) with ⟨e', _, _⟩,
        rcases (ih r size_lt_size_app_r hrb hrc) with ⟨r', _, _⟩,
        use (e' ⟦0 ↦ r'⟧), refine ⟨r1_beta _ _, red_1_subst _ _⟩, assumption' },
      case r1_app : l lc r rc hlc hrc
      { rcases (ih l size_lt_size_app_l hteb hlc) with ⟨l', _, _⟩,
        rcases (ih r size_lt_size_app_r hrb hrc) with ⟨r', _, _⟩,
        use (app l' r'), refine ⟨r1_app _ _, r1_app _ _⟩, assumption' } } },
  case lam : l r
  { rcases hb with _ | _ | _ | _ | @⟨l, lb, r, rb, hlb, hrb⟩ | _,
    rcases hc with _ | _ | _ | _ | @⟨l, lc, r, rc, hlc, hrc⟩ | _,
    rcases (ih l size_lt_size_lam_l hlb hlc) with ⟨l', _, _⟩,
    rcases (ih r size_lt_size_lam_r hrb hrc) with ⟨r', _, _⟩,
    use (lam l' r'), refine ⟨r1_lam _ _, r1_lam _ _⟩, assumption' },
  case pi : l r
  { rcases hb with _ | _ | _ | _ | _ | @⟨l, lb, r, rb, hlb, hrb⟩,
    rcases hc with _ | _ | _ | _ | _ | @⟨l, lc, r, rc, hlc, hrc⟩,
    rcases (ih l size_lt_size_pi_l hlb hlc) with ⟨l', hl₁, hl₂⟩,
    rcases (ih r size_lt_size_pi_r hrb hrc) with ⟨r', hr₁, hr₂⟩,
    use (pi l' r'), refine ⟨r1_pi _ _, r1_pi _ _⟩, assumption' } }

/-- Transitive closure of one-step reduction. -/
inductive red_n : nat → expr → expr → Prop
| rn_refl {e}          :                                 red_n 0 e e
| rn_step {n e₁ e₂ e₃} : red_n n e₁ e₂ → (red_1 e₂ e₃) → red_n (nat.succ n) e₁ e₃
open red_n

local notation e ` ~>⟦` n `⟧ ` e' := red_n n e e'

/- Main part. -/
namespace red_n_confluent
section

-- instance : linear_order (nat ×ₗ nat) := infer_instance

-- #check to_lex
-- #check of_lex
#check prod.lex_wf nat.lt_wf nat.lt_wf
#check prod.lex.lt_iff
#check prod.lex.le_iff
#check prod.lex.left
#check prod.lex.right

/-- Auxiliary grid structure for proving confluence of `red_n`. -/
structure aux (n m : nat) (a b c : expr) (grid : nat → nat → expr) (cur : nat × nat) : Prop :=
  (ha : grid 0 0 = a) (hb : grid n 0 = b) (hc : grid 0 m = c)
  (go_down  (i j : nat) : i < n → j ≤ m → j = 0 ∨ to_lex (i.succ, j) ≤ to_lex cur → (grid i j ~>₁ grid i.succ j))
  (go_right (i j : nat) : i ≤ n → j < m → i = 0 ∨ to_lex (i, j.succ) ≤ to_lex cur → (grid i j ~>₁ grid i j.succ))

/-- The grid update function. -/
def update (grid : nat → nat → expr) (i j : nat) (e : expr) : nat → nat → expr :=
  λ i' j', if i' = i then (if j' = j then e else grid i' j') else grid i' j'

lemma update_eq {g i j e} : update g i j e i j = e := by
{ unfold update, split_ifs; refl }

lemma update_ne_fst {g i j e i' j'} (h : i' ≠ i) : update g i j e i' j' = g i' j' := by
{ unfold update, split_ifs; refl <|> contradiction }

lemma update_ne_snd {g i j e i' j'} (h : j' ≠ j) : update g i j e i' j' = g i' j' := by
{ unfold update, split_ifs; refl }

/-- Fill the zeroth row and column. -/
lemma init {n m a b c} (hb : a ~>⟦n⟧ b) (hc : a ~>⟦m⟧ c) : ∃ g, aux n m a b c g (0, 0) := by
{ induction n with n ihn generalizing b c,
  { -- Zeroth row
    rcases hb with hb | _,
    induction m with m ihm generalizing c,
    { cases hc, use (λ _ _, a), split; refl <|> skip,
      { intros _ _ h, exfalso, exact nat.not_lt_zero _ h },
      { intros _ _ _ h, exfalso, exact nat.not_lt_zero _ h } },
    rcases hc with _ | @⟨n, c₁, c₂, c₃, hc₁, hc₂⟩,
    rcases ihm hc₁ with ⟨g, ha, hb, hc, go_down, go_right⟩,
    use (update g 0 m.succ c), split,
    { rw update_ne_snd (nat.succ_ne_zero _).symm, exact ha },
    { rw update_ne_snd (nat.succ_ne_zero _).symm, exact ha },
    { rw update_eq },
    { intros i j hi hj h, exfalso, exact nat.not_lt_zero _ hi },
    { intros i j hi hj h,
      rw [update_ne_snd (ne_of_lt hj), nat.eq_zero_of_le_zero hi],
      cases lt_or_eq_of_le (nat.le_of_lt_succ hj) with hj hj,
      { rw update_ne_snd (ne_of_lt (nat.succ_lt_succ hj)),
        apply go_right 0 j, { refl }, { exact hj }, { left, refl } },
      { rw [hj, update_eq, hc], exact hc₂ } } },
  { -- Zeroth column; the rest we don't care now
    rcases hb with _ | @⟨m, b₁, b₂, b₃, hb₁, hb₂⟩,
    rcases ihn hb₁ hc with ⟨g, ha, hb, hc, go_down, go_right⟩,
    use (update g n.succ 0 b), split,
    { rw update_ne_fst (nat.succ_ne_zero _).symm, exact ha },
    { rw update_eq },
    { rw update_ne_fst (nat.succ_ne_zero _).symm, exact hc },
    { intros i j hi hj h,
      cases h with h h,
      { rw [h, update_ne_fst (ne_of_lt hi)],
        cases lt_or_eq_of_le (nat.le_of_lt_succ hi) with hi hi,
        { rw update_ne_fst (ne_of_lt (nat.succ_lt_succ hi)),
          apply go_down i 0, { exact hi }, { exact nat.zero_le _ }, { left, refl } },
        { rw [hi, update_eq, hb], exact hb₂ } },
      { rw prod.lex.le_iff at h,
        rcases h with h | ⟨h₁, h₂⟩,
        { exfalso, exact nat.not_lt_zero _ h },
        { exfalso, exact nat.succ_ne_zero _ h₁ } } },
    { intros i j hi hj h,
      cases h with h h,
      { rw h, apply go_right 0 j, { exact nat.zero_le _ }, { exact hj }, { left, refl } },
      { rw prod.lex.le_iff at h,
      rcases h with h | ⟨h₁, h₂⟩,
        { exfalso, exact nat.not_lt_zero _ h },
        { exfalso, exact nat.not_succ_le_zero _ h₂ } } } } }

/-- Fill the rest of the grid. -/
lemma traverse {n m a b c g} (h : aux n m a b c g (0, 0)) : ∀ cur, ∃ g', aux n m a b c g' cur := by
{ -- Induction on the lexical ordering of `cur`.
  intros cur, apply (prod.lex_wf nat.lt_wf nat.lt_wf).induction cur, rintros ⟨i, j⟩ ih,

  cases i with i,
  { -- Zeroth row (already done in `init`, we just need to move cursor)
    rcases h with ⟨ha, hb, hc, go_down, go_right⟩, refine ⟨g, ha, hb, hc, _, _⟩,
    { intros i' j' hi' hj' h, refine (go_down i' j' hi' hj' _),
      rw prod.lex.le_iff at h,
      rcases h with h | h | ⟨h₁, h₂⟩,
      { exact or.inl h },
      { exfalso, exact nat.not_lt_zero _ h },
      { exfalso, exact nat.succ_ne_zero _ h₁ } },
    { intros i' j' hi' hj' h, refine (go_right i' j' hi' hj' _),
      rw prod.lex.le_iff at h,
      rcases h with h | h | ⟨h₁, h₂⟩,
      { exact or.inl h },
      { exfalso, exact nat.not_lt_zero _ h },
      { exact or.inl h₁ } } },

  cases j with j,
  { -- Zeroth column (already done in `init`, we just need to move cursor)
    replace ih := ih (i, m) (prod.lex.left _ _ (lt_add_one i)),
    rcases ih with ⟨g, ha, hb, hc, go_down, go_right⟩,
    refine ⟨g, ha, hb, hc, _, _⟩,
    { intros i' j' hi' hj' h, refine (go_down i' j' hi' hj' _),
      rw prod.lex.le_iff at h,
      rcases h with h | h | ⟨h₁, h₂⟩,
      { exact or.inl h },
      { right, rw prod.lex.le_iff,
        cases (lt_or_eq_of_le (nat.le_of_lt_succ h)) with h h,
        { exact or.inl h },
        { exact or.inr ⟨h, hj'⟩ } },
      { left, replace h₂ : j' = 0 := nat.eq_zero_of_le_zero h₂, rw h₂ } },
    { intros i' j' hi' hj' h, refine (go_right i' j' hi' hj' _),
      rw prod.lex.le_iff at h,
      rcases h with h | h | ⟨h₁, h₂⟩,
      { exact or.inl h },
      { right, rw prod.lex.le_iff,
        cases (lt_or_eq_of_le (nat.le_of_lt_succ h)) with h h,
        { exact or.inl h },
        { exact or.inr ⟨h, hj'⟩ } },
      { exfalso, exact nat.not_succ_le_zero _ h₂ } } },

  -- Inductive case.
  replace ih := ih (i.succ, j) (prod.lex.right _ (lt_add_one j)),
  rcases ih with ⟨g, ha, hb, hc, go_down, go_right⟩,

  cases (lt_or_le i n) with hi hi, swap,
  { -- `i` overflow (no modification)
    refine ⟨g, ha, hb, hc, _, _⟩,
    { intros i' j' hi' hj' h, refine (go_down i' j' hi' hj' _),
      rw prod.lex.le_iff, right, left,
      exact nat.succ_lt_succ (nat.lt_of_lt_of_le hi' hi) },
    { intros i' j' hi' hj' h, refine (go_right i' j' hi' hj' _),
      rw prod.lex.le_iff, right, left,
      exact nat.lt_succ_of_le (nat.le_trans hi' hi) } },

  cases (lt_or_le j m) with hj hj, swap,
  { -- `j` overflow (no modification)
    refine ⟨g, ha, hb, hc, _, _⟩,
    { intros i' j' hi' hj' h, refine (go_down i' j' hi' hj' _),
      rw prod.lex.le_iff at h,
      rcases h with h | h | ⟨h₁, h₂⟩,
      { exact or.inl h },
      { right, rw prod.lex.le_iff, left, exact h },
      { right, rw prod.lex.le_iff, right, exact ⟨h₁, nat.le_trans hj' hj⟩ } },
    { intros i' j' hi' hj' h, refine (go_right i' j' hi' hj' _),
      rw prod.lex.le_iff at h,
      rcases h with h | h | ⟨h₁, h₂⟩,
      { exact or.inl h },
      { right, rw prod.lex.le_iff, left, exact h },
      { right, rw prod.lex.le_iff, right, exact ⟨h₁, nat.le_trans hj' hj⟩ } } },

  -- The only "interesting" case (but still trivial intuitively)...
  let a' := g i j, let b' := g i.succ j, let c' := g i j.succ,
  have hab' : (a' ~>₁ b') := go_down i j hi (nat.le_of_lt hj) (or.inr _), swap,
  { rw prod.lex.le_iff, right, exact ⟨rfl, nat.le_refl _⟩ },
  have hac' : (a' ~>₁ c') := go_right i j (nat.le_of_lt hi) hj (or.inr _), swap,
  { rw prod.lex.le_iff, left, exact lt_add_one _ },
  rcases (red_1_confluent hab' hac') with ⟨d', hbd', hcd'⟩,

  -- Modify grid, prove invariants.
  use (update g i.succ j.succ d'),
  split,
  { rw update_ne_fst (nat.succ_ne_zero _).symm, exact ha },
  { rw update_ne_snd (nat.succ_ne_zero _).symm, exact hb },
  { rw update_ne_fst (nat.succ_ne_zero _).symm, exact hc },
  { intros i' j' hi' hj' h,
    rw prod.lex.le_iff at h,
    rcases h with h | h | ⟨h₁, h₂⟩,
    { rw [h, update_ne_snd (nat.succ_ne_zero _).symm, update_ne_snd (nat.succ_ne_zero _).symm],
      exact go_down i' 0 hi' (nat.zero_le _) (or.inl rfl), },
    { unfold prod.fst at h,
      rw [update_ne_fst (ne_of_lt h), update_ne_fst (ne_of_lt (nat.lt_of_succ_lt h))],
      refine go_down i' j' hi' hj' _, right, rw prod.lex.le_iff, exact or.inl h },
    { unfold prod.fst prod.snd at h₁ h₂,
      replace h₁ := nat.succ.inj h₁,
      cases (lt_or_eq_of_le h₂) with h₂ h₂,
      { rw [h₁, update_ne_snd (ne_of_lt h₂), update_ne_snd (ne_of_lt h₂)],
        apply go_down i j' hi hj', right, rw prod.lex.le_iff,
        exact or.inr ⟨rfl, nat.le_of_lt_succ h₂⟩ },
      { rw [h₁, h₂, update_ne_fst (nat.succ_ne_self _).symm, update_eq], exact hcd' } } },
  { intros i' j' hi' hj' h,
    rw prod.lex.le_iff at h,
    rcases h with h | h | ⟨h₁, h₂⟩,
    { rw [h, update_ne_fst (nat.succ_ne_zero _).symm, update_ne_fst (nat.succ_ne_zero _).symm],
      exact go_right 0 j' (nat.zero_le _) hj' (or.inl rfl) },
    { unfold prod.fst at h,
      rw [update_ne_fst (ne_of_lt h), update_ne_fst (ne_of_lt h)],
      refine go_right i' j' hi' hj' _, right, rw prod.lex.le_iff, exact or.inl h },
    { unfold prod.fst prod.snd at h₁ h₂,
      replace h₂ := nat.le_of_succ_le_succ h₂,
      rw [h₁, update_ne_snd (ne_of_lt (nat.lt_succ_of_le h₂))],
      cases (lt_or_eq_of_le h₂) with h₂ h₂,
      { rw update_ne_snd (ne_of_lt (nat.succ_lt_succ h₂)),
        apply go_right i.succ j' (nat.succ_le_of_lt hi) hj', right, rw prod.lex.le_iff,
        exact or.inr ⟨rfl, nat.succ_le_of_lt h₂⟩ },
      { rw [h₂, update_eq], exact hbd' } } } }

/-- Extract conclusion from a filled grid. -/
lemma final {n m a b c g} (h : aux n m a b c g (n, m)) : ∃ d, (b ~>⟦m⟧ d) ∧ (c ~>⟦n⟧ d) := by
{ rcases h with ⟨ha, hb, hc, go_down, go_right⟩,
  use g n m, split,
  { -- Last row
    suffices : ∀ j, j ≤ m → (b ~>⟦j⟧ g n j), { exact this m (nat.le_refl _) },
    intros j,
    induction j with j hj,
    { intros ih, rw hb, exact rn_refl },
    { intros ih, apply @rn_step _ _ (g n j) _, { exact hj (nat.le_of_succ_le ih) },
      apply go_right, exact nat.le_refl _, exact nat.lt_of_succ_le ih,
      right, exact prod.lex.right _ ih, } },
  { -- Last column
    suffices : ∀ i, i ≤ n → (c ~>⟦i⟧ g i m), { exact this n (nat.le_refl _) },
    intros i,
    induction i with i hi,
    { intros ih, rw hc, exact rn_refl },
    { intros ih, apply @rn_step _ _ (g i m) _, { exact hi (nat.le_of_succ_le ih) },
      apply go_down, exact nat.lt_of_succ_le ih, exact nat.le_refl _,
      right, cases eq_or_lt_of_le ih with h h, rw h, exact prod.lex.left _ _ (nat.lt_of_succ_le h), } } }

end
end red_n_confluent

lemma red_n_confluent {n m a b c} (hb : a ~>⟦n⟧ b) (hc : a ~>⟦m⟧ c) : ∃ d, (b ~>⟦m⟧ d) ∧ (c ~>⟦n⟧ d) :=
  let ⟨_, aux₁⟩ := red_n_confluent.init hb hc,
      ⟨_, aux₂⟩ := red_n_confluent.traverse aux₁ (n, m)
  in (red_n_confluent.final aux₂)

end
end expr

end
end coc
