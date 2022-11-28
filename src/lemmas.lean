import tactic
import tactic.induction
import data.prod.lex
import expr

namespace coc
section

/- Notations. -/

set_option pp.structure_projections false

local notation e ` ⟦` n ` ↦ ` e' `⟧` := expr.subst e n e'
local notation e ` ⟦` n ` ↟ ` m `⟧`  := expr.shift e n m

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

/- Uninteresting `shift` lemmas for supporting case analysis. -/

lemma shift_le {v n m} (h : n ≤ v) : var v ⟦n ↟ m⟧ = var (v + m) := by
{ unfold shift, split_ifs, refl }

lemma shift_gt {v n m} (h : v < n) : var v ⟦n ↟ m⟧ = var v := by
{ unfold shift, split_ifs with hif, exfalso, exact not_le_of_lt h hif, refl }

/- Uninteresting `subst` lemmas for supporting case analysis. -/

lemma subst_lt {v n e'} (h : n < v) : var v ⟦n ↦ e'⟧ = var (nat.pred v) := by
{ unfold subst, split_ifs, refl }

lemma subst_eq {n e'} : var n ⟦n ↦ e'⟧ = e' ⟦0 ↟ n⟧ := by
{ unfold subst, split_ifs with hif, { exfalso, exact nat.lt_irrefl _ hif }, refl }

lemma subst_gt {v n e'} (h : v < n) : var v ⟦n ↦ e'⟧ = var v := by
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
  { rcases (lt_or_le v k) with h₁ | h₁,
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
  { rcases (lt_or_le v k) with h | h,
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
  { rcases (lt_or_le v k) with h₁ | h₁,
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
  { rcases (lt_or_le v k) with h₁ | h₁,
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

lemma shift_subst_inside (e e' n m) : e ⟦0 ↟ nat.succ (n + m)⟧ ⟦n ↦ e'⟧ = e ⟦0 ↟ (n + m)⟧ :=
  shift_subst_inside_ind e e' 0 n m

lemma shift_subst_below_ind (e e' k n m) : e ⟦nat.succ (n + k) ↟ m⟧ ⟦k ↦ e' ⟦n ↟ m⟧⟧ = e ⟦k ↦ e'⟧ ⟦(n + k) ↟ m⟧ := by
{ induction e generalizing k,
  case sort : s { unfold shift subst },
  case var : v
  { rcases (nat.lt_trichotomy v k) with h₁ | h₁ | h₁,
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
  { rcases (nat.lt_trichotomy v k) with h₁ | h₁ | h₁,
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
    "`e₁` reduces to `e₂` by contracting zero or more immediate redexes." -/
inductive red_1 : expr → expr → Prop
| r1_beta {t e e' r r'}   : red_1 e e' → red_1 r r' →     red_1 (app (lam t e) r) (e'⟦0 ↦ r'⟧)
| r1_sort {s}             :                               red_1 (sort s) (sort s)
| r1_var  {v}             :                               red_1 (var v) (var v)
| r1_app  {l l' r r'}     : red_1 l l' → red_1 r r' →     red_1 (app l r) (app l' r')
| r1_lam  {t t' e e'}     : red_1 t t' → red_1 e e' →     red_1 (lam t e) (lam t' e')
| r1_pi   {t₁ t₁' t₂ t₂'} : red_1 t₁ t₁' → red_1 t₂ t₂' → red_1 (pi t₁ t₂) (pi t₁' t₂')
open red_1

local notation e ` ~>₁ ` e' := red_1 e e'

lemma red_1_refl {e} : e ~>₁ e :=
  @expr.rec_on (λ e, e ~>₁ e) e
    (λ _, r1_sort) (λ _, r1_var) (λ _ _, r1_app) (λ _ _, r1_lam) (λ _ _, r1_pi)

/-- Shifting respects one-step reduction. -/
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

/-- Substitution respects one-step reduction. -/
lemma red_1_subst_ind {l l'} (hl : l ~>₁ l') {r r'} (hr : r ~>₁ r') (k) : l ⟦k ↦ r⟧ ~>₁ l' ⟦k ↦ r'⟧ := by
{ -- Strong induction on `l₀` generalising `l₀' hl₀ r₀ r₀' hr₀ k`.
  revert_after l, apply size_wf.induction l, intros l₀ ih l₀' hl₀ r₀ r₀' hr₀ k,
  cases l₀,
  case sort : s { cases hl₀, unfold subst, exact r1_sort },
  case var : v
  { cases hl₀; unfold subst,
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
      { obtain ⟨e', _, _⟩ := ih e size_lt_size_app_lam_e heb hec,
        obtain ⟨r', _, _⟩ := ih r size_lt_size_lam_r hrb hrc,
        use (e' ⟦0 ↦ r'⟧), refine ⟨red_1_subst _ _, red_1_subst _ _⟩, assumption' },
      case r1_app : tec r rc htec hrc
      { rcases htec with _ | _ | _ | _ | @⟨t, tc, e, ec, htc, hec⟩ | _,
        obtain ⟨e', _, _⟩ := ih e size_lt_size_app_lam_e heb hec,
        obtain ⟨r', _, _⟩ := ih r size_lt_size_app_r hrb hrc,
        use (e' ⟦0 ↦ r'⟧), refine ⟨red_1_subst _ _, r1_beta _ _⟩, assumption' } },
    case r1_app : te teb r rb hteb hrb
    { cases hc,
      case r1_beta : t e ec r rc hec hrc
      { rcases hteb with _ | _ | _ | _ | @⟨t, tb, e, eb, htb, heb⟩ | _,
        obtain ⟨e', _, _⟩ := ih e size_lt_size_app_lam_e heb hec,
        obtain ⟨r', _, _⟩ := ih r size_lt_size_app_r hrb hrc,
        use (e' ⟦0 ↦ r'⟧), refine ⟨r1_beta _ _, red_1_subst _ _⟩, assumption' },
      case r1_app : l lc r rc hlc hrc
      { obtain ⟨l', _, _⟩ := ih l size_lt_size_app_l hteb hlc,
        obtain ⟨r', _, _⟩ := ih r size_lt_size_app_r hrb hrc,
        use (app l' r'), refine ⟨r1_app _ _, r1_app _ _⟩, assumption' } } },
  case lam : l r
  { rcases hb with _ | _ | _ | _ | @⟨l, lb, r, rb, hlb, hrb⟩ | _,
    rcases hc with _ | _ | _ | _ | @⟨l, lc, r, rc, hlc, hrc⟩ | _,
    obtain ⟨l', _, _⟩ := ih l size_lt_size_lam_l hlb hlc,
    obtain ⟨r', _, _⟩ := ih r size_lt_size_lam_r hrb hrc,
    use (lam l' r'), refine ⟨r1_lam _ _, r1_lam _ _⟩, assumption' },
  case pi : l r
  { rcases hb with _ | _ | _ | _ | _ | @⟨l, lb, r, rb, hlb, hrb⟩,
    rcases hc with _ | _ | _ | _ | _ | @⟨l, lc, r, rc, hlc, hrc⟩,
    obtain ⟨l', _, _⟩ := ih l size_lt_size_pi_l hlb hlc,
    obtain ⟨r', _, _⟩ := ih r size_lt_size_pi_r hrb hrc,
    use (pi l' r'), refine ⟨r1_pi _ _, r1_pi _ _⟩, assumption' } }

/-- Transitive closure of one-step reduction. -/
inductive red_n : nat → expr → expr → Prop
| rn_refl {e}          :                                 red_n 0 e e
| rn_step {n e₁ e₂ e₃} : red_n n e₁ e₂ → (red_1 e₂ e₃) → red_n (nat.succ n) e₁ e₃
open red_n

local notation e ` ~>⟦` n `⟧ ` e' := red_n n e e'

lemma red_n_refl {e} : e ~>⟦0⟧ e :=
  rn_refl

lemma red_n_trans {n m e₁ e₂ e₃} (h₁ : e₁ ~>⟦n⟧ e₂) (h₂ : e₂ ~>⟦m⟧ e₃) : (e₁ ~>⟦n + m⟧ e₃) := by
{ induction m with m ih generalizing e₃,
  { cases h₂, exact h₁ },
  { rcases h₂ with _ | ⟨h₂₁, h₂₂⟩, exact rn_step (ih h₂₁) h₂₂ } }

/-- Shifting respects n-step reduction. -/
lemma red_n_shift_ind {n e e'} (h : e ~>⟦n⟧ e') (s k) : e ⟦k ↟ s⟧ ~>⟦n⟧ e' ⟦k ↟ s⟧ := by
{ induction n with n ih generalizing e',
  { cases h, exact rn_refl },
  { rcases h with _ | ⟨h₁, h₂⟩, exact rn_step (ih h₁) (red_1_shift_ind _ _ _ _ h₂), } }

lemma red_n_shift {n e e'} (h : e ~>⟦n⟧ e') (s): e ⟦0 ↟ s⟧ ~>⟦n⟧ e' ⟦0 ↟ s⟧ :=
  red_n_shift_ind h s 0

/-- Substitution respects n-step reduction. -/
lemma red_n_subst_ind {n m l l'} (hl : l ~>⟦n⟧ l') {r r'} (hr : r ~>⟦m⟧ r') (k) : l ⟦k ↦ r⟧ ~>⟦n + m⟧ l' ⟦k ↦ r'⟧ := by
{ induction n with n ih generalizing l',
  { cases hl,
    rw nat.zero_add,
    induction m with m ih generalizing r',
    { cases hr, exact rn_refl },
    { rcases hr with _ | ⟨hr₁, hr₂⟩,
      exact rn_step (ih hr₁) (red_1_subst_ind red_1_refl hr₂ _) } },
  { rcases hl with _ | ⟨hl₁, hl₂⟩,
    rw nat.succ_add,
    exact rn_step (ih hl₁) (red_1_subst_ind hl₂ red_1_refl _) } }

lemma red_n_subst {n m l l'} (hl : l ~>⟦n⟧ l') {r r'} (hr : r ~>⟦m⟧ r') : l ⟦0 ↦ r⟧ ~>⟦n + m⟧ l' ⟦0 ↦ r'⟧ :=
  red_n_subst_ind hl hr 0

/- Main part. -/
namespace red_n_confluent
section

-- instance : linear_order (nat ×ₗ nat) := infer_instance

-- #check to_lex
-- #check of_lex
-- #check prod.lex_wf nat.lt_wf nat.lt_wf
-- #check prod.lex.lt_iff
-- #check prod.lex.le_iff
-- #check prod.lex.left
-- #check prod.lex.right

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
    obtain ⟨g, ha, hb, hc, go_down, go_right⟩ := ihm hc₁,
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
    obtain ⟨g, ha, hb, hc, go_down, go_right⟩ := ihn hb₁ hc,
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
    obtain ⟨ha, hb, hc, go_down, go_right⟩ := h, refine ⟨g, ha, hb, hc, _, _⟩,
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
    obtain ⟨g, ha, hb, hc, go_down, go_right⟩ := ih, refine ⟨g, ha, hb, hc, _, _⟩,
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
  obtain ⟨g, ha, hb, hc, go_down, go_right⟩ := ih,

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
  obtain ⟨d', hbd', hcd'⟩ := red_1_confluent hab' hac',

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
{ obtain ⟨ha, hb, hc, go_down, go_right⟩ := h,
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

/-- Confluence of n-step reduction. -/
lemma red_n_confluent {n m a b c} (hb : a ~>⟦n⟧ b) (hc : a ~>⟦m⟧ c) : ∃ d, (b ~>⟦m⟧ d) ∧ (c ~>⟦n⟧ d) :=
  let ⟨_, aux₁⟩ := red_n_confluent.init hb hc,
      ⟨_, aux₂⟩ := red_n_confluent.traverse aux₁ (n, m) in
    red_n_confluent.final aux₂

open small
open small_star
open small_eq

local notation e ` ~> ` e'  := small e e'
local notation e ` ~>* ` e' := small_star e e'
local notation e ` ~~ ` e'  := small_eq e e'

/- Reduction lemmas. -/

instance coe_small_star_of_small {e₁ e₂} : has_coe (small e₁ e₂) (small_star e₁ e₂) := ⟨ss_step ss_refl⟩
instance coe_small_eq_of_small {e₁ e₂} : has_coe (small e₁ e₂) (small_eq e₁ e₂) := ⟨se_step⟩

lemma small_star_refl (e) : e ~>* e :=
  ss_refl

lemma small_star_trans {e₁ e₂ e₃} (h₁ : e₁ ~>* e₂) (h₂ : e₂ ~>* e₃) : (e₁ ~>* e₃) := by
{ induction h₂,
  case ss_refl : _ { exact h₁ },
  case ss_step : _ _ _ _ h₂ ih { exact ss_step (ih h₁) h₂ } }

lemma small_star_app {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : app l r ~>* app l' r' :=
  @small_star_trans (app l r) (app l' r) (app l' r')
    (small_star.rec_on hl (λ _, ss_refl) (λ _ _ _ _ h₂ ih, ss_step ih (s_app_left h₂)))
    (small_star.rec_on hr (λ _, ss_refl) (λ _ _ _ _ h₂ ih, ss_step ih (s_app_right h₂)))

lemma small_star_lam {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : lam l r ~>* lam l' r' :=
  @small_star_trans (lam l r) (lam l' r) (lam l' r')
    (small_star.rec_on hl (λ _, ss_refl) (λ _ _ _ _ h₂ ih, ss_step ih (s_lam_left h₂)))
    (small_star.rec_on hr (λ _, ss_refl) (λ _ _ _ _ h₂ ih, ss_step ih (s_lam_right h₂)))

lemma small_star_pi {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : pi l r ~>* pi l' r' :=
  @small_star_trans (pi l r) (pi l' r) (pi l' r')
    (small_star.rec_on hl (λ _, ss_refl) (λ _ _ _ _ h₂ ih, ss_step ih (s_pi_left h₂)))
    (small_star.rec_on hr (λ _, ss_refl) (λ _ _ _ _ h₂ ih, ss_step ih (s_pi_right h₂)))

/- Equivalence of formulations. -/

lemma red_1_of_small {e₁ e₂} (h : e₁ ~> e₂) : (e₁ ~>₁ e₂) :=
  h.rec_on
    (λ _ _ _, r1_beta red_1_refl red_1_refl)
    (λ _ _ _ _ ihl, r1_app ihl red_1_refl)
    (λ _ _ _ _ ihr, r1_app red_1_refl ihr)
    (λ _ _ _ _ ihl, r1_lam ihl red_1_refl)
    (λ _ _ _ _ ihr, r1_lam red_1_refl ihr)
    (λ _ _ _ _ ihl, r1_pi ihl red_1_refl)
    (λ _ _ _ _ ihr, r1_pi red_1_refl ihr)

lemma red_n_of_small_star {e₁ e₂} (h : e₁ ~>* e₂) : ∃ n, (e₁ ~>⟦n⟧ e₂) := by
{ induction h,
  case ss_refl : e { exact ⟨_, rn_refl⟩ },
  case ss_step : e₁ e₂ e₃ h₁ h₂ ih
  { cases ih with n ih, exact ⟨_, rn_step ih (red_1_of_small h₂)⟩ } }

lemma small_star_of_red_1 {e₁ e₂} (h : e₁ ~>₁ e₂) : e₁ ~>* e₂ := by
{ induction h,
  case r1_beta : t _ _ _ _ _ _ ihe ihr
  { exact ss_step (small_star_app (small_star_lam (small_star_refl _) ihe) ihr) s_beta, },
  case r1_sort : _ { exact small_star_refl _ },
  case r1_var : _ { exact small_star_refl _ },
  case r1_app : _ _ _ _ _ _ ihl ihr { exact small_star_app ihl ihr },
  case r1_lam : _ _ _ _ _ _ ihl ihr { exact small_star_lam ihl ihr },
  case r1_pi : _ _ _ _ _ _ ihl ihr { exact small_star_pi ihl ihr } }

lemma small_star_of_red_n {e₁ e₂ n} (h : e₁ ~>⟦n⟧ e₂) : e₁ ~>* e₂ := by
{ induction h,
  case rn_refl : e { exact small_star_refl _ },
  case rn_step : n e₁ e₂ e₃ h₁ h₂ ih { exact small_star_trans ih (small_star_of_red_1 h₂), } }

/-- Shifting respects small-step reduction. -/
lemma small_star_shift_ind {e e'} (h : e ~>* e') (s k) : e ⟦k ↟ s⟧ ~>* e' ⟦k ↟ s⟧ :=
  let ⟨n, hn⟩ := red_n_of_small_star h in small_star_of_red_n (red_n_shift_ind hn s k)

lemma small_star_shift {e e'} (h : e ~>* e') (s): e ⟦0 ↟ s⟧ ~>* e' ⟦0 ↟ s⟧ :=
  small_star_shift_ind h s 0

/-- Substitution respects small-step reduction. -/
lemma small_star_subst_ind {l l'} (hl : l ~>* l') {r r'} (hr : r ~>* r') (k) : l ⟦k ↦ r⟧ ~>* l' ⟦k ↦ r'⟧ :=
  let ⟨nl, hnl⟩ := red_n_of_small_star hl,
      ⟨nr, hnr⟩ := red_n_of_small_star hr in
    small_star_of_red_n (red_n_subst_ind hnl hnr k)

lemma small_star_subst {l l'} (hl : l ~>* l') {r r'} (hr : r ~>* r') : l ⟦0 ↦ r⟧ ~>* l' ⟦0 ↦ r'⟧ :=
  small_star_subst_ind hl hr 0

/-- Confluence of small-step reduction. -/
lemma small_star_confluent {a b c} (hb : a ~>* b) (hc : a ~>* c) : ∃ d, (b ~>* d) ∧ (c ~>* d) :=
  let ⟨n, hb'⟩ := red_n_of_small_star hb,
      ⟨m, hc'⟩ := red_n_of_small_star hc in
    let ⟨d, hbd', hcd'⟩ := red_n_confluent hb' hc' in
      ⟨d, small_star_of_red_n hbd', small_star_of_red_n hcd'⟩

/-- A term is in "normal form" iff there is no other term it reduces to. -/
def is_normal (e : expr) : Prop := ∀ e', ¬ (e ~> e')

lemma small_star_self_of_is_normal {e e'} (hn : is_normal e) (h: e ~>* e') : e = e' := by
{ induction h,
  case ss_refl : e { refl },
  case ss_step : e₁ e₂ e₃ h₁ h₂ ih
  { replace ih := ih hn, replace hn := hn e₃,
    rw ih at hn, exfalso, exact hn h₂ } }

/-- If a term has a normal form, it must be unique. -/
lemma small_star_normal_unique {e e₁ e₂} (h₁ : e ~>* e₁) (hn₁ : is_normal e₁) (h₂ : e ~>* e₂) (hn₂ : is_normal e₂) :
  e₁ = e₂ := by
{ obtain ⟨e', h₁', h₂'⟩ := small_star_confluent h₁ h₂,
  cases h₁',
  case ss_refl : _
  { rw (small_star_self_of_is_normal hn₂ h₂') },
  case ss_step : _ _ _ h' h''
  { rw ← (small_star_self_of_is_normal hn₁ h') at h'',
    exfalso, exact hn₁ _ h'' } }

/- Definitional equality lemmas. -/

lemma small_eq_refl (e) : e ~~ e := se_refl
lemma small_eq_symm {e₁ e₂} (h : e₁ ~~ e₂) : e₂ ~~ e₁ := se_symm h
lemma small_eq_trans {e₁ e₂ e₃} (h₁ : e₁ ~~ e₂) (h₂ : e₂ ~~ e₃) : (e₁ ~~ e₃) := se_trans h₁ h₂

lemma small_eq_app {l l' r r'} (hl : l ~~ l') (hr : r ~~ r') : app l r ~~ app l' r' :=
  @se_trans (app l r) (app l' r) (app l' r')
    (small_eq.rec_on hl (λ _, se_refl) (λ _ _, se_step ∘ s_app_left) (λ _ _ _, se_symm) (λ _ _ _ _ _, se_trans))
    (small_eq.rec_on hr (λ _, se_refl) (λ _ _, se_step ∘ s_app_right) (λ _ _ _, se_symm) (λ _ _ _ _ _, se_trans))

lemma small_eq_lam {l l' r r'} (hl : l ~~ l') (hr : r ~~ r') : lam l r ~~ lam l' r' :=
  @se_trans (lam l r) (lam l' r) (lam l' r')
    (small_eq.rec_on hl (λ _, se_refl) (λ _ _, se_step ∘ s_lam_left) (λ _ _ _, se_symm) (λ _ _ _ _ _, se_trans))
    (small_eq.rec_on hr (λ _, se_refl) (λ _ _, se_step ∘ s_lam_right) (λ _ _ _, se_symm) (λ _ _ _ _ _, se_trans))

lemma small_eq_pi {l l' r r'} (hl : l ~~ l') (hr : r ~~ r') : pi l r ~~ pi l' r' :=
  @se_trans (pi l r) (pi l' r) (pi l' r')
    (small_eq.rec_on hl (λ _, se_refl) (λ _ _, se_step ∘ s_pi_left) (λ _ _ _, se_symm) (λ _ _ _ _ _, se_trans))
    (small_eq.rec_on hr (λ _, se_refl) (λ _ _, se_step ∘ s_pi_right) (λ _ _ _, se_symm) (λ _ _ _ _ _, se_trans))

/-- Reduction respects definitional equality. -/
lemma small_eq_of_small_star {e₁ e₂} (h : e₁ ~>* e₂) : e₁ ~~ e₂ :=
  small_star.rec_on h
    (λ _, se_refl)
    (λ _ _ _ _ h₂ ih, se_trans ih (se_step h₂))

instance coe_small_eq_of_small_star {e₁ e₂} : has_coe (small_star e₁ e₂) (small_eq e₁ e₂) :=
  ⟨small_eq_of_small_star⟩

lemma small_eq_of_small_stars {e₁ e₂ e} (h₁ : e₁ ~>* e) (h₂ : e₂ ~>* e) : e₁ ~~ e₂ :=
  se_trans (h₁ : e₁ ~~ e) (se_symm (h₂ : e₂ ~~ e))

lemma small_stars_of_small_eq {e₁ e₂} (h : e₁ ~~ e₂) : ∃ e, (e₁ ~>* e) ∧ (e₂ ~>* e) := by
{ induction h,
  case se_refl : e { exact ⟨e, ss_refl, ss_refl⟩ },
  case se_step : e₁ e₂ h { exact ⟨e₂, ss_step ss_refl h, ss_refl⟩, },
  case se_symm : e₁ e₂ h ih { obtain ⟨e, ih₁, ih₂⟩ := ih, exact ⟨e, ih₂, ih₁⟩ },
  case se_trans : e₁ e₂ e₃ hb hc ihb ihc
  { obtain ⟨b, ihb₁, ihb₂⟩ := ihb,
    obtain ⟨c, ihc₁, ihc₂⟩ := ihc,
    obtain ⟨d, hd₁, hd₂⟩ := small_star_confluent ihb₂ ihc₁,
    exact ⟨d, small_star_trans ihb₁ hd₁, small_star_trans ihc₂ hd₂⟩ } }

/-- Two terms are definitionally equal iff they reduce to some same term. -/
lemma small_eq_iff_small_stars {e₁ e₂} : (e₁ ~~ e₂) ↔ ∃ e, (e₁ ~>* e) ∧ (e₂ ~>* e) :=
  ⟨small_stars_of_small_eq, (λ ⟨e, he₁, he₂⟩, small_eq_of_small_stars he₁ he₂)⟩

/-- Shifting respects definitional equality. -/
lemma small_eq_shift_ind {e e'} (h : e ~~ e') (s k) : e ⟦k ↟ s⟧ ~~ e' ⟦k ↟ s⟧ :=
  let ⟨e', h'₁, h'₂⟩ := small_stars_of_small_eq h in
    small_eq_of_small_stars (small_star_shift_ind h'₁ _ _) (small_star_shift_ind h'₂ _ _)

lemma small_eq_shift {e e'} (h : e ~~ e') (s): e ⟦0 ↟ s⟧ ~~ e' ⟦0 ↟ s⟧ :=
  small_eq_shift_ind h s 0

/-- Substitution respects definitional equality. -/
lemma small_eq_subst_ind {l l'} (hl : l ~~ l') {r r'} (hr : r ~~ r') (k) : l ⟦k ↦ r⟧ ~~ l' ⟦k ↦ r'⟧ :=
  let ⟨el', hl'₁, hl'₂⟩ := small_stars_of_small_eq hl,
      ⟨er', hr'₁, hr'₂⟩ := small_stars_of_small_eq hr in
    small_eq_of_small_stars (small_star_subst_ind hl'₁ hr'₁ _) (small_star_subst_ind hl'₂ hr'₂ _)

lemma small_eq_subst {l l'} (hl : l ~~ l') {r r'} (hr : r ~~ r') : l ⟦0 ↦ r⟧ ~~ l' ⟦0 ↦ r'⟧ :=
  small_eq_subst_ind hl hr 0

/- Universe lemmas (used in the unique typing theorem). -/

lemma small_star_sort_normal {s e} (h : sort s ~>* e) : e = sort s := by
{ induction' h, { refl }, { obtain ⟨s', ih⟩ := ih, rw ih at h, cases h } }

lemma small_eq_sort_inv {s s'} (h : sort s ~~ sort s') : s = s' := by
{ obtain ⟨e', h₁, h₂⟩ := small_stars_of_small_eq h,
  have hi := small_star_sort_normal h₁,
  have hi' := small_star_sort_normal h₂,
  injection (eq.trans hi.symm hi') }

/- Pi lemmas (used in the unique typing theorem). -/

lemma small_pi_normal {l r e} (h : pi l r ~> e) : ∃ l' r', e = pi l' r' := by
{ cases' h, exacts [⟨e, t₂, rfl⟩, ⟨t₁, e, rfl⟩] }

lemma small_star_pi_normal {l r e} (h : pi l r ~>* e) : ∃ l' r', e = pi l' r' := by
{ induction' h,
  { exact ⟨l, r, rfl⟩ },
  { obtain ⟨l', r', ih⟩ := ih, rw ih at h,
    exact small_pi_normal h } }

lemma small_star_pi_inv {l l' r r'} (h : pi l r ~>* pi l' r') : (l ~>* l') ∧ (r ~>* r') := by
{ induction' h,
  case ss_refl { exact ⟨ss_refl, ss_refl⟩ },
  case ss_step : e₂ h₁ h₂ ih
  { obtain ⟨l'', r'', h''⟩ := small_star_pi_normal h₁,
    rw h'' at h₂, cases' h₂,
    { obtain ⟨hl, hr⟩ := ih h'', exact ⟨ss_step hl h₂, hr⟩ },
    { obtain ⟨hl, hr⟩ := ih h'', exact ⟨hl, ss_step hr h₂⟩ } } }

lemma small_eq_pi_inv {l l' r r'} (h : pi l r ~~ pi l' r') : (l ~~ l') ∧ (r ~~ r') := by
{ obtain ⟨e, h₁, h₂⟩ := small_stars_of_small_eq h,
  obtain ⟨l'', r'', he⟩ := small_star_pi_normal h₁,
  rw he at h₁ h₂,
  have hi := small_star_pi_inv h₁,
  have hi' := small_star_pi_inv h₂,
  exact ⟨small_eq_of_small_stars hi.1 hi'.1, small_eq_of_small_stars hi.2 hi'.2⟩ }

open has_type
open lawful_ctx

local notation Γ ` ▷ ` e ` : ` t := has_type Γ e t
local notation `▷ ` Γ            := lawful_ctx Γ

/-- Every well-formed (typeable) term has a unique type, up to definitional equality. -/
lemma has_type_unique {Γ e t t'} (h : Γ ▷ e : t) (h' : Γ ▷ e : t') : t ~~ t' := by
{ revert_all, intros Γ₀ e₀ t₀ t₀' h₀ h₀',
  induction h₀ generalizing t₀',
  case t_conv : Γ e t t' hc ht ih { exact se_trans (se_symm hc) (ih h₀') },
  case t_sort : Γ n
  { induction' h₀',
    case t_conv : _ _ _ hc' _ ih' { exact se_trans ih' hc' },
    case t_sort : _ _ { exact se_refl } },
  case t_var : Γ n t ht
  { induction' h₀',
    case t_conv : _ _ _ h' _ ih' { exact se_trans (ih' ht) h' },
    case t_var : _ _ _ h' { injection eq.trans ht.symm h' with ht, rw ht, exact se_refl } },
  case t_app : Γ l r t₁ t₂ hl hr ihl ihr
  { induction' h₀',
    case t_conv : _ _ _ h' _ ih' { exact se_trans (ih' hl hr (λ _, ihl) (λ _, ihr)) h' },
    case t_app : _ _ _ _ _ h' _ _ _ { exact small_eq_subst (small_eq_pi_inv (ihl h')).2 se_refl } },
  case t_lam : Γ t₁ t₂ s e hs he iht ihe
  { induction' h₀',
    case t_conv : _ _ _ h' _ ih' { exact se_trans (ih' hs he (λ _, iht) (λ _, ihe)) h' },
    case t_lam : _ _ _ _ _ _ he' _ _ { exact small_eq_pi se_refl (ihe he') } },
  case t_pi : Γ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
  { induction' h₀',
    case t_conv : _ _ _ h' _ ih' { exact se_trans (ih' ht₁ ht₂ (λ _, iht₁) (λ _, iht₂)) h' },
    case t_pi : _ _ _ _ _ ht₁' ht₂' _ _
    { rw [small_eq_sort_inv (iht₁ ht₁'), small_eq_sort_inv (iht₂ ht₂')], exact se_refl } } }

/-- Typing judgment lemmas. -/

lemma has_type_conv {Γ e t'} (t) (h : t ~~ t') (h' : Γ ▷ e : t) :
  Γ ▷ e : t' := t_conv h h'

lemma has_type_sort {Γ n t} (h : Γ ▷ sort n : t) :
  t ~~ sort n.succ := has_type_unique h t_sort

lemma has_type_var {Γ n t} (h : Γ ▷ var n : t) :
  ∃ t', (list.nth Γ n = option.some t') ∧ (t ~~ t'⟦0 ↟ n.succ⟧) := by
{ induction' h,
  case t_conv : Γ t t' ht h ih
  { obtain ⟨t'', ih₁, ih₂⟩ := ih,
    exact ⟨t'', ih₁, se_trans (se_symm ht) ih₂⟩ },
  case t_var : Γ n t ht
  { exact ⟨t, ht, se_refl⟩ } }

lemma has_type_app {Γ l r t} (h : Γ ▷ app l r : t) :
  ∃ t₁ t₂, (Γ ▷ l : pi t₁ t₂) ∧ (Γ ▷ r : t₁) ∧ (t ~~ t₂ ⟦0 ↦ r⟧) := by
{ induction' h,
  case t_conv : Γ t t' ht h ih
  { obtain ⟨t₁, t₂, ih₁, ih₂, ih₃⟩ := ih,
    exact ⟨t₁, t₂, ih₁, ih₂, se_trans (se_symm ht) ih₃⟩, },
  case t_app : Γ l r t₁ t₂ hl hr _ _
  { exact ⟨t₁, t₂, hl, hr, se_refl⟩ } }

lemma has_type_lam {Γ t₁ e t} (h : Γ ▷ lam t₁ e : t) :
  ∃ t₂ s, (Γ ▷ pi t₁ t₂ : sort s) ∧ (t₁ :: Γ ▷ e : t₂) ∧ (t ~~ pi t₁ t₂) := by
{ induction' h,
  case t_conv : Γ t t' ht h ih
  { obtain ⟨t₂, s, ih₁, ih₂, ih₃⟩ := ih,
    exact ⟨t₂, s, ih₁, ih₂, se_trans (se_symm ht) ih₃⟩ },
  case t_lam : Γ t₁ t₂ s e ht₁ ht₂ _ _
  { exact ⟨t₂, s, ht₁, ht₂, se_refl⟩ } }

lemma has_type_pi {Γ t₁ t₂ t} (h : Γ ▷ pi t₁ t₂ : t) :
  ∃ s₁ s₂, (Γ ▷ t₁ : sort s₁) ∧ (t₁ :: Γ ▷ t₂ : sort s₂) ∧ (t ~~ sort (max s₁ s₂)) := by
{ induction' h,
  case t_conv : Γ t t' ht h ih
  { obtain ⟨s₁, s₂, ih₁, ih₂, ih₃⟩ := ih,
    exact ⟨s₁, s₂, ih₁, ih₂, se_trans (se_symm ht) ih₃⟩ },
  case t_pi : Γ t₁ s₁ t₂ s₂ ht₁ ht₂ _ _
  { exact ⟨s₁, s₂, ht₁, ht₂, se_refl⟩ } }

/-- Definitional equality for contexts. -/
inductive small_eq_ctx : ctx → ctx → Prop
| sec_nil              :                                     small_eq_ctx [] []
| sec_cons {t t' Γ Γ'} : small_eq t t' → small_eq_ctx Γ Γ' → small_eq_ctx (t :: Γ) (t' :: Γ')
open small_eq_ctx

local notation Γ ` ~~c ` Γ' := small_eq_ctx Γ Γ'

lemma small_eq_ctx_refl (Γ) : Γ ~~c Γ := by
{ induction Γ with t Γ ih, exacts [sec_nil, sec_cons se_refl ih] }

lemma small_eq_ctx_symm {Γ₁ Γ₂} (h : Γ₁ ~~c Γ₂) : Γ₂ ~~c Γ₁ := by
{ induction Γ₁ with t₁ Γ₁ ih generalizing Γ₂,
  { cases h, exact sec_nil },
  { rcases h with _ | ⟨ht, hΓ⟩, exact sec_cons (se_symm ht) (ih hΓ) } }

lemma small_eq_ctx_trans {Γ₁ Γ₂ Γ₃} (h₁ : Γ₁ ~~c Γ₂) (h₂ : Γ₂ ~~c Γ₃) : Γ₁ ~~c Γ₃ := by
{ induction Γ₂ with t₂ Γ₂ ih generalizing Γ₁ Γ₃,
  { cases h₁, cases h₂, exact sec_nil },
  { rcases h₁ with _ | ⟨ht₁, hΓ₁⟩,
    rcases h₂ with _ | ⟨ht₂, hΓ₂⟩,
    exact sec_cons (se_trans ht₁ ht₂) (ih hΓ₁ hΓ₂) } }

lemma small_eq_ctx_elem {Γ Γ' n t} (he : Γ ~~c Γ') (h : Γ.nth n = option.some t) :
  ∃ t', (Γ'.nth n = option.some t') ∧ (t ~~ t') := by
{ induction he generalizing n,
  case sec_nil { cases h },
  case sec_cons : t₁ t₁' Γ₁ Γ₁' h₁ h₁' ih
  { cases n with n,
    { unfold list.nth at h ⊢,
      injection h with h, rw h at h₁,
      exact ⟨t₁', rfl, h₁⟩ },
    { unfold list.nth at h ⊢,
      exact ih h } } }

/-- A term has equal types under equal contexts. -/
lemma has_type_small_eq_ctx {Γ Γ' e t} (he : Γ ~~c Γ') (h : Γ ▷ e : t) : Γ' ▷ e : t := by
{ revert_all, intros Γ₀ Γ₀' e₀ t₀ he₀ h₀,
  induction h₀ generalizing Γ₀',
  case t_conv : Γ e t t' hc h ih { exact t_conv hc (ih he₀) },
  case t_sort : Γ n { exact t_sort },
  case t_var : Γ n t h
  { obtain ⟨t', h₁, h₂⟩ := small_eq_ctx_elem he₀ h,
    exact t_conv (small_eq_shift (se_symm h₂) n.succ) (t_var h₁) },
  case t_app : Γ l r t₁ t₂ hl hr ihl ihr { exact t_app (ihl he₀) (ihr he₀) },
  case t_lam : Γ t₁ t₂ s e hs he iht ihe { exact t_lam (iht he₀) (ihe (sec_cons se_refl he₀)) },
  case t_pi : Γ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂ { exact t_pi (iht₁ he₀) (iht₂ (sec_cons se_refl he₀)) } }

/- Main part. (Ugly!) -/

/- Auxiliary functions and related lemmas. -/

def ctxshift : ctx → nat → ctx
| []       _ := []
| (t :: Γ) n := (t ⟦Γ.length ↟ n⟧) :: ctxshift Γ n

lemma ctxshift_length {Γ e} : (ctxshift Γ e).length = Γ.length := by
{ induction Γ with t Γ ih,
  { unfold ctxshift },
  { unfold ctxshift list.length at *, rw ih } }

lemma ctxshift_nth {Γ : ctx} {n m : nat} {e k} (h : Γ.nth n = option.some e) (h' : n.succ + m = Γ.length) :
  (ctxshift Γ k).nth n = option.some (e ⟦m ↟ k⟧) := by
{ induction' Γ with t Γ ih,
  { unfold list.nth at h, injection h },
  { unfold ctxshift at *,
    cases n with n,
    { unfold list.nth list.length at *, injection h with h,
      rw [nat.one_add, nat.add_one] at h', injection h' with h',
      rw [h, h'] },
    { unfold list.nth list.length at *,
      rw [nat.add_one, nat.succ_add] at h', injection h' with h',
      exact ih h h' } } }

def ctxsubst : ctx → expr → ctx
| []       _ := []
| (t :: Γ) e := (t ⟦Γ.length ↦ e⟧) :: ctxsubst Γ e

lemma ctxsubst_length {Γ e} : (ctxsubst Γ e).length = Γ.length := by
{ induction Γ with t Γ ih,
  { unfold ctxsubst },
  { unfold ctxsubst list.length at *, rw ih } }

lemma ctxsubst_nth {Γ : ctx} {n m : nat} {e e'} (h : Γ.nth n = option.some e) (h' : n.succ + m = Γ.length) :
  (ctxsubst Γ e').nth n = option.some (e ⟦m ↦ e'⟧) := by
{ induction' Γ with t Γ ih,
  { unfold list.nth at h, injection h },
  { unfold ctxsubst at *,
    cases n with n,
    { unfold list.nth list.length at *, injection h with h,
      rw [nat.one_add, nat.add_one] at h', injection h' with h',
      rw [h, h'] },
    { unfold list.nth list.length at *,
      rw [nat.add_one, nat.succ_add] at h', injection h' with h',
      exact ih h h' } } }

lemma list.nth_aux_1 {α} (a b : list α) (n : nat) (h : n < a.length) :
  list.nth (a ++ b) n = list.nth a n := by
{ exact list.nth_append h }

lemma list.nth_aux_2 {α} (a b : list α) (n : nat) :
  list.nth (a ++ b) (a.length + n) = list.nth b n := by
{ rw [nat.add_comm, list.nth_append_right (nat.le_add_left _ _), nat.add_sub_cancel _ _] }

lemma list.nth_aux_3 {α} (a : list α) (b : α) (c : list α) (n : nat) (h : n < a.length) :
  list.nth (a ++ b :: c) n = list.nth a n := by
{ exact list.nth_append h }

lemma list.nth_aux_4 {α} (a : list α) (b : α) (c : list α) :
  list.nth (a ++ b :: c) a.length = option.some b := by
{ rw [← nat.zero_add a.length, list.nth_append_right (nat.le_add_left _ _), nat.add_sub_cancel _ _], refl }

lemma list.nth_aux_5 {α} (a : list α) (b : α) (c : list α) (n : nat) :
  list.nth (a ++ b :: c) (a.length + n.succ) = list.nth c n := by
{ rw [nat.add_comm, list.nth_append_right (nat.le_add_left _ _), nat.add_sub_cancel _ _], refl }

/-- How typing interacts with shifting. -/
lemma has_type_shift_ind (Δ : ctx) {Γ' Γ e t} (h : Γ' ++ Γ ▷ e : t) :
  ctxshift Γ' Δ.length ++ Δ ++ Γ ▷ e ⟦Γ'.length ↟ Δ.length⟧ : t ⟦Γ'.length ↟ Δ.length⟧ := by
{ induction' h,
  case t_conv : e t t' hc h ih { exact t_conv (small_eq_shift_ind hc _ _) (ih _) },
  case t_sort : n { unfold shift, exact t_sort },
  case t_var : n t h
  { rcases (lt_or_le n Γ'.length) with h₁ | h₁,
    { rw shift_gt h₁,
      obtain ⟨m, hm⟩ := nat.le.dest (nat.succ_le_of_lt h₁),
      have := shift_shift_disjoint t n.succ m Δ.length,
      rw hm at this, rw ← this, clear this,
      refine t_var _,
      have h₂ := h₁, rw ← @ctxshift_length Γ' Δ.length at h₂,
      rw [list.append_assoc, list.nth_aux_1 _ _ _ h₂],
      rw list.nth_aux_1 _ _ _ h₁ at h,
      exact ctxshift_nth h hm },
    { rw shift_le h₁,
      obtain ⟨m, hm⟩ := nat.le.dest h₁,
      have := shift_shift_overlap t Γ'.length m.succ Δ.length,
      rw [nat.add_succ, hm] at this, rw [this, nat.succ_add], clear this,
      refine t_var _,
      rw [← hm, list.nth_aux_2] at h,
      have h₂ := hm, rw ← @ctxshift_length Γ' Δ.length at h₂,
      rw [← h₂, list.append_assoc, nat.add_assoc, list.nth_aux_2, nat.add_comm, list.nth_aux_2],
      exact h } },
  case t_app : l r t₁ t₂ hl hr ihl ihr
  { unfold shift at *,
    have := shift_subst_below_ind t₂ r 0 Γ'.length Δ.length,
    rw nat.add_zero at this, rw ← this,
    exact t_app (ihl _) (ihr _) },
  case t_lam : t₁ t₂ s e hs he iht ihe
  { unfold shift at *,
    refine t_lam (iht _) _,
    have := @ihe Δ (t₁ :: Γ') Γ (list.cons_append _ _ _),
    exact this },
  case t_pi : t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
  { unfold shift at *,
    refine t_pi (iht₁ _) _,
    have := @iht₂ Δ (t₁ :: Γ') Γ (list.cons_append _ _ _),
    exact this } }

lemma has_type_shift (Δ : ctx) {Γ e t} (h : Γ ▷ e : t) :
  Δ ++ Γ ▷ e ⟦0 ↟ Δ.length⟧ : t ⟦0 ↟ Δ.length⟧ := by
{ rw ← list.nil_append Γ at h,
  have := has_type_shift_ind Δ h,
  unfold ctxshift list.length at this,
  rw list.nil_append at this,
  exact this }

/-- How typing interacts with substitution. -/
lemma has_type_subst_ind {Γ Δ l r t₁ t₂} (hl : Γ ++ t₁ :: Δ ▷ l : t₂) (hr : Δ ▷ r : t₁) :
  ctxsubst Γ r ++ Δ ▷ l ⟦Γ.length ↦ r⟧ : t₂ ⟦Γ.length ↦ r⟧ := by
{ revert_all, intros Γ₀ Δ₀ l₀ r₀ t₁₀ t₂₀ hl₀ hr₀,
  induction' hl₀,
  case t_conv : e t t' hc h ih { exact t_conv (small_eq_subst_ind hc se_refl _) (ih hr₀) },
  case t_sort : n { unfold subst, exact t_sort },
  case t_var : n t h
  { rcases (nat.lt_trichotomy Γ₀.length n) with h₁ | h₁ | h₁,
    { cases n with n, { exfalso, exact nat.not_lt_zero _ h₁ },
      rw [subst_lt h₁],
      replace h₁ := nat.le_of_lt_succ h₁,
      obtain ⟨m, hm⟩ := nat.le.dest h₁,
      have := @shift_subst_inside t r₀ Γ₀.length m.succ,
      rw [nat.add_succ, hm] at this,
      rw [this, nat.pred_succ], clear this,
      refine t_var _,
      have hm' := hm, rw [← @ctxsubst_length Γ₀ r₀] at hm',
      rw [← hm', list.nth_aux_2],
      rw [← hm, ← nat.add_succ, list.nth_aux_2] at h,
      exact h },
    { have := @shift_subst_inside t r₀ n 0,
      rw [nat.add_zero] at this,
      rw [h₁, subst_eq, this], clear this,
      rw [← h₁, list.nth_aux_4] at h, injection h with h, rw h at hr₀,
      have := has_type_shift (ctxsubst Γ₀ r₀) hr₀,
      rw [ctxsubst_length, h₁] at this, exact this },
    { rw [subst_gt h₁],
      rw [list.nth_aux_3 _ _ _ _ h₁] at h,
      have h₂ := nat.succ_le_of_lt h₁,
      obtain ⟨m, hm⟩ := nat.le.dest h₂,
      rw [← hm, shift_subst_above],
      refine t_var _,
      rw [← @ctxsubst_length Γ₀ r₀] at h₁,
      rw [list.nth_aux_1 _ _ _ h₁],
      exact ctxsubst_nth h hm } },
  case t_app : l r t₁ t₂ hl hr ihl ihr
  { unfold subst at ihl ⊢, rw ← subst_subst,
    exact t_app (ihl hr₀) (ihr hr₀) },
  case t_lam : t₁ t₂ s e hs he iht ihe
  { unfold subst at iht ⊢,
    refine t_lam (iht hr₀) _,
    replace ihe := ihe hr₀ (list.cons_append _ _ _).symm,
    unfold ctxsubst list.length at ihe,
    rw [nat.add_one, list.cons_append] at ihe,
    exact ihe },
  case t_pi : t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
  { unfold subst at iht₁ ⊢,
    refine t_pi (iht₁ hr₀) _,
    replace iht₂ := iht₂ hr₀ (list.cons_append _ _ _).symm,
    unfold ctxsubst list.length subst at iht₂,
    rw [nat.add_one, list.cons_append] at iht₂,
    exact iht₂ } }

lemma has_type_subst {Γ l r t₁ t₂} (hl : t₁ :: Γ ▷ l : t₂) (hr : Γ ▷ r : t₁) :
  Γ ▷ l ⟦0 ↦ r⟧ : t₂ ⟦0 ↦ r⟧ := by
{ rw ← list.nil_append (t₁ :: Γ) at hl,
  have := has_type_subst_ind hl hr,
  unfold ctxsubst at this,
  rw list.nil_append at this,
  exact this }

/-- Small-step reduction preserves type. -/
lemma has_type_small {Γ e e' t} (h : Γ ▷ e : t) (h' : e ~> e') : (Γ ▷ e' : t) := by
{ revert_all, intros Γ₀ e₀ e' t₀ h h',
  induction h generalizing e',
  case t_conv : Γ e t t' hc h ih { exact t_conv hc (ih h'), },
  case t_sort : Γ n { rw small_star_sort_normal (h' : sort n ~>* e'), exact t_sort },
  case t_var : Γ n t h { cases h' },
  case t_app : Γ l r t₁ t₂ hl hr ihl ihr
  { cases h',
    case s_beta : t' e' r'
    { obtain ⟨tt, s, h₁, h₂, h₃⟩ := has_type_lam hl,
      have := small_eq_pi_inv h₃,
      refine t_conv (small_eq_subst (se_symm this.2) se_refl) _,
      exact has_type_subst h₂ (t_conv this.1 hr) },
    case s_app_left : l l' r hl'
    { exact t_app (ihl hl') hr, },
    case s_app_right : l r r' hr'
    { refine t_conv (small_eq_subst se_refl (se_symm (hr' : r ~~ r'))) _,
      exact (t_app hl (ihr hr')) } },
  case t_lam : Γ t₁ t₂ s e hs he iht ihe
  { cases h',
    case s_lam_left : t t' e ht'
    { refine t_conv (small_eq_pi (se_symm (ht' : t ~~ t')) se_refl) _,
      refine t_lam (iht (s_pi_left ht')) _,
      exact has_type_small_eq_ctx (sec_cons (ht' : t ~~ t') (small_eq_ctx_refl Γ)) he },
    case s_lam_right : t e e' he'
    { exact t_lam hs (ihe he') } },
  case t_pi : Γ t₁ s₁ t₂ s₂ ht₁ ht₂ iht₁ iht₂
  { cases h',
    case s_pi_left : t₁' t₁'' t₂' ht₁'
    { refine t_pi (iht₁ ht₁') _,
      exact has_type_small_eq_ctx (sec_cons (ht₁' : t₁' ~~ t₁'') (small_eq_ctx_refl Γ)) ht₂ },
    case s_pi_right : t₁' t₂' t₂'' ht₂'
    { exact t_pi ht₁ (iht₂ ht₂') } } }

lemma has_type_small_star {Γ e e' t} (h : Γ ▷ e : t) (h' : e ~>* e') : (Γ ▷ e' : t) := by
{ induction h',
  case ss_refl : e { exact h },
  case ss_step : e₁ e₂ e₃ h₁ h₂ ih { exact has_type_small (ih h) h₂ } }

end
end expr

end
end coc
