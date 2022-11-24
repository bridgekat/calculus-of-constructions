import tactic
import expr

namespace coc
section

set_option pp.structure_projections false

local notation e ` ⟦` n ` ↦ ` e' `⟧`  := expr.subs e n e'
local notation e ` ⟦` n ` ↟ ` m `⟧`   := expr.gap e n m
local notation e ` ~> ` e'            := small e e'
local notation e ` ~>* ` e'           := small_star e e'
local notation Γ ` ⊢ ` e `: ` t       := has_type Γ e t
local notation `⊢ ` Γ                 := ctx_wf Γ

/- Auxiliary arithmetic lemmas. -/

lemma nat.order_aux_1 {a b : nat} (h₁ : ¬a < b) (h₂ : ¬a = b) : (b < a) :=
  ne.lt_of_le (ne.symm h₂) (le_of_not_gt h₁)

lemma nat.order_aux_2 {a b c : nat} (h : a + b < c) : b < c :=
  lt_of_le_of_lt (nat.le_add_left b a) h

lemma nat.order_aux_3 {a b c : nat} (h : a + b < c) : a < c :=
  lt_of_le_of_lt (nat.le_add_right a b) h

lemma nat.le_add_left' (a b c : ℕ) (h : a ≤ b) : a ≤ c + b :=
  le_add_left h

lemma nat.le_add_right' (a b c : ℕ) (h : a ≤ b) : a ≤ b + c :=
  le_add_right h

-- #check @nat.le.intro
-- #check @nat.le.dest

namespace expr
section

open idx

/- Uninteresting `gap` lemmas for supporting case analysis. -/

lemma gap_bound (v n m) : var (bound v) ⟦n ↟ m⟧ =
  if n <= v then var (bound (v + m)) else var (bound v) := by unfold gap

lemma gap_bound_n_le_v {v n m} (h : n ≤ v) :
  var (bound v) ⟦n ↟ m⟧ = var (bound (v + m)) := by
  { unfold gap, split_ifs, refl }

lemma gap_bound_v_lt_n {v n m} (h : v < n) :
  var (bound v) ⟦n ↟ m⟧ = var (bound v) := by
  { unfold gap, split_ifs with hif, exfalso, exact not_le_of_lt h hif, refl }

/- Uninteresting `subs` lemmas for supporting case analysis. -/

lemma subs_bound (v n e') : var (bound v) ⟦n ↦ e'⟧ =
  if n < v then var (bound v.pred)
  else if n = v then e'.gap 0 n
  else (var (bound v)) := by unfold subs

lemma subs_bound_n_lt_v {v n e'} (h : n < v) :
  var (bound v) ⟦n ↦ e'⟧ = var (bound v.pred) := by
  { unfold subs, split_ifs, refl }

lemma subs_bound_eq {n e'} :
  var (bound n) ⟦n ↦ e'⟧ = e'.gap 0 n := by
  { unfold subs, split_ifs with hif, { exfalso, exact nat.lt_irrefl _ hif }, refl }

lemma subs_bound_v_lt_n {v n e'} (h : v < n) :
  var (bound v) ⟦n ↦ e'⟧ = var (bound v) := by
  { unfold subs, split_ifs with hif₁ hif₂,
    { exfalso, exact nat.lt_irrefl _ (nat.lt_trans h hif₁) },
    { rw hif₂ at h, exfalso, exact nat.lt_irrefl _ h },
    refl }

/- How `gap` interacts with itself. -/

lemma gap_zero (e n) : e ⟦n ↟ 0⟧ = e := by
{ induction e generalizing n,
  case sort : s { unfold gap },
  case var : v { cases v; unfold gap; split_ifs; simp },
  case app : l r ihl ihr { unfold gap, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold gap, rw [iht, ihe] },
  case pi : t₁ t₂ iht₁ iht₂ { unfold gap, rw [iht₁, iht₂] } }

lemma gap_gap_disjoint_ind (e k a b c) : e ⟦k ↟ a⟧ ⟦(a + b + k) ↟ c⟧ = e ⟦(b + k) ↟ c⟧ ⟦k ↟ a⟧ := by
{ induction e generalizing k,
  case sort : s { unfold gap },
  case var : v
  { cases v, swap, { unfold gap },
    rcases (lt_or_le v k) with h₁ | h₁,
    { rw [gap_bound_v_lt_n h₁,
          gap_bound_v_lt_n (nat.lt_add_left _ _ _ h₁),
          gap_bound_v_lt_n (nat.lt_add_left _ _ _ h₁),
          gap_bound_v_lt_n h₁] },
    rcases (lt_or_le v (b + k)) with h₂ | h₂,
    { rw [gap_bound_n_le_v h₁, nat.add_comm, nat.add_assoc,
          gap_bound_v_lt_n (nat.add_lt_add_left h₂ _),
          gap_bound_v_lt_n h₂,
          gap_bound_n_le_v h₁, nat.add_comm] },
    { rw [gap_bound_n_le_v h₁, nat.add_comm, nat.add_assoc,
          gap_bound_n_le_v (nat.add_le_add_left h₂ _),
          gap_bound_n_le_v h₂,
          gap_bound_n_le_v (nat.le_add_right' _ _ _ h₁), nat.add_assoc, nat.add_comm] } },
  case app : l r ihl ihr { unfold gap, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold gap, rw [iht, ← nat.add_succ, ihe], refl },
  case pi : t₁ t₂ iht₁ iht₂ { unfold gap, rw [iht₁, ← nat.add_succ, iht₂], refl } }

lemma gap_gap_disjoint (e a b c) : e ⟦0 ↟ a⟧ ⟦(a + b) ↟ c⟧ = e ⟦b ↟ c⟧ ⟦0 ↟ a⟧ :=
  gap_gap_disjoint_ind e 0 a b c

lemma gap_gap_overlap_ind (e k a b c) : e ⟦k ↟ (a + b + c)⟧ = e ⟦k ↟ (a + b)⟧ ⟦(k + a) ↟ c⟧ := by
{ induction e generalizing k,
  case sort : s { unfold gap },
  case var : v
  { cases v, swap, { unfold gap },
    rcases (lt_or_le v k) with h | h,
    { rw [gap_bound_v_lt_n h,
          gap_bound_v_lt_n h,
          gap_bound_v_lt_n (nat.lt_add_right _ _ _ h)] },
    { rw [gap_bound_n_le_v h,
          gap_bound_n_le_v h, ← nat.add_assoc v a b,
          gap_bound_n_le_v (nat.le_add_right' _ _ _ (nat.add_le_add_right h _)),
          ← nat.add_assoc, ← nat.add_assoc] } },
  case app : l r ihl ihr { unfold gap, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold gap, rw [iht, ihe, nat.succ_add] },
  case pi : t₁ t₂ iht₁ iht₂ { unfold gap, rw [iht₁, iht₂, nat.succ_add] } }

lemma gap_gap_overlap (e a b c) : e ⟦0 ↟ (a + b + c)⟧ = e ⟦0 ↟ (a + b)⟧ ⟦a ↟ c⟧ :=
  @eq.subst _ (λ x, e ⟦0 ↟ (a + b + c)⟧ = e ⟦0 ↟ (a + b)⟧ ⟦x ↟ c⟧) _ _
    (nat.zero_add a) (gap_gap_overlap_ind e 0 a b c)

/- How `gap` and `subs` interact with each other. -/

lemma gap_subs_above_ind (e e' k n m) : e ⟦k ↟ n⟧ ⟦(n + m + k) ↦ e'⟧ = e ⟦(m + k) ↦ e'⟧ ⟦k ↟ n⟧ := by
{ induction e generalizing k n m,
  case sort : s { unfold gap subs },
  case var : v
  { cases v, swap, { unfold gap subs },
    rcases (lt_or_le v k) with h₁ | h₁,
    { rw [gap_bound_v_lt_n h₁,
          subs_bound_v_lt_n (nat.lt_add_left _ _ _ h₁),
          subs_bound_v_lt_n (nat.lt_add_left _ _ _ h₁),
          gap_bound_v_lt_n h₁] },
    { rw gap_bound_n_le_v h₁,
      rcases (nat.lt_trichotomy v (m + k)) with h₂ | h₂ | h₂,
      { rw [subs_bound_v_lt_n h₂, nat.add_comm, nat.add_assoc,
            subs_bound_v_lt_n (nat.add_lt_add_left h₂ _),
            gap_bound_n_le_v h₁, nat.add_comm] },
      { rw [nat.add_comm, nat.add_assoc, h₂,
            subs_bound_eq,
            subs_bound_eq, nat.add_comm, nat.add_comm m k,
            gap_gap_overlap _ _ _ _] },
      { cases v, { exfalso, exact nat.not_lt_zero _ h₂, },
        rw [nat.add_comm, nat.add_assoc,
            subs_bound_n_lt_v (nat.add_lt_add_left h₂ _),
            subs_bound_n_lt_v h₂, nat.add_succ, nat.pred_succ, nat.pred_succ,
            gap_bound_n_le_v (nat.le_of_lt_succ (nat.order_aux_2 h₂)), nat.add_comm] } } },
  case app : l r hl hr { unfold gap subs, rw [hl, hr] },
  case lam : t e ht he { unfold gap subs, rw [ht, ← nat.add_succ, he], refl },
  case pi : t₁ t₂ ht₁ ht₂ { unfold gap subs, rw [ht₁, ← nat.add_succ, ht₂], refl } }

lemma gap_subs_above (e e' n m) : e ⟦0 ↟ n⟧ ⟦(n + m) ↦ e'⟧ = e ⟦m ↦ e'⟧ ⟦0 ↟ n⟧ := 
  gap_subs_above_ind e e' 0 n m

lemma gap_subs_inside_ind (e e' k n m) : e ⟦k ↟ nat.succ (n + m)⟧ ⟦(n + k) ↦ e'⟧ = e ⟦k ↟ (n + m)⟧ := by
{ induction e generalizing k,
  case sort : s { unfold gap subs },
  case var : v
  { cases v, swap, { unfold gap subs },
    rcases (lt_or_le v k) with h₁ | h₁,
    { rw [gap_bound_v_lt_n h₁,
          gap_bound_v_lt_n h₁,
          subs_bound_v_lt_n (nat.lt_add_left _ _ _ h₁)] },
    { rw [gap_bound_n_le_v h₁,
          gap_bound_n_le_v h₁, nat.add_succ, ← nat.add_assoc, nat.add_comm n k,
          subs_bound_n_lt_v (nat.lt_succ_of_le (nat.le_add_right' _ _ _ (nat.add_le_add_right h₁ _))),
          nat.pred_succ] } },
  case app : l r hl hr { unfold gap subs, rw [hl, hr] },
  case lam : t e ht he { unfold gap subs, rw [ht, ← nat.add_succ n k, he] },
  case pi : t₁ t₂ ht₁ ht₂ { unfold gap subs, rw [ht₁, ← nat.add_succ n k, ht₂] } }

lemma gap_subs_inside (e e') {n m} : e ⟦0 ↟ nat.succ (n + m)⟧ ⟦n ↦ e'⟧ = e ⟦0 ↟ (n + m)⟧ :=
  gap_subs_inside_ind e e' 0 n m

lemma gap_subs_below_ind (e e' k n m) : e ⟦nat.succ (n + k) ↟ m⟧ ⟦k ↦ e' ⟦n ↟ m⟧⟧ = e ⟦k ↦ e'⟧ ⟦(n + k) ↟ m⟧ := by
{ induction e generalizing k,
  case sort : s { unfold gap subs },
  case var : v
  { cases v, swap, { unfold gap subs },
    rcases (nat.lt_trichotomy v k) with h₁ | h₁ | h₁,
    { rw [gap_bound_v_lt_n (nat.lt_succ_of_lt (nat.lt_add_left _ _ _ h₁)),
          subs_bound_v_lt_n h₁,
          subs_bound_v_lt_n h₁,
          gap_bound_v_lt_n (nat.lt_add_left _ _ _ h₁)] },
    { rw [← h₁,
          gap_bound_v_lt_n (nat.lt_succ_of_le (nat.le_add_left' _ _ _ (nat.le_refl v))),
          subs_bound_eq,
          subs_bound_eq, nat.add_comm,
          gap_gap_disjoint] },
    { cases v, { exfalso, exact nat.not_lt_zero _ h₁ },
      rw subs_bound_n_lt_v h₁,
      rcases (lt_or_le v (n + k)) with h₂ | h₂,
      { rw [gap_bound_v_lt_n (nat.succ_lt_succ h₂), nat.pred_succ,
            subs_bound_n_lt_v h₁,
            gap_bound_v_lt_n h₂, nat.pred_succ] },
      { rw [gap_bound_n_le_v (nat.succ_le_succ h₂), nat.pred_succ,
            subs_bound_n_lt_v (nat.lt_add_right _ _ _ h₁), nat.succ_add,
            gap_bound_n_le_v h₂, nat.pred_succ] } } },
  case app : l r ihl ihr { unfold gap subs, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold gap subs, rw [iht, ← nat.add_succ, ihe],  },
  case pi : t₁ t₂ iht₁ iht₂ { unfold gap subs, rw [iht₁, ← nat.add_succ, iht₂] } }

lemma gap_subs_below (e e' n m) : e ⟦nat.succ n ↟ m⟧ ⟦0 ↦ e' ⟦n ↟ m⟧⟧ = e ⟦0 ↦ e'⟧ ⟦n ↟ m⟧ :=
  gap_subs_below_ind e e' 0 n m

/- How `sub` interacts with itself. -/

lemma subs_subs_ind (e e₁ e₂ k n) : e ⟦k ↦ e₁⟧ ⟦(n + k) ↦ e₂⟧ = e ⟦nat.succ (n + k) ↦ e₂⟧ ⟦k ↦ e₁ ⟦n ↦ e₂⟧⟧ := by
{ induction e generalizing e₁ e₂ k n,
  case sort : s { unfold subs },
  case var : v
  { cases v, swap, { unfold subs },
    rcases (nat.lt_trichotomy v k) with h₁ | h₁ | h₁,
    { rw [subs_bound_v_lt_n h₁,
          subs_bound_v_lt_n (nat.lt_add_left _ _ _ h₁),
          subs_bound_v_lt_n (nat.lt_succ_of_lt (nat.lt_add_left _ _ _ h₁)),
          subs_bound_v_lt_n h₁] },
    { rw [← h₁,
          subs_bound_eq,
          subs_bound_v_lt_n (nat.lt_succ_of_le (nat.le_add_left' _ _ _ (nat.le_refl v))),
          subs_bound_eq, nat.add_comm,
          gap_subs_above _ _ _ _] },
    { cases v, { exfalso, exact nat.not_lt_zero _ h₁ },
      rcases (nat.lt_trichotomy v (n + k)) with h₂ | h₂ | h₂,
      { rw [subs_bound_n_lt_v h₁, nat.pred_succ,
            subs_bound_v_lt_n h₂,
            subs_bound_v_lt_n (nat.succ_lt_succ h₂),
            subs_bound_n_lt_v h₁, nat.pred_succ] },
      { rw [← h₂,
            subs_bound_n_lt_v h₁, nat.pred_succ,
            subs_bound_eq,
            subs_bound_eq, h₂, nat.add_comm,
            gap_subs_inside] },
      { rw [subs_bound_n_lt_v h₁, nat.pred_succ,
            subs_bound_n_lt_v h₂,
            subs_bound_n_lt_v (nat.succ_lt_succ h₂), nat.pred_succ,
            subs_bound_n_lt_v (nat.order_aux_2 h₂)] } } },
  case app : l r ihl ihr { unfold subs, rw [ihl, ihr] },
  case lam : t e iht ihe { unfold subs, rw iht, simp, exact ihe _ _ _ _ },
  case pi : t₁ t₂ iht₁ iht₂ { unfold subs, rw iht₁, simp, exact iht₂ _ _ _ _ } }

lemma subs_subs (e e₁ e₂ n) : e ⟦0 ↦ e₁⟧ ⟦n ↦ e₂⟧ = e ⟦(nat.succ n) ↦ e₂⟧ ⟦0 ↦ e₁ ⟦n ↦ e₂⟧⟧ :=
  subs_subs_ind e e₁ e₂ 0 n

/- Uninteresting `size` lemmas to support strong induction on `expr`. -/

lemma size_wf : well_founded (λ e₁ e₂ : expr, size e₁ < size e₂) :=
  measure_wf size

lemma size_lt_size_app_l {l r} : size l < size (app l r) := by
{ unfold size, rw [← nat.add_succ], simp }

lemma size_lt_size_app_r {l r} : size r < size (app l r) := by
{ unfold size, rw [nat.add_comm, ← nat.add_succ], simp }

lemma size_lt_size_lam_l {l r} : size l < size (lam l r) := by
{ unfold size, rw [← nat.add_succ], simp }

lemma size_lt_size_lam_r {l r} : size r < size (lam l r) := by
{ unfold size, rw [nat.add_comm, ← nat.add_succ], simp }

lemma size_lt_size_app_lam_e {t e r} : size e < size (app (lam t e) r) :=
  nat.lt_trans size_lt_size_lam_r size_lt_size_app_l

lemma size_lt_size_pi_l {l r} : size l < size (pi l r) := by
{ unfold size, rw [← nat.add_succ], simp }

lemma size_lt_size_pi_r {l r} : size r < size (pi l r) := by
{ unfold size, rw [nat.add_comm, ← nat.add_succ], simp }

end
end expr
open expr

/- Main part. -/

/-- The "one-step reduction" relation `red1 e₁ e₂`: "`e₁` reduces to `e₂` by contracting zero or more immediate redexes."
    See: https://archive-pml.github.io/martin-lof/pdfs/An-Intuitionistic-Theory-of-Types-1972.pdf -/
inductive red1 : expr → expr → Prop
| r1_beta {t e e' r r'}   : red1 e e' → red1 r r' →     red1 (app (lam t e) r) (e'⟦0 ↦ r'⟧)
| r1_sort {s}             :                             red1 (sort s) (sort s)
| r1_var  {v}             :                             red1 (var v) (var v)
| r1_app  {l l' r r'}     : red1 l l' → red1 r r' →     red1 (app l r) (app l' r')
| r1_lam  {t t' e e'}     : red1 t t' → red1 e e' →     red1 (lam t e) (lam t' e')
| r1_pi   {t₁ t₁' t₂ t₂'} : red1 t₁ t₁' → red1 t₂ t₂' → red1 (pi t₁ t₂) (pi t₁' t₂')
open red1

local notation e ` ~>₁ ` e' := red1 e e'

lemma red1.refl {e : expr} : e ~>₁ e :=
  @expr.rec_on (λ e, e ~>₁ e) e
    (λ _, r1_sort) (λ _, r1_var) (λ _ _, r1_app) (λ _ _, r1_lam) (λ _ _, r1_pi)

lemma red1.red1_gap_ind (n e e' k) (h : e ~>₁ e') : e ⟦k ↟ n⟧ ~>₁ e' ⟦k ↟ n⟧ := by
{ -- Strong induction on `e` generalising `e' k h`.
  revert_after e, apply size_wf.induction e, intros e ih,
  cases e,
  case sort : s { intros, cases h, unfold gap, exact red1.refl },
  case var : v { intros, cases h, cases v; split_ifs <|> skip; exact red1.refl },
  case app : l r
  { intros,
    cases h,
    case r1_beta : t e e' r r' he hr
    { unfold gap, rw ← gap_subs_below,
      refine r1_beta (ih e _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_lam_e, size_lt_size_app_r] },
    case r1_app : l l' r r' hl hr
    { unfold gap, refine r1_app (ih l _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_l, size_lt_size_app_r] } },
  case lam : t e
  { intros, cases h, unfold gap,
    refine r1_lam (ih t _ _ _ _) (ih e _ _ _ _), assumption',
    exacts [size_lt_size_lam_l, size_lt_size_lam_r] },
  case pi : t₁ t₂
  { intros, cases h, unfold gap,
    refine r1_pi (ih t₁ _ _ _ _) (ih t₂ _ _ _ _), assumption',
    exacts [size_lt_size_pi_l, size_lt_size_pi_r] } }

lemma red1.red1_gap (n) {e e'} (h : e ~>₁ e') : e ⟦0 ↟ n⟧ ~>₁ e' ⟦0 ↟ n⟧ :=
  red1.red1_gap_ind n e e' 0 h

lemma red1.red1_subs_ind {l l'} (hl : l ~>₁ l') {r r'} (hr : r ~>₁ r') (k) : l ⟦k ↦ r⟧ ~>₁ l' ⟦k ↦ r'⟧ := by
{ revert_all, intros l₀ l₀' hl₀ r₀ r₀' hr₀ k,
  -- Strong induction on `l₀` generalising `l₀' hl₀ r₀ r₀' hr₀ k`.
  revert_after l₀, apply size_wf.induction l₀, intros l₀ ih,
  cases l₀,
  case sort : s { intros, cases hl₀, unfold subs, exact r1_sort },
  case var : v
  { intros, cases v; cases hl₀; unfold subs, swap, apply r1_var,
    split_ifs; exact red1.refl <|> skip,
    exact red1.red1_gap k hr₀ },
  case app : l r
  { intros,
    cases hl₀,
    case r1_beta : t e e' r r' he hr
    { unfold subs, rw subs_subs,
      refine r1_beta (ih e _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_lam_e, size_lt_size_app_r] },
    case r1_app : l l' r r' hl hr
    { unfold subs,
      refine r1_app (ih l _ _ _ _) (ih r _ _ _ _), assumption',
      exacts [size_lt_size_app_l, size_lt_size_app_r] } },
  case lam : t e
  { intros, cases hl₀, unfold subs,
    refine r1_lam (ih t _ _ _ _) (ih e _ _ _ _), assumption',
    exacts [size_lt_size_lam_l, size_lt_size_lam_r] },
  case pi : t₁ t₂
  { intros, cases hl₀, unfold subs,
    refine r1_pi (ih t₁ _ _ _ _) (ih t₂ _ _ _ _), assumption',
    exacts [size_lt_size_pi_l, size_lt_size_pi_r] } }

lemma red1.confluent {a b c : expr} (hb : a ~>₁ b) (hc : a ~>₁ c) :
  ∃ d, (b ~>₁ d) ∧ (c ~>₁ d) := by
{ -- Strong induction on `a` generalising `b c hb hc`.
  revert_after a, apply size_wf.induction a, intros a ih,
  cases a,
  case sort : s { intros, cases hb, cases hc, use (sort s), exact ⟨r1_sort, r1_sort⟩, },
  case var : v { intros, cases hb, cases hc, use (var v), exact ⟨r1_var, r1_var⟩ },
  case app : l r { sorry },
  case lam : l r { sorry },
  case pi : l r { sorry }
}

end
end coc
