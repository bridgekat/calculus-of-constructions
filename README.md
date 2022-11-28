## Main results

Confluence, unique typing, and type preservation: in [`lemmas.lean`](src/lemmas.lean).

```lean
/-- Confluence of small-step reduction. -/
lemma small_star_confluent {a b c} (hb : a ~>* b) (hc : a ~>* c) : ∃ d, (b ~>* d) ∧ (c ~>* d) := ...

/-- If a term has a normal form, it must be unique. -/
lemma small_star_normal_unique {e e₁ e₂} (h₁ : e ~>* e₁) (hn₁ : is_normal e₁) (h₂ : e ~>* e₂) (hn₂ : is_normal e₂) : e₁ = e₂ := ...

/-- Every well-formed (typeable) term has a unique type, up to definitional equality. -/
lemma has_type_unique {Γ e t t'} (h : Γ ▷ e : t) (h' : Γ ▷ e : t') : t ~~ t' := ...

/-- Small-step reduction preserves type. -/
lemma has_type_small_star {Γ e e' t} (h : Γ ▷ e : t) (h' : e ~>* e') : (Γ ▷ e' : t) := ...
```

## Details

### Terms (preterms)

```lean
inductive expr : Type
| sort : nat →         expr
| var  : nat →         expr
| app  : expr → expr → expr
| lam  : expr → expr → expr
| pi   : expr → expr → expr
open expr
```

`var` are variables represented in standard [de Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index).

When a term is added to a context (which is a list of terms representing types), its overflow variables are considered to refer to the immediate successors in the list, relative to its own position, i.e. free variable with overflow index 0 refers to the next element, 1 refers to the next-next one, etc. Under such convention, prepending to a context does not need to modify any of its existing entries.

### Single-variable substitutions

```lean
/-- Lift variables with level ≥ `n` by `m` levels. -/
def expr.shift : expr → nat → nat → expr
| (sort s)   n m := sort s
| (var v)    n m := if n <= v then var (v + m) else var v
| (app l r)  n m := app (expr.shift l n m) (expr.shift r n m)
| (lam t e)  n m := lam (expr.shift t n m) (expr.shift e (nat.succ n) m)
| (pi t₁ t₂) n m := pi (expr.shift t₁ n m) (expr.shift t₂ (nat.succ n) m)

local notation e ` ⟦` n ` ↦ ` e' `⟧` := expr.subst e n e'

/-- Replace all variables at level = `n` by an expression `e'`
    (when deleting the outermost layer of binder). -/
def expr.subst : expr → nat → expr → expr
| (sort s)   n e' := sort s
| (var v)    n e' := if n < v then var (nat.pred v) else if n = v then expr.shift e' 0 n else var v
| (app l r)  n e' := app (expr.subst l n e') (expr.subst r n e')
| (lam t e)  n e' := lam (expr.subst t n e') (expr.subst e (nat.succ n) e')
| (pi t₁ t₂) n e' := pi (expr.subst t₁ n e') (expr.subst t₂ (nat.succ n) e')

local notation e ` ⟦` n ` ↟ ` m `⟧` := expr.shift e n m
```

This is definitely far from the optimal formalisation (especially in comparison with [Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf)), but it might be closer to real implementations...

<details>
<summary>Useful lemmas</summary>
<br>

```lean
/- How `shift` interacts with itself. -/
lemma shift_zero (e n) : e ⟦n ↟ 0⟧ = e := ...
lemma shift_shift_disjoint_ind (e k a b c) : e ⟦(b + k) ↟ c⟧ ⟦k ↟ a⟧ = e ⟦k ↟ a⟧ ⟦(a + b + k) ↟ c⟧ := ...
lemma shift_shift_disjoint (e a b c) : e ⟦b ↟ c⟧ ⟦0 ↟ a⟧ = e ⟦0 ↟ a⟧ ⟦(a + b) ↟ c⟧ := ...

/- How `shift` and `subst` interact with each other. -/
lemma shift_subst_above_ind (e e' k n m) : e ⟦k ↟ n⟧ ⟦(n + m + k) ↦ e'⟧ = e ⟦(m + k) ↦ e'⟧ ⟦k ↟ n⟧ := ...
lemma shift_subst_above (e e' n m) : e ⟦0 ↟ n⟧ ⟦(n + m) ↦ e'⟧ = e ⟦m ↦ e'⟧ ⟦0 ↟ n⟧ := ...
lemma shift_subst_inside_ind (e e' k n m) : e ⟦k ↟ nat.succ (n + m)⟧ ⟦(n + k) ↦ e'⟧ = e ⟦k ↟ (n + m)⟧ := ...
lemma shift_subst_inside (e e' n m) : e ⟦0 ↟ nat.succ (n + m)⟧ ⟦n ↦ e'⟧ = e ⟦0 ↟ (n + m)⟧ := ...
lemma shift_subst_below_ind (e e' k n m) : e ⟦nat.succ (n + k) ↟ m⟧ ⟦k ↦ e' ⟦n ↟ m⟧⟧ = e ⟦k ↦ e'⟧ ⟦(n + k) ↟ m⟧ := ...
lemma shift_subst_below (e e' n m) : e ⟦nat.succ n ↟ m⟧ ⟦0 ↦ e' ⟦n ↟ m⟧⟧ = e ⟦0 ↦ e'⟧ ⟦n ↟ m⟧ := ...

/- How `subst` interacts with itself. -/
lemma subst_subst_ind (e e₁ e₂ k n) : e ⟦nat.succ (n + k) ↦ e₂⟧ ⟦k ↦ e₁ ⟦n ↦ e₂⟧⟧ = e ⟦k ↦ e₁⟧ ⟦(n + k) ↦ e₂⟧ := ...
lemma subst_subst (e e₁ e₂ n) : e ⟦(nat.succ n) ↦ e₂⟧ ⟦0 ↦ e₁ ⟦n ↦ e₂⟧⟧ = e ⟦0 ↦ e₁⟧ ⟦n ↦ e₂⟧ := ...
```

</details>

### Reduction rules

```lean
/-- Small-step reduction rules. -/
inductive small : expr → expr → Prop
| s_beta      {t e r}     : small (app (lam t e) r) (expr.subst e 0 r)
| s_app_left  {l l' r}    : small l l' →   small (app l r) (app l' r)
| s_app_right {l r r'}    : small r r' →   small (app l r) (app l r')
| s_lam_left  {t t' e}    : small t t' →   small (lam t e) (lam t' e)
| s_lam_right {t e e'}    : small e e' →   small (lam t e) (lam t e')
| s_pi_left   {t₁ t₁' t₂} : small t₁ t₁' → small (pi t₁ t₂) (pi t₁' t₂)
| s_pi_right  {t₁ t₂ t₂'} : small t₂ t₂' → small (pi t₁ t₂) (pi t₁ t₂')

local notation e ` ~> ` e' := small e e'

/-- Transitive closure of small-step reduction rules. -/
inductive small_star : expr → expr → Prop
| ss_refl {e}        :                                  small_star e e
| ss_step {e₁ e₂ e₃} : small_star e₁ e₂ → small e₂ e₃ → small_star e₁ e₃

local notation e ` ~>* ` e' := small_star e e'
```

<details>
<summary>Useful lemmas</summary>
<br>

```lean
lemma small_star_refl (e) : e ~>* e := ...
lemma small_star_trans {e₁ e₂ e₃} (h₁ : e₁ ~>* e₂) (h₂ : e₂ ~>* e₃) : (e₁ ~>* e₃) := ...
lemma small_star_app {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : app l r ~>* app l' r' := ...
lemma small_star_lam {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : lam l r ~>* lam l' r' := ...
lemma small_star_pi {l l' r r'} (hl : l ~>* l') (hr : r ~>* r') : pi l r ~>* pi l' r' := ...

/-- Shifting respects small-step reduction. -/
lemma small_star_shift_ind {e e'} (h : e ~>* e') (s k) : e ⟦k ↟ s⟧ ~>* e' ⟦k ↟ s⟧ := ...
lemma small_star_shift {e e'} (h : e ~>* e') (s): e ⟦0 ↟ s⟧ ~>* e' ⟦0 ↟ s⟧ := ...

/-- Substitution respects small-step reduction. -/
lemma small_star_subst_ind {l l'} (hl : l ~>* l') {r r'} (hr : r ~>* r') (k) : l ⟦k ↦ r⟧ ~>* l' ⟦k ↦ r'⟧ := ...
lemma small_star_subst {l l'} (hl : l ~>* l') {r r'} (hr : r ~>* r') : l ⟦0 ↦ r⟧ ~>* l' ⟦0 ↦ r'⟧ := ...

/-- Confluence of small-step reduction. -/
lemma small_star_confluent {a b c} (hb : a ~>* b) (hc : a ~>* c) : ∃ d, (b ~>* d) ∧ (c ~>* d) := ...

/-- A term is in "normal form" iff there is no other term it reduces to. -/
def is_normal (e : expr) : Prop := ∀ e', ¬ (e ~> e')
lemma small_star_self_of_is_normal {e e'} (hn : is_normal e) (h: e ~>* e') : e = e' := ...

/-- If a term has a normal form, it must be unique. -/
lemma small_star_normal_unique {e e₁ e₂} (h₁ : e ~>* e₁) (hn₁ : is_normal e₁) (h₂ : e ~>* e₂) (hn₂ : is_normal e₂) : e₁ = e₂ := ...
```

</details>

### Typing rules

```lean
/-- Typing rules (without global environment and free variables). -/
inductive has_type : ctx → expr → expr → Prop
| t_conv {Γ e t t'} :
  small_eq t t' →
  has_type Γ e t →
  has_type Γ e t'
| t_sort {Γ n} :
  has_type Γ (sort n) (sort (nat.succ n))
| t_var {Γ n t} :
  list.nth Γ n = option.some t →
  has_type Γ (var n) (expr.shift t 0 (nat.succ n))
| t_app {Γ l r t₁ t₂} :
  has_type Γ l (pi t₁ t₂) →
  has_type Γ r t₁ →
  has_type Γ (app l r) (expr.subst t₂ 0 r)
| t_lam {Γ t₁ t₂ s e} :
  has_type Γ (pi t₁ t₂) (sort s) →
  has_type (t₁ :: Γ) e t₂ →
  has_type Γ (lam t₁ e) (pi t₁ t₂)
| t_pi {Γ t₁ s₁ t₂ s₂} :
  has_type Γ t₁ (sort s₁) →
  has_type (t₁ :: Γ) t₂ (sort s₂) →
  has_type Γ (pi t₁ t₂) (sort (max s₁ s₂))

local notation Γ ` ▷ ` e ` : ` t := has_type Γ e t
```

<details>
<summary>Useful lemmas</summary>
<br>

```lean
/-- Every well-formed (typeable) term has a unique type, up to definitional equality. -/
lemma has_type_unique {Γ e t t'} (h : Γ ▷ e : t) (h' : Γ ▷ e : t') : t ~~ t' := ...

lemma has_type_conv {Γ e t'} (t) (h : t ~~ t') (h' : Γ ▷ e : t) : Γ ▷ e : t' := ...
lemma has_type_sort {Γ n t} (h : Γ ▷ sort n : t) : t ~~ sort n.succ := ...
lemma has_type_var {Γ n t} (h : Γ ▷ var n : t) : ∃ t', (list.nth Γ n = option.some t') ∧ (t ~~ t'⟦0 ↟ n.succ⟧) := ...
lemma has_type_app {Γ l r t} (h : Γ ▷ app l r : t) : ∃ t₁ t₂, (Γ ▷ l : pi t₁ t₂) ∧ (Γ ▷ r : t₁) ∧ (t ~~ t₂ ⟦0 ↦ r⟧) := ...
lemma has_type_lam {Γ t₁ e t} (h : Γ ▷ lam t₁ e : t) : ∃ t₂ s, (Γ ▷ pi t₁ t₂ : sort s) ∧ (t₁ :: Γ ▷ e : t₂) ∧ (t ~~ pi t₁ t₂) := ...
lemma has_type_pi {Γ t₁ t₂ t} (h : Γ ▷ pi t₁ t₂ : t) : ∃ s₁ s₂, (Γ ▷ t₁ : sort s₁) ∧ (t₁ :: Γ ▷ t₂ : sort s₂) ∧ (t ~~ sort (max s₁ s₂)) := ...

/-- A term has equal types under equal contexts. -/
lemma has_type_small_eq_ctx {Γ Γ' e t} (he : Γ ~~c Γ') (h : Γ ▷ e : t) : Γ' ▷ e : t := ...

/-- How typing interacts with shifting. -/
lemma has_type_shift_ind (Δ : ctx) {Γ' Γ e t} (h : Γ' ++ Γ ▷ e : t) : ctxshift Γ' Δ.length ++ Δ ++ Γ ▷ e ⟦Γ'.length ↟ Δ.length⟧ : t ⟦Γ'.length ↟ Δ.length⟧ := ...
lemma has_type_shift (Δ : ctx) {Γ e t} (h : Γ ▷ e : t) : Δ ++ Γ ▷ e ⟦0 ↟ Δ.length⟧ : t ⟦0 ↟ Δ.length⟧ := ...

/-- How typing interacts with substitution. -/
lemma has_type_subst_ind {Γ Δ l r t₁ t₂} (hl : Γ ++ t₁ :: Δ ▷ l : t₂) (hr : Δ ▷ r : t₁) : ctxsubst Γ r ++ Δ ▷ l ⟦Γ.length ↦ r⟧ : t₂ ⟦Γ.length ↦ r⟧ := ...
lemma has_type_subst {Γ l r t₁ t₂} (hl : t₁ :: Γ ▷ l : t₂) (hr : Γ ▷ r : t₁) : Γ ▷ l ⟦0 ↦ r⟧ : t₂ ⟦0 ↦ r⟧ := ...

/-- Small-step reduction preserves type. -/
lemma has_type_small {Γ e e' t} (h : Γ ▷ e : t) (h' : e ~> e') : (Γ ▷ e' : t) := ...
lemma has_type_small_star {Γ e e' t} (h : Γ ▷ e : t) (h' : e ~>* e') : (Γ ▷ e' : t) := ...
```

</details>

## References

Confluence proof follows the Tait and Martin-Löf technique as described in [An Intuitionistic Theory of Types](https://archive-pml.github.io/martin-lof/pdfs/An-Intuitionistic-Theory-of-Types-1972.pdf).
