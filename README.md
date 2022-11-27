Proofs of **confluence**, **unique typing** and **type preservation** can be found in [`lemmas.lean`](https://github.com/bridgekat/calculus-of-constructions/blob/main/src/lemmas.lean).

(TODO: add more explanation)

## Details

Consider terms

```lean
inductive expr : Type
| sort : nat →         expr
| var  : idx →         expr
| app  : expr → expr → expr
| lam  : expr → expr → expr
| pi   : expr → expr → expr
open expr
```

where `idx` denote standard de Bruijn indices.

Single-variable substitution is defined as

```lean
/-- Lift variables with level ≥ `n` by `m` levels. -/
def expr.shift : expr → nat → nat → expr
| (sort s)        n m := sort s
| (var (bound b)) n m :=
  if n <= b then var (bound (b + m))
  else var (bound b)
| (var (free f))  n m := var (free f)
| (app l r)       n m := app (expr.shift l n m) (expr.shift r n m)
| (lam t e)       n m := lam (expr.shift t n m) (expr.shift e (nat.succ n) m)
| (pi t₁ t₂)      n m := pi (expr.shift t₁ n m) (expr.shift t₂ (nat.succ n) m)

/-- Replace all variables at level = `n` by an expression `e'`
    (when deleting the outermost layer of binder). -/
def expr.subst : expr → nat → expr → expr
| (sort s)        n e' := sort s
| (var (bound b)) n e' :=
  if n < b then var (bound (nat.pred b))
  else if n = b then expr.shift e' 0 n
  else (var (bound b))
| (var (free f))  n e' := var (free f)
| (app l r)       n e' := app (expr.subst l n e') (expr.subst r n e')
| (lam t e)       n e' := lam (expr.subst t n e') (expr.subst e (nat.succ n) e')
| (pi t₁ t₂)      n e' := pi (expr.subst t₁ n e') (expr.subst t₂ (nat.succ n) e')
```

(...this is definitely far from the optimal formalisation, especially in comparison with [Autosubst.](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf))

Reduction rules considered:

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

/-- Transitive closure of small-step reduction rules. -/
inductive small_star : expr → expr → Prop
| ss_refl {e}        :                                  small_star e e
| ss_step {e₁ e₂ e₃} : small_star e₁ e₂ → small e₂ e₃ → small_star e₁ e₃
```

Typing rules considered:

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
  has_type Γ (var (bound n)) (expr.shift t 0 (nat.succ n))
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
```

## References

Confluence proof follows the Tait and Martin-Löf technique as described in [An Intuitionistic Theory of Types](https://archive-pml.github.io/martin-lof/pdfs/An-Intuitionistic-Theory-of-Types-1972.pdf).
