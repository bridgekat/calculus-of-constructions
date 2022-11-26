import defs

namespace coc
section

open option
open idx
open expr

/-- Size measure for strong induction. -/
def expr.size : expr → nat
| (sort s)   := 1
| (var v)    := 1
| (app l r)  := (l.size + r.size).succ
| (lam t e)  := (t.size + e.size).succ
| (pi t₁ t₂) := (t₁.size + t₂.size).succ

/-- Lift variables with level ≥ `n` by `m` levels. -/
@[irreducible]
def expr.shift : expr → nat → nat → expr
| (sort s)        n m := sort s
| (var (bound b)) n m :=
  if n <= b then var (bound (b + m))
  else var (bound b)
| (var (free f))  n m := var (free f)
| (app l r)       n m := app (expr.shift l n m) (expr.shift r n m)
| (lam t e)       n m := lam (expr.shift t n m) (expr.shift e n.succ m)
| (pi t₁ t₂)      n m := pi (expr.shift t₁ n m) (expr.shift t₂ n.succ m)

/-- Replace all variables at level = `n` by an expression `e'`
    (when deleting the outermost layer of binder). -/
@[irreducible]
def expr.subst : expr → nat → expr → expr
| (sort s)        n e' := sort s
| (var (bound b)) n e' :=
  if n < b then var (bound (nat.pred b))
  else if n = b then expr.shift e' 0 n
  else (var (bound b))
| (var (free f))  n e' := var (free f)
| (app l r)       n e' := app (expr.subst l n e') (expr.subst r n e')
| (lam t e)       n e' := lam (expr.subst t n e') (expr.subst e n.succ e')
| (pi t₁ t₂)      n e' := pi (expr.subst t₁ n e') (expr.subst t₂ n.succ e')

/-- Small-step reduction rules. -/
inductive small : expr → expr → Prop
| s_beta      {t e r}     : small (app (lam t e) r) (e.subst 0 r)
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

/-- Symmetric transitive closure of small-step reduction rules. -/
inductive small_eq : expr → expr → Prop
| se_refl  {e}        :                                   small_eq e e
| se_step  {e₁ e₂}    : small e₁ e₂ →                     small_eq e₁ e₂
| se_symm  {e₁ e₂}    : small_eq e₁ e₂ →                  small_eq e₂ e₁
| se_trans {e₁ e₂ e₃} : small_eq e₁ e₂ → small_eq e₂ e₃ → small_eq e₁ e₃

/-- Typing rules (without global environment and free variables). -/
inductive has_type : ctx → expr → expr → Prop
| t_conv {Γ e t t'} :
  small_eq t t' →
  has_type Γ e t →
  has_type Γ e t'
| t_sort {Γ n} :
  has_type Γ (sort n) (sort n.succ)
| t_var {Γ n t} :
  list.nth Γ n = some t →
  has_type Γ (var (bound n)) t
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

/-- Rules for defining well-formed local contexts. -/
inductive lawful_ctx : ctx → Prop
| c_nil          :                                        lawful_ctx []
| c_cons {Γ t s} : lawful_ctx Γ → has_type Γ t (sort s) → lawful_ctx (t :: Γ)

/-- Performs applicative-order beta-reduction.
    If the original expression is well-typed, the resulting expression will have the same type.
    Note that this function is only a syntactic operation, and does not check well-formedness.
    It does not terminate on inputs like `(fun x => x x x) (fun x => x x x)`. -/
meta def expr.reduce : expr → expr
| (sort s)   := sort s
| (var v)    := var v
| (app l r)  :=
  let l := l.reduce,
      r := r.reduce
  in match l with
  | (lam t e) := (expr.subst e 0 r).reduce
  | _         := app l r
  end
| (lam t e)  := lam t.reduce e.reduce
| (pi t₁ t₂) := pi t₁.reduce t₂.reduce

end
end coc
