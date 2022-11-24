import defs

namespace coc
section

open option
open idx
open expr

def imax : nat → nat → nat
| 0 _ := 0
| _ 0 := 0
| a b := max a b

/-- Size measure for strong structural induction. -/
def expr.size : expr → nat
| (sort s)   := 1
| (var v)    := 1
| (app l r)  := (l.size + r.size).succ
| (lam t e)  := (t.size + e.size).succ
| (pi t₁ t₂) := (t₁.size + t₂.size).succ

/-- Three-way comparison operator. -/
inductive threeway (m n : nat) : Prop
| lt : m < n → threeway
| eq : m = n → threeway
| gt : n < m → threeway

@[irreducible]
def threeway_cmp (m n : nat) : threeway m n :=
  dite (m < n) threeway.lt
    (dite (m = n) (λ h _, threeway.eq h)
      (λ h₁ h₂, threeway.gt
        (nat.lt_of_le_and_ne (le_of_not_lt h₂)
          (λ h : n = m, (h₁ h.symm)))))

/-- Lift overflow variables by `m` levels. -/
@[irreducible]
def expr.gap : expr → nat → nat → expr
| (sort s)        n m := sort s
| (var (bound b)) n m :=
  if n <= b then var (bound (b + m))
  else var (bound b)
| (var (free f))  n m := var (free f)
| (app l r)       n m := app (expr.gap l n m) (expr.gap r n m)
| (lam t e)       n m := lam (expr.gap t n m) (expr.gap e n.succ m)
| (pi t₁ t₂)      n m := pi (expr.gap t₁ n m) (expr.gap t₂ n.succ m)

/-- Replace one overflow variable by an expression
    (when deleting the outermost layer of binder). -/
@[irreducible]
def expr.subs : expr → nat → expr → expr
| (sort s)        n e' := sort s
| (var (bound b)) n e' :=
  if n < b then var (bound b.pred)
  else if n = b then e'.gap 0 n
  else (var (bound b))
| (var (free f))  n e' := var (free f)
| (app l r)       n e' := app (expr.subs l n e') (expr.subs r n e')
| (lam t e)       n e' := lam (expr.subs t n e') (expr.subs e n.succ e')
| (pi t₁ t₂)      n e' := pi (expr.subs t₁ n e') (expr.subs t₂ n.succ e')

/-- Small-step reduction rules. -/
inductive small : expr → expr → Prop
| s_beta      {t e r}     : small (app (lam t e) r) (e.subs 0 r)
| s_app_left  {l l' r}    : small l l' →   small (app l r) (app l' r)
| s_app_right {l r r'}    : small r r' →   small (app l r) (app l r')
| s_lam_left  {t t' e}    : small t t' →   small (lam t e) (lam t' e)
| s_lam_right {t e e'}    : small e e' →   small (lam t e) (lam t e')
| s_pi_left   {t₁ t₁' t₂} : small t₁ t₁' → small (pi t₁ t₂) (pi t₁' t₂)
| s_pi_right  {t₁ t₂ t₂'} : small t₂ t₂' → small (pi t₁ t₂) (pi t₁ t₂')

/-- Transitive closure of small-step reduction rules. -/
inductive small_star : expr → expr → Prop
| ss_refl {e}        :                                    small_star e e
| ss_step {e₁ e₂ e₃} : small_star e₁ e₂ → (small e₂ e₃) → small_star e₁ e₃

/-- Symmetric transitive closure of small-step reduction rules. -/
inductive small_eq : expr → expr → Prop
| ss_refl {e}        :                                  small_eq e e
| ss_symm {e₁ e₂}    : small_eq e₁ e₂ →                 small_eq e₂ e₁
| ss_step {e₁ e₂ e₃} : small_eq e₁ e₂ → (small e₂ e₃) → small_eq e₁ e₃

/-- Typing rules (without free variables). -/
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
  has_type Γ (app l r) (t₂.subs 0 r)
| t_lam {Γ t₁ t₂ s e} :
  has_type Γ (pi t₁ t₂) (sort s) →
  has_type (t₁ :: Γ) e t₂ →
  has_type Γ (lam t₁ e) (pi t₁ t₂)
| t_pi {Γ t₁ s₁ t₂ s₂} :
  has_type Γ t₁ (sort s₁) →
  has_type (t₁ :: Γ) t₂ (sort s₂) →
  has_type Γ (pi t₁ t₂) (sort (imax s₁ s₂))

/-- Rules for defining well-formed local contexts. -/
inductive ctx_wf : ctx → Prop
| c_nil          :                                    ctx_wf []
| c_cons {Γ t s} : ctx_wf Γ → has_type Γ t (sort s) → ctx_wf (t :: Γ)

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
  | (lam t e) := (e.subs 0 r).reduce
  | _         := app l r
  end
| (lam t e)  := lam t.reduce e.reduce
| (pi t₁ t₂) := pi t₁.reduce t₂.reduce

end
end coc
