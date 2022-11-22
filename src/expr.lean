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

def expr.size : expr → nat
| (sort s)   := 1
| (var v)    := 1
| (app l r)  := (l.size + r.size).succ
| (lam t e)  := (t.size + e.size).succ
| (pi t₁ t₂) := (t₁.size + t₂.size).succ

def expr.closed : expr → nat → Prop
| (sort s)        n := true
| (var (bound b)) n := b < n
| (var (free f))  n := true
| (app l r)       n := expr.closed l n ∧ expr.closed r n
| (lam t e)       n := expr.closed t n ∧ expr.closed e n.succ
| (pi t₁ t₂)      n := expr.closed t₁ n ∧ expr.closed t₂ n.succ

structure cexpr (n : nat) : Type :=
  (e : expr) (hce : expr.closed e n)

/-- Make a free variable into an "overflowed" bound variable. -/
@[irreducible]
def expr.bind : expr → nat → nat → expr
| (sort s)   n f := sort s
| (var v)    n f := if v = free f then var (bound n) else var v
| (app l r)  n f := app (expr.bind l n f) (expr.bind r n f)
| (lam t e)  n f := lam (expr.bind t n f) (expr.bind e n.succ f)
| (pi t₁ t₂) n f := pi (expr.bind t₁ n f) (expr.bind t₂ n.succ f)

/-- Replace one overflow variable by an expression. -/
@[irreducible]
def expr.subs : expr → nat → expr → expr
| (sort s)   n e' := sort s
| (var v)    n e' := if v = bound n then e' else var v
| (app l r)  n e' := app (expr.subs l n e') (expr.subs r n e')
| (lam t e)  n e' := lam (expr.subs t n e') (expr.subs e n.succ e')
| (pi t₁ t₂) n e' := pi (expr.subs t₁ n e') (expr.subs t₂ n.succ e')

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
