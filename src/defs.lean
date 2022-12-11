namespace coc
section

/-- Expressions (preterms) -/
@[derive decidable_eq]
inductive expr : Type
| sort : nat →         expr
| var  : nat →         expr
| app  : expr → expr → expr
| lam  : expr → expr → expr
| pi   : expr → expr → expr
open expr

/-- Debug output. -/
def expr.show : expr → string
| (sort s)   := "Sort " ++ to_string s
| (var v)    := "#" ++ to_string v
| (app l r)  :=
  let fl := match l with | (sort _) := ff | (var _) := ff | (app _ _) := ff | _ := tt end in
  let fr := match r with | (sort _) := ff | (var _) := ff | _ := tt end in
    (ite fl "(" "") ++ l.show ++ (ite fl ")" "") ++ " " ++
    (ite fr "(" "") ++ r.show ++ (ite fr ")" "")
| (lam t e)  := "fun #: " ++ t.show ++ " => " ++ e.show
| (pi t₁ t₂) := "(#: " ++ t₁.show ++ ") -> " ++ t₂.show

instance : has_to_string expr := ⟨expr.show⟩
instance : has_repr expr := ⟨expr.show⟩

/-- Size measure for strong induction. -/
def expr.size : expr → nat
| (sort s)   := 1
| (var v)    := 1
| (app l r)  := nat.succ (expr.size l + expr.size r)
| (lam t e)  := nat.succ (expr.size t + expr.size e)
| (pi t₁ t₂) := nat.succ (expr.size t₁ + expr.size t₂)

/-- Lift variables with level ≥ `n` by `m` levels. -/
@[irreducible]
def expr.shift : expr → nat → nat → expr
| (sort s)   n m := sort s
| (var v)    n m := if n <= v then var (v + m) else var v
| (app l r)  n m := app (expr.shift l n m) (expr.shift r n m)
| (lam t e)  n m := lam (expr.shift t n m) (expr.shift e (nat.succ n) m)
| (pi t₁ t₂) n m := pi (expr.shift t₁ n m) (expr.shift t₂ (nat.succ n) m)

/-- Replace all variables at level = `n` by an expression `e'`
    (when deleting the outermost layer of binder). -/
@[irreducible]
def expr.subst : expr → nat → expr → expr
| (sort s)   n e' := sort s
| (var v)    n e' := if n < v then var (nat.pred v) else if n = v then expr.shift e' 0 n else var v
| (app l r)  n e' := app (expr.subst l n e') (expr.subst r n e')
| (lam t e)  n e' := lam (expr.subst t n e') (expr.subst e (nat.succ n) e')
| (pi t₁ t₂) n e' := pi (expr.subst t₁ n e') (expr.subst t₂ (nat.succ n) e')

/-- Small-step reduction rules. -/
inductive small : expr → expr → Prop
| s_beta      {t e r}     : small (app (lam t e) r) (expr.subst e 0 r)
| s_app_left  {l l' r}    : small l l' →   small (app l r) (app l' r)
| s_app_right {l r r'}    : small r r' →   small (app l r) (app l r')
| s_lam_left  {t t' e}    : small t t' →   small (lam t e) (lam t' e)
| s_lam_right {t e e'}    : small e e' →   small (lam t e) (lam t e')
| s_pi_left   {t₁ t₁' t₂} : small t₁ t₁' → small (pi t₁ t₂) (pi t₁' t₂)
| s_pi_right  {t₁ t₂ t₂'} : small t₂ t₂' → small (pi t₁ t₂) (pi t₁ t₂')
open small

/-- Transitive closure of small-step reduction rules. -/
inductive small_star : expr → expr → Prop
| ss_refl {e}        :                                  small_star e e
| ss_step {e₁ e₂ e₃} : small_star e₁ e₂ → small e₂ e₃ → small_star e₁ e₃
open small_star

/-- Symmetric transitive closure of small-step reduction rules. -/
inductive defeq : expr → expr → Prop
| de_refl  {e}        :                             defeq e e
| de_step  {e₁ e₂}    : small e₁ e₂ →               defeq e₁ e₂
| de_symm  {e₁ e₂}    : defeq e₁ e₂ →               defeq e₂ e₁
| de_trans {e₁ e₂ e₃} : defeq e₁ e₂ → defeq e₂ e₃ → defeq e₁ e₃
open defeq

/-- Contexts (precontexts) -/
def ctx : Type := list expr

instance : has_to_string ctx := ⟨list.to_string⟩
instance : has_repr ctx := ⟨list.to_string⟩
instance : has_append ctx := ⟨list.append⟩

/-- Lean 3 does not have good specialised support for mutually inductive types. -/
@[derive decidable_eq]
inductive judgment_index : Type
| well_ctx : ctx →               judgment_index
| has_type : ctx → expr → expr → judgment_index
open judgment_index

/-- Typing rules. -/
inductive judgment : judgment_index → Prop
| c_nil :
  judgment (well_ctx [])
| c_cons {Γ t s} :
  judgment (has_type Γ t (sort s)) →
  judgment (well_ctx (t :: Γ))
| t_conv {Γ e t t' s} :
  defeq t t' →
  judgment (has_type Γ t' (sort s)) →
  judgment (has_type Γ e t) →
  judgment (has_type Γ e t')
| t_sort {Γ n} :
  judgment (well_ctx Γ) →
  judgment (has_type Γ (sort n) (sort (nat.succ n)))
| t_var {Γ n t} :
  judgment (well_ctx Γ) →
  list.nth Γ n = option.some t →
  judgment (has_type Γ (var n) (expr.shift t 0 (nat.succ n)))
| t_app {Γ l r t₁ t₂} :
  judgment (has_type Γ l (pi t₁ t₂)) →
  judgment (has_type Γ r t₁) →
  judgment (has_type Γ (app l r) (expr.subst t₂ 0 r))
| t_lam {Γ t₁ t₂ s e} :
  judgment (has_type Γ (pi t₁ t₂) (sort s)) →
  judgment (has_type (t₁ :: Γ) e t₂) →
  judgment (has_type Γ (lam t₁ e) (pi t₁ t₂))
| t_pi {Γ t₁ s₁ t₂ s₂} :
  judgment (has_type Γ t₁ (sort s₁)) →
  judgment (has_type (t₁ :: Γ) t₂ (sort s₂)) →
  judgment (has_type Γ (pi t₁ t₂) (sort (max s₁ s₂)))
open judgment

end
end coc
