import Lean.Meta

namespace Coc
section

/-- Expressions (preterms) -/
inductive Expr : Type
  | sort : Nat →         Expr
  | var  : Nat →         Expr
  | app  : Expr → Expr → Expr
  | lam  : Expr → Expr → Expr
  | pi   : Expr → Expr → Expr
deriving DecidableEq

/-- Debug output. -/
def Expr.show : Expr → String
  | sort s   => s!"Sort {toString s}"
  | var v    => s!"#{toString v}"
  | app l r  =>
    let fl := match l with
      | sort _  => false
      | var _   => false
      | app _ _ => false
      | _       => true;
    let fr := match r with
      | sort _  => false
      | var _   => false
      | _       => true;
    s!"{if fl then "(" else ""}{Expr.show l}{if fl then ")" else ""}" ++ " " ++
    s!"{if fr then "(" else ""}{Expr.show r}{if fr then ")" else ""}"
  | lam t e  => s!"fun #: {Expr.show t} => {Expr.show e}"
  | pi t₁ t₂ => s!"(#: {Expr.show t₁}) -> {Expr.show t₂}"

instance : ToString Expr := ⟨Expr.show⟩
instance : Repr Expr := ⟨fun e _ => e.show⟩

/-- Size measure for strong induction. -/
def Expr.size : Expr → Nat
  | sort _   => 1
  | var _    => 1
  | app l r  => Nat.succ (Expr.size l + Expr.size r)
  | lam t e  => Nat.succ (Expr.size t + Expr.size e)
  | pi t₁ t₂ => Nat.succ (Expr.size t₁ + Expr.size t₂)

/-- Lift variables with level ≥ `n` by `m` levels. -/
def Expr.shift : Expr → Nat → Nat → Expr
  | sort s,   _, _ => .sort s
  | var v,    n, m => if n <= v then .var (v + m) else .var v
  | app l r,  n, m => .app (Expr.shift l n m) (Expr.shift r n m)
  | lam t e,  n, m => .lam (Expr.shift t n m) (Expr.shift e (Nat.succ n) m)
  | pi t₁ t₂, n, m => .pi (Expr.shift t₁ n m) (Expr.shift t₂ (Nat.succ n) m)

/-- Replace all variables at level = `n` by an expression `e'`
    (when deleting the outermost layer of binder). -/
def Expr.subst : Expr → Nat → Expr → Expr
  | sort s,   _, _  => .sort s
  | var v,    n, e' => if n < v then .var (Nat.pred v) else if n = v then Expr.shift e' 0 n else .var v
  | app l r,  n, e' => .app (Expr.subst l n e') (Expr.subst r n e')
  | lam t e,  n, e' => .lam (Expr.subst t n e') (Expr.subst e (Nat.succ n) e')
  | pi t₁ t₂, n, e' => .pi (Expr.subst t₁ n e') (Expr.subst t₂ (Nat.succ n) e')

/-- Small-step reduction rules. -/
inductive Small : Expr → Expr → Prop
  | beta     {t e r}     : Small (.app (.lam t e) r) (Expr.subst e 0 r)
  | appLeft  {l l' r}    : Small l l' →   Small (.app l r) (.app l' r)
  | appRight {l r r'}    : Small r r' →   Small (.app l r) (.app l r')
  | lamLeft  {t t' e}    : Small t t' →   Small (.lam t e) (.lam t' e)
  | lamRight {t e e'}    : Small e e' →   Small (.lam t e) (.lam t e')
  | piLeft   {t₁ t₁' t₂} : Small t₁ t₁' → Small (.pi t₁ t₂) (.pi t₁' t₂)
  | piRight  {t₁ t₂ t₂'} : Small t₂ t₂' → Small (.pi t₁ t₂) (.pi t₁ t₂')

/-- Transitive closure of small-step reduction rules. -/
inductive SmallStar : Expr → Expr → Prop
  | refl {e}        :                                 SmallStar e e
  | step {e₁ e₂ e₃} : SmallStar e₁ e₂ → Small e₂ e₃ → SmallStar e₁ e₃

/-- Symmetric transitive closure of small-step reduction rules. -/
inductive Defeq : Expr → Expr → Prop
  | refl  {e}        :                             Defeq e e
  | step  {e₁ e₂}    : Small e₁ e₂ →               Defeq e₁ e₂
  | symm  {e₁ e₂}    : Defeq e₁ e₂ →               Defeq e₂ e₁
  | trans {e₁ e₂ e₃} : Defeq e₁ e₂ → Defeq e₂ e₃ → Defeq e₁ e₃

/-- Contexts (precontexts) -/
def Ctx : Type := List Expr deriving DecidableEq

instance : ToString Ctx := ⟨List.toString⟩
instance : Repr Ctx := ⟨List.repr⟩
instance : Append Ctx := ⟨List.append⟩

/-- Lean 3 does not have good specialised support for mutually inductive types. -/
inductive JudgmentIndex : Type
  | wellCtx : Ctx →               JudgmentIndex
  | hasType : Ctx → Expr → Expr → JudgmentIndex
deriving DecidableEq

/-- Typing rules. -/
inductive Judgment : JudgmentIndex → Prop
  | nil :
    Judgment (.wellCtx [])
  | cons {Γ t s} :
    Judgment (.hasType Γ t (.sort s)) →
    Judgment (.wellCtx (t :: Γ))
  | conv {Γ e t t' s} :
    Defeq t t' →
    Judgment (.hasType Γ t' (.sort s)) →
    Judgment (.hasType Γ e t) →
    Judgment (.hasType Γ e t')
  | sort {Γ n} :
    Judgment (.wellCtx Γ) →
    Judgment (.hasType Γ (.sort n) (.sort (Nat.succ n)))
  | var {Γ n t} :
    Judgment (.wellCtx Γ) →
    List.get? Γ n = some t →
    Judgment (.hasType Γ (.var n) (Expr.shift t 0 (Nat.succ n)))
  | app {Γ l r t₁ t₂} :
    Judgment (.hasType Γ l (.pi t₁ t₂)) →
    Judgment (.hasType Γ r t₁) →
    Judgment (.hasType Γ (.app l r) (Expr.subst t₂ 0 r))
  | lam {Γ t₁ t₂ s e} :
    Judgment (.hasType Γ (.pi t₁ t₂) (.sort s)) →
    Judgment (.hasType (t₁ :: Γ) e t₂) →
    Judgment (.hasType Γ (.lam t₁ e) (.pi t₁ t₂))
  | pi {Γ t₁ s₁ t₂ s₂} :
    Judgment (.hasType Γ t₁ (.sort s₁)) →
    Judgment (.hasType (t₁ :: Γ) t₂ (.sort s₂)) →
    Judgment (.hasType Γ (.pi t₁ t₂) (.sort (max s₁ s₂)))

#eval Lean.Meta.getEqnsFor? ``Expr.size
#eval Lean.Meta.getEqnsFor? ``Expr.shift
#eval Lean.Meta.getEqnsFor? ``Expr.subst

end
end Coc
