namespace coc
section

/-- Bound and free variables (de Bruijn indices and global IDs.) -/
@[derive decidable_eq]
inductive idx : Type
| bound : nat → idx
| free  : nat → idx
open idx

def idx.show : idx → string
| (bound id) := "?b" ++ to_string id
| (free id)  := "?f" ++ to_string id

instance : has_to_string idx := ⟨idx.show⟩
instance : has_repr idx := ⟨idx.show⟩

/-- Expressions (preterms) -/
@[derive decidable_eq]
inductive expr : Type
| sort : nat →         expr
| var  : idx →         expr
| app  : expr → expr → expr
| lam  : expr → expr → expr
| pi   : expr → expr → expr
open expr

def expr.show : expr → string
| (sort s)   := "Sort " ++ to_string s
| (var v)    := v.show
| (app l r)  :=
  let fl := match l with | (sort _) := ff | (var _) := ff | (app _ _) := ff | _ := tt end in
  let fr := match r with | (sort _) := ff | (var _) := ff | _ := tt end in
    (ite fl "(" "") ++ l.show ++ (ite fl ")" "") ++ " " ++
    (ite fr "(" "") ++ r.show ++ (ite fr ")" "")
| (lam t e)  := "fun #: " ++ t.show ++ " => " ++ e.show
| (pi t₁ t₂) := "(#: " ++ t₁.show ++ ") -> " ++ t₂.show

instance : has_to_string expr := ⟨expr.show⟩
instance : has_repr expr := ⟨expr.show⟩

/-- Contexts (precontexts) -/
@[derive decidable_eq]
inductive ctx : Type
| nil  :              ctx
| cons : expr → ctx → ctx
open ctx

notation `⟦`:max t:max `⟧`:max ` :: `:max Γ:max := cons t Γ

def ctx.show : ctx → string
| nil        := "ctx.nil\n"
| (cons t Γ) := "⟦" ++ t.show ++ "⟧ ::\n" ++ ctx.show Γ 

instance : has_to_string ctx := ⟨ctx.show⟩
instance : has_repr ctx := ⟨ctx.show⟩

end
end coc