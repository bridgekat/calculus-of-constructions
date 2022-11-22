import system.io
import checker

namespace coc
section

open idx
open expr
open ctx

-- Examples adapted from ApiMu (FOLContext).
def bv := var ∘ bound
def fv := var ∘ free
def prop := sort 0
def type := sort 1
def bin := λ a f b, app (app f a) b

def c₁ :=
  ⟦(pi (fv 0) $ pi (fv 0) prop)⟧ :: -- [13] mem       : setvar → setvar → Prop
  ⟦(pi (pi (fv 0) prop) prop)  ⟧ :: -- [12] unique    : (setvar → Prop) → Prop
  ⟦(pi (pi (fv 0) prop) prop)  ⟧ :: -- [11] exists    : (setvar → Prop) → Prop
  ⟦(pi (pi (fv 0) prop) prop)  ⟧ :: -- [10] forall    : (setvar → Prop) → Prop
  ⟦(pi prop $ pi prop prop)    ⟧ :: -- [9]  iff       : Prop → Prop → Prop
  ⟦(pi prop $ pi prop prop)    ⟧ :: -- [8]  implies   : Prop → Prop → Prop
  ⟦(pi prop $ pi prop prop)    ⟧ :: -- [7]  or        : Prop → Prop → Prop
  ⟦(pi prop $ pi prop prop)    ⟧ :: -- [6]  and       : Prop → Prop → Prop
  ⟦(pi prop prop)              ⟧ :: -- [5]  not       : Prop → Prop
  ⟦prop                        ⟧ :: -- [4]  false     : Prop
  ⟦prop                        ⟧ :: -- [3]  true      : Prop
  ⟦(pi (fv 0) $ pi (fv 0) prop)⟧ :: -- [2]  equals    : setvar → setvar → Prop
  ⟦(fv 0)                      ⟧ :: -- [1]  arbitrary : setvar 
  ⟦type                        ⟧ :: -- [0]  setvar    : Type
  nil

def and := fv 6
def iff := fv 9
def for := app (fv 10) ∘ lam (fv 0)
def exi := app (fv 11) ∘ lam (fv 0)
def mem := fv 13

def e₁ :=
  (lam (pi (fv 0) $ pi (fv 0) prop)
    (for $ exi $ for $
      (bin (bin (bv 0) mem (bv 1))
       iff (bin (bin (bv 0) mem (bv 2))
            and (app (app (bv 3) (bv 2)) (bv 0))))))

meta def main : io unit := do
{ io.put_str_ln c₁.show,
  io.put_str_ln e₁.show,
  io.put_str_ln "",
  match e₁.check c₁ with
  | (sum.inl msg) := io.put_str_ln $ "Error: " ++ msg
  | (sum.inr t)   := io.put_str_ln t.show
  end,
  io.put_str_ln "",
  return () }

#eval main

end
end coc
