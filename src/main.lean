import system.io
import checker

namespace coc
section

open expr
open ctx

-- Examples adapted from ApiMu (FOLContext).
def prop := sort 0
def type := sort 1
def bin := λ a f b, app (app f a) b

def c₁ : ctx :=
  [ (pi (var 12) $ pi (var 12) prop), -- [13] mem       : setvar → setvar → Prop
    (pi (pi (var 11) prop) prop),     -- [12] unique    : (setvar → Prop) → Prop
    (pi (pi (var 10) prop) prop),     -- [11] exists    : (setvar → Prop) → Prop
    (pi (pi (var 9) prop) prop),      -- [10] forall    : (setvar → Prop) → Prop
    (pi prop $ pi prop prop),         -- [9]  iff       : Prop → Prop → Prop
    (pi prop $ pi prop prop),         -- [8]  implies   : Prop → Prop → Prop
    (pi prop $ pi prop prop),         -- [7]  or        : Prop → Prop → Prop
    (pi prop $ pi prop prop),         -- [6]  and       : Prop → Prop → Prop
    (pi prop prop),                   -- [5]  not       : Prop → Prop
    prop,                             -- [4]  false     : Prop
    prop,                             -- [3]  true      : Prop
    (pi (var 0) $ pi (var 0) prop),   -- [2]  equals    : setvar → setvar → Prop
    (var 0),                          -- [1]  arbitrary : setvar
    type ]                            -- [0]  setvar    : Type

def e₁ :=
  lam (pi (var 13) $ pi (var 13) prop) $
    app (var 4) ∘ lam (var 14) $
      app (var 4) ∘ lam (var 15) $
        app (var 6) ∘ lam (var 16) $
          (bin (bin (var 0) (var 4) (var 1))
            (var 8) (bin (bin (var 0) (var 4) (var 2))
              (var 11) (app (app (var 3) (var 2)) (var 0))))

meta def main : io unit := do
{ io.put_str_ln c₁.to_string,
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
