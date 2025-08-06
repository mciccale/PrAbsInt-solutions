inductive ExpKind where
  | arith
  | bool

@[reducible]
def ExpKind.interp : ExpKind → Type
  | arith => Int
  | bool  => Bool

inductive Exp : ExpKind → Type where
  | one  : Exp .arith
  | sub  : Exp .arith → Exp .arith → Exp .arith
  | tt   : Exp .bool
  | ff   : Exp .bool
  | lt   : Exp .arith → Exp .arith → Exp .bool
  | nand : Exp .bool → Exp .bool → Exp .bool

def Exp.eval {kind: ExpKind} : Exp kind → kind.interp
  | .one        => 1
  | .sub  e₁ e₂ => eval e₁ - eval e₂
  | .tt         => true
  | .ff         => false
  | .lt   e₁ e₂ => eval e₁ < eval e₂
  | .nand e₁ e₂ => !(eval e₁ && eval e₂)

#eval Exp.eval (Exp.sub (Exp.sub Exp.one Exp.one) Exp.one)
