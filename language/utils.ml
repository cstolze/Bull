type family =
  | SFc of family * family
  | SAnd of family * family
  | SOr of family * family
  | SAtom of string

type kind =
  | Type

type delta =
  | DVar of string
  | DLambda of string * family * delta
  | DApp of delta * delta
  | DAnd of delta * delta
  | DProjL of delta
  | DProjR of delta
  | DOr of delta * delta
  | DInjL of delta
  | DInjR of delta

type sentence =
  | Quit
  | Load of string
  | Proof of string * family
  | Typecst of string * kind
  | Cst of string * family
  | Typecheck of string * delta * family
  | Typeinfer of string * delta
  | Error

type proofrule =
  | PVar
  | PAbort
  | PIntro
  | PElim of family
  | PSconj
  | PProjL of family
  | PProjR of family
  | PInjL
  | PInjR
  | PSdisj of family * family
  | PBacktrack
  | PChangerule
  | PError
