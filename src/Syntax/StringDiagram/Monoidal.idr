module Syntax.StringDiagram.Monoidal

import public Control.Category.Core
import public Control.Category.Functor
import public Control.Category.Monoidal
import Data.Wrap0
import public Language.Reflection
import public Syntax.StringDiagram.Util

%default total
%language ElabReflection

export infix 0 -<
export prefix 0 =<

record MonDiagramStep where
  constructor MkMDStep
  l, c, c', r : Nat
  mor : TTImp

MonDiagram : Type
MonDiagram = List MonDiagramStep

findSublist : Eq a => (sub, full : List a) -> Maybe (List a, List a)
findSublist [] full = Just ([], full)
findSublist (_ :: _) [] = Nothing
findSublist (s :: sub) (f :: full) =
  if s == f
  then findSublist sub full
  else mapFst (f::) <$> findSublist (s :: sub) full

||| Check if this string diagram is valid in a monoidal category.
checkDiagram : SDiagram -> Elab MonDiagram
checkDiagram (MkSDiagram inp steps out) = do
  let Just strings = the (Maybe _) $ sequence inp
    | Nothing => fail "Strings cannot be discarded"
  checkDiagram' [<] strings steps
  where
    checkDiagram' : SnocList MonDiagramStep -> List String -> List SDiagramStep -> Elab MonDiagram
    checkDiagram' diag strings (MkSDStep i m o :: steps) = do
      let Just o' = the (Maybe _) $ sequence o
        | Nothing => fail "Strings cannot be discarded"
      let False = any (\name => elem name strings) o'
        | True => fail "Cannot shadow string name"
      let Just (l,r) = findSublist i strings
        | Nothing => fail "Strings are not contiguous"
      checkDiagram'
        (diag :< MkMDStep (length l) (length i) (length o) (length r) m)
        (l ++ o' ++ r) steps
    checkDiagram' diag strings [] =
      if strings == out
      then pure (diag <>> [])
      else fail "Return strings are not contiguous"

||| Expand shortened string diagram notation into a full expression.
|||
||| This takes two additional parameters: `obj`, which is a wildcard
||| expression used when passing objects as parameters, and `impl`,
||| which is the `Monoidal` implementation the expansion will use.
export
stringImpl : (obj,impl : TTImp) -> TTImp -> Elab TTImp
stringImpl obj impl t = do
  diag <- checkDiagram =<< parseDiagram t
  cat <- genSym "cat"
  ts <- for diag $ \(MkMDStep l c c' r mor) => do
    pure `(
      Control.Category.Monoidal.applyAssoc
      @{~impl}
      {xs = ~(listImp l), ys = ~(listImp c),
       ys' = ~(listImp c'), zs = ~(listImp r)}
       ~(mor))
  pure `(let Control.Category.Monoidal.MkMonoidal @{~(IBindVar EmptyFC cat)} {} = ~impl
         in ~(composeImp (IVar EmptyFC cat) ts))
  where
    listImp : Nat -> TTImp
    listImp Z = `(Prelude.Nil)
    listImp (S n) = `(Prelude.(::) ~obj ~(listImp n))

    composeImp : TTImp -> List TTImp -> TTImp
    composeImp cat [] =
      `(Control.Category.Core.id @{~cat}
        {a = ~obj})
    composeImp _ [t] = t
    composeImp cat (t :: ts) =
      `(Control.Category.Core.(.) @{~cat}
        {a = ~obj, b = ~obj, c = ~obj}
        ~(composeImp cat ts) ~t)

||| Enter string diagram notation (for `Monoidal`).
|||
||| This elaboration script must be specifically invoked with
||| `%runElab`. The category is inferred from the return type, but
||| the tensor product must be passed as an explicit argument.
export
string : {obj : _} -> {0 cat : Hom obj} -> (0 ten : obj -> obj -> obj) -> {0 i,a,b : obj} ->
         Monoidal cat ten i => TTImp -> Elab (cat a b)
string {obj = obj@(Wrap0 _)} _ @{impl} t = check !(stringImpl `(W0 _) !(quote impl) t)
string {obj = _} @{impl} _ t = check !(stringImpl `(_) !(quote impl) t)
