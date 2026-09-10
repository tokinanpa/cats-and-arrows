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
checkDiagram (MkSDiagram inp steps out) = checkDiagram' inp steps
  where
    checkDiagram' : List (Maybe CatString) -> List SDiagramStep -> Elab MonDiagram
    checkDiagram' strings (MkSDStep i m o :: steps) =
      case findSublist (map Just i) strings of
        Nothing => fail "Strings are not contiguous"
        Just (l,r) => do
          diag <- checkDiagram' (l ++ o ++ r) steps
          pure $ MkMDStep (length l) (length i) (length o) (length r) m :: diag
    checkDiagram' strings [] =
      if strings == map Just out
      then pure []
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
  ts <- for diag $ \(MkMDStep l c c' r mor) => do
    pure `(
      Control.Category.Monoidal.applyAssoc
      @{~impl}
      {xs = ~(listImp l), ys = ~(listImp c),
       ys' = ~(listImp c'), zs = ~(listImp r)}
       ~(mor))
  i <- genSym "impl"
  pure $ composeImp i ts
  where
    listImp : Nat -> TTImp
    listImp Z = `(Prelude.Nil)
    listImp (S n) = `(Prelude.(::) ~obj ~(listImp n))

    composeImp : Name -> List TTImp -> TTImp
    composeImp i [] =
      `(Control.Category.Core.id
        @{let Control.Category.Monoidal.MkMonoidal @{~(IBindVar EmptyFC i)} {} = ~impl
          in ~(IVar EmptyFC i)}
        {a = ~obj})
    composeImp i [t] = t
    composeImp i (t :: ts) =
      `(Control.Category.Core.(.)
        {a = ~obj, b = ~obj, c = ~obj}
        @{let Control.Category.Monoidal.MkMonoidal @{~(IBindVar EmptyFC i)} {} = ~impl
        in ~(IVar EmptyFC i)}
        ~(composeImp i ts) ~t)

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
