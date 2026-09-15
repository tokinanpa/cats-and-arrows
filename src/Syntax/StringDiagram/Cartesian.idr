module Syntax.StringDiagram.Cartesian

import public Control.Category.Core
import public Control.Category.Functor
import public Control.Category.Monoidal
import public Control.Category.Cartesian
import public Data.Fin
import Data.Wrap0
import public Language.Reflection
import public Syntax.StringDiagram.Util

%default total
%language ElabReflection

export infix 0 -<
export prefix 0 =<

usedInDiagram : List SDiagramStep -> List String -> String -> Bool
usedInDiagram [] out n = elem n out
usedInDiagram (step :: steps) out n =
  elem n step.inputs ||
    (not (elem (Just n) step.outputs) && usedInDiagram steps out n)

||| Expand shortened string diagram notation into a full expression.
|||
||| This takes two additional parameters: `obj`, which is a wildcard
||| expression used when passing objects as parameters, and `impl`,
||| which is the `Cartesian` implementation the expansion will use.
export
stringImpl : (obj,impl : TTImp) -> TTImp -> Elab TTImp
stringImpl obj impl t = do
  MkSDiagram inp steps out <- parseDiagram t
  mon <- genSym "mon"
  cat <- genSym "cat"
  ts <- stringImpl' [<] (IVar EmptyFC mon) inp out steps
  pure `(let Control.Category.Cartesian.MkCartesian @{~(IBindVar EmptyFC mon)} {} = ~impl
             Control.Category.Monoidal.MkMonoidal @{~(IBindVar EmptyFC cat)} {} = ~(IVar EmptyFC mon)
        in ~(composeImp (IVar EmptyFC cat) ts))
  where
    listImp : Nat -> TTImp
    listImp Z = `(Prelude.Nil)
    listImp (S n) = `(Prelude.(::) ~obj ~(listImp n))

    toFinList : List Integer -> TTImp
    toFinList [] = `(Prelude.Nil)
    toFinList (n :: ns) =
      `(Prelude.(::) (Data.Fin.fromInteger ~(IPrimVal EmptyFC (BI n))) ~(toFinList ns))

    stringImpl' : SnocList TTImp -> TTImp ->
                  List (Maybe String) -> List String -> List SDiagramStep -> Elab (SnocList TTImp)
    stringImpl' ts mon strings out (step :: steps) = do
      let (us, used) = unzip $
                        filter (usedInDiagram steps out . snd) $
                        mapMaybe (\(i,n) => (i,) <$> n) $
                        zip [0..natToInteger (length strings) - 1] strings
      let Just is = for step.inputs $ \n =>
                      finToInteger <$> findIndex (== Just n) strings
        | Nothing => fail "Unrecognized string name"
      let sw = toFinList (us ++ is)
      stringImpl'
        (ts :<
        `(Control.Category.Cartesian.swizzle @{~impl}
        {xs = ~(listImp $ length strings)} ~sw) :<
        `(Control.Category.Monoidal.applyAssoc @{~mon}
          {xs = ~(listImp $ length us), ys = ~(listImp $ length step.inputs),
           ys' = ~(listImp $ length step.outputs), zs = Prelude.Nil} ~(step.mor)))
        mon
        (map Just used ++ step.outputs)
        out steps
    stringImpl' ts _ strings out [] = do
      let Just is = for out $ \n =>
                      finToInteger <$> findIndex (== Just n) strings
        | Nothing => fail "Unrecognized string name"
      let sw = toFinList is
      pure (ts :<
        `(Control.Category.Cartesian.swizzle @{~impl}
          {xs = ~(listImp $ length strings)} ~sw))
      
    composeImp : TTImp -> SnocList TTImp -> TTImp
    composeImp cat [<] = `(Control.Category.Core.id {a = ~obj})
    composeImp cat [<t] = t
    composeImp cat (ts :< t) =
      `(Control.Category.Core.(.) @{~cat}
        {a = ~obj, b = ~obj, c = ~obj}
        ~t ~(composeImp cat ts))

||| Enter string diagram notation (for `Cartesian`).
|||
||| This elaboration script must be specifically invoked with
||| `%runElab`. The category is inferred from the return type, but
||| the tensor product must be passed as an explicit argument.
export
string : {obj : _} -> {0 cat : Hom obj} -> (0 ten : obj -> obj -> obj) -> {0 i,a,b : obj} ->
         Cartesian cat ten i => TTImp -> Elab (cat a b)
string {obj = obj@(Wrap0 _)} _ @{impl} t = check !(stringImpl `(W0 _) !(quote impl) t)
string {obj = _} @{impl} _ t = check !(stringImpl `(_) !(quote impl) t)

