module Syntax.StringDiagram.Braided

import public Control.Category.Core
import public Control.Category.Functor
import public Control.Category.Monoidal
import public Control.Category.Braided
import public Data.Fin
import Data.Wrap0
import public Language.Reflection
import public Syntax.StringDiagram.Util

%default total
%language ElabReflection

export infix 0 -<
export prefix 0 =<

||| Expand shortened string diagram notation into a full expression.
|||
||| This takes two additional parameters: `obj`, which is a wildcard
||| expression used when passing objects as parameters, and `impl`,
||| which is the `Braided` implementation the expansion will use.
export
stringImpl : (obj,impl : TTImp) -> TTImp -> Elab TTImp
stringImpl obj impl t = do
  MkSDiagram inp steps out <- parseDiagram t
  let Just inp' = the (Maybe _) $ sequence inp
    | Nothing => fail "Strings cannot be discarded"
  mon <- genSym "mon"
  cat <- genSym "cat"
  ts <- stringImpl' [<] (IVar EmptyFC mon) inp' out steps
  pure `(let Control.Category.Braided.MkBraided @{~(IBindVar EmptyFC mon)} {} = ~impl
             Control.Category.Monoidal.MkMonoidal @{~(IBindVar EmptyFC cat)} {} = ~(IVar EmptyFC mon)
        in ~(composeImp (IVar EmptyFC cat) ts))
  where
    listImp : Nat -> TTImp
    listImp Z = `(Prelude.Nil)
    listImp (S n) = `(Prelude.(::) ~obj ~(listImp n))

    stringsToBack : SnocList TTImp -> Nat -> List Nat -> SnocList TTImp
    stringsToBack ts n [] = ts
    stringsToBack ts n (i :: is) =
      let iminus = pred (n `minus` i)
      in if isSucc iminus
          then stringsToBack
                (ts :<
                  `(Control.Category.Braided.sendToBack @{~impl}
                    {xs = ~(listImp i), x = ~obj, ys = ~(listImp iminus)}))
                n $ assert_smaller (i::is) $ map (\i' => if i' > i then pred i' else i') is
          else stringsToBack ts n is

    stringImpl' : SnocList TTImp -> TTImp ->
                  List String -> List String -> List SDiagramStep -> Elab (SnocList TTImp)
    stringImpl' ts mon strings out (step :: steps) = do
      let Just o = the (Maybe _) $ sequence step.outputs
        | Nothing => fail "Strings cannot be discarded"
      let False = any (\name => elem name strings) o
        | True => fail "Cannot shadow string name"
      let Just is = for step.inputs $ \n =>
                      finToNat <$> findIndex (== n) strings
        | Nothing => fail "Unrecognized string name"
      let rest = filter (\n => not $ elem n step.inputs) strings
      let ts' = stringsToBack [<] (length strings) is
      stringImpl' (ts ++ ts' :<
        `(Control.Category.Monoidal.applyAssoc @{~mon}
          {xs = ~(listImp $ length rest), ys = ~(listImp $ length step.inputs),
           ys' = ~(listImp $ length o), zs = Prelude.Nil} ~(step.mor)))
        mon (rest ++ o) out steps
    stringImpl' ts _ strings out [] = do
      let Just is = for out $ \n =>
                      finToNat <$> findIndex (== n) strings
        | Nothing => fail "Unrecognized string name"
      when (length strings /= length out) $ fail "Return strings violate linearity"
      let ts' = stringsToBack [<] (length strings) is
      pure $ ts ++ ts'

    composeImp : TTImp -> SnocList TTImp -> TTImp
    composeImp cat [<] = `(Control.Category.Core.id {a = ~obj})
    composeImp cat [<t] = t
    composeImp cat (ts :< t) =
      `(Control.Category.Core.(.) @{~cat}
        {a = ~obj, b = ~obj, c = ~obj}
        ~t ~(composeImp cat ts))

||| Enter string diagram notation (for `Braided`).
|||
||| This elaboration script must be specifically invoked with
||| `%runElab`. The category is inferred from the return type, but
||| the tensor product must be passed as an explicit argument.
|||
||| NOTE: This notation is intended for use with symmetric monoidal
||| categories, and may be confusing if used in the non-symmetric
||| braided case. If your category is non-symmetric, it may be better
||| to use the string diagram notation for `Monoidal` and insert
||| explicit braiding calls.
export
string : {obj : _} -> {0 cat : Hom obj} -> (0 ten : obj -> obj -> obj) -> {0 i,a,b : obj} ->
         Braided cat ten i => TTImp -> Elab (cat a b)
string {obj = obj@(Wrap0 _)} _ @{impl} t = check !(stringImpl `(W0 _) !(quote impl) t)
string {obj = _} @{impl} _ t = check !(stringImpl `(_) !(quote impl) t)
