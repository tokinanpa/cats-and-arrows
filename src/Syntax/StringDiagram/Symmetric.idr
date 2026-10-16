module Syntax.StringDiagram.Symmetric

import public Control.Category.Core
import public Control.Category.Functor
import public Control.Category.Monoidal
import public Control.Category.Braided
import public Data.Vect
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
  brd <- genSym "brd"
  mon <- genSym "mon"
  cat <- genSym "cat"
  ts <- stringImpl' [<] (IVar EmptyFC mon) inp' out steps
  pure `(let Control.Category.Braided.MkMonSymmetric @{~(IBindVar EmptyFC brd)} {} = ~impl
             Control.Category.Braided.MkBraided @{~(IBindVar EmptyFC mon)} {} = ~(IVar EmptyFC brd)
             Control.Category.Monoidal.MkMonoidal @{~(IBindVar EmptyFC cat)} {} = ~(IVar EmptyFC mon)
        in ~(composeImp (IVar EmptyFC cat) ts))
  where
    listImp : Nat -> TTImp
    listImp Z = `(Prelude.Nil)
    listImp (S n) = `(Prelude.(::) ~obj ~(listImp n))

    permutation : List Integer -> TTImp
    permutation [] = `(Data.Permutation.Nil)
    permutation (x :: xs) =
      `(Data.Permutation.(::) (Data.Fin.fromInteger ~(IPrimVal EmptyFC (BI x))) ~(permutation xs))

    stringsToBack : Eq a => SnocList Integer -> Integer -> List a -> List a -> TTImp
    stringsToBack xs _ _ [] = permutation (xs <>> [])
    stringsToBack xs r inp (str :: strings) =
      case findIndex (==str) inp of
        Just i => stringsToBack (xs :< r + finToInteger i) r (filter (/=str) inp) strings
        Nothing => stringsToBack (xs :< 0) (r - 1) inp strings


    stringImpl' : SnocList TTImp -> TTImp ->
                  List String -> List String -> List SDiagramStep -> Elab (SnocList TTImp)
    stringImpl' ts mon strings out (step :: steps) = do
      let Just o = the (Maybe _) $ sequence step.outputs
        | Nothing => fail "Strings cannot be discarded"
      let rest = filter (\n => not $ elem n step.inputs) strings
      let False = any (`elem` rest) o
        | True => fail "Cannot shadow string name"
      let perm = stringsToBack [<] (natToInteger $ length rest) step.inputs strings
      stringImpl' (ts :<
        `(Control.Category.Braided.permute @{~impl} {xs = ~(listImp $ length strings)} ~perm) :<
        `(Control.Category.Monoidal.applyAssoc @{~mon}
          {xs = ~(listImp $ length rest), ys = ~(listImp $ length step.inputs),
           ys' = ~(listImp $ length o), zs = Prelude.Nil} ~(step.mor)))
        mon (rest ++ o) out steps
    stringImpl' ts _ strings out [] = do
      perm <- do
        let Just is = for out $ \n =>
                      findIndex (== n) strings
          | Nothing => fail "Unrecognized string name"
        let Just p = fromPermSeq =<< toVect (length strings) is
          | Nothing => fail "Return strings violate linearity"
        pure $ permutation $ natToInteger <$> toList p
      pure $ ts :< `(Control.Category.Braided.permute @{~impl}
                      {xs = ~(listImp $ length strings)} ~perm)

    composeImp : TTImp -> SnocList TTImp -> TTImp
    composeImp cat [<] = `(Control.Category.Core.id {a = ~obj})
    composeImp cat [<t] = t
    composeImp cat (ts :< t) =
      `(Control.Category.Core.(.) @{~cat}
        {a = ~obj, b = ~obj, c = ~obj}
        ~t ~(composeImp cat ts))

||| Enter string diagram notation (for `MonSymmetric`).
|||
||| This elaboration script must be specifically invoked with
||| `%runElab`. The category is inferred from the return type, but
||| the tensor product must be passed as an explicit argument.
export
string : {obj : _} -> {0 cat : Hom obj} -> (0 ten : obj -> obj -> obj) -> {0 i,a,b : obj} ->
         MonSymmetric cat ten i => TTImp -> Elab (cat a b)
string {obj = obj@(Wrap0 _)} _ @{impl} t = check !(stringImpl `(W0 _) !(quote impl) t)
string {obj = _} @{impl} _ t = check !(stringImpl `(_) !(quote impl) t)
