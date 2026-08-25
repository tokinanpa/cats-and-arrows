module Control.Category.Closed

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Control.Category.Cartesian
import Data.Morphisms

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A monoidal category is *closed* if it can meaningfully represent
||| its morphisms as an object inside of itself. More specifically,
||| the internal hom ``(a `hom` b)`` is an object that encodes the
||| set of morphisms from `a` to `b`.
|||
||| Formally, a monoidal category is closed if the functor
||| ``(`ten` a)`` has a right adjoint functor `hom a`.
|||
||| This is the interface-style definition of a closed monoidal category.
||| For the record-style definition, see `Control.Category.Records.ClosedR`.
|||
||| Laws:
||| * `curry` is natural in `a`,`b`,`c` (see `NatTrans`)
||| * `uncurry` is natural in `a`,`b`,`c` (see `NatTrans`)
public export
interface Monoidal cat ten i =>
    Closed (0 cat : Hom obj) (0 ten,hom : obj -> obj -> obj) (0 i : obj) | cat where
  constructor MkClosed
  ||| The currying transformation.
  curry : forall a,b,c. cat (a `ten` b) c -> cat a (b `hom` c)
  ||| The uncurrying transformation.
  uncurry : forall a,b,c. cat a (b `hom` c) -> cat (a `ten` b) c

||| A monoidal category that is both cartesian and closed.
|||
||| This is the interface-style definition of a cartesian closed
||| monoidal category. For the record-style definition, see
||| `Control.Category.Records.CartesianClosedR`.
public export
CartesianClosed : (cat : Hom obj) -> (ten,hom : obj -> obj -> obj) -> (i : obj) -> Type
CartesianClosed cat ten hom i = (Cartesian cat ten i, Closed cat ten hom i)


------------------------------------------------------------
-- Functions
------------------------------------------------------------

||| The evaluation map of a closed monoidal category.
public export
eval : Closed cat ten hom i => cat ((a `hom` b) `ten` a) b
eval = uncurry id

||| The coevaluation map of a closed monoidal category.
public export
coeval : Closed cat ten hom i => cat a (b `hom` (a `ten` b))
coeval = curry id


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

public export
Closed Morphism Pair Morphism () where
  curry (Mor f) = Mor $ Mor . curry f
  uncurry (Mor f) = Mor $ uncurry $ applyMor . f

public export
Closed Morphism Pair (~~>) () where
  curry = Mor . curry . applyMor
  uncurry = Mor . uncurry . applyMor

namespace Closed
  public export
  [Function] Closed (~~>) Pair (~~>) ()
      using Monoidal.FuncPair where
    curry = Prelude.curry
    uncurry = Prelude.uncurry
