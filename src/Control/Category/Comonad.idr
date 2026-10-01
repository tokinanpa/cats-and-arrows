module Control.Category.Comonad

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Control.Category.MonFunctor
import Data.Morphisms

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *comonad* `w` is a comonoid object in the category of
||| endofunctors in `cat`, where the tensor product is given by
||| composition. Generally, `cat` is a category, though this is not
||| enforced by the interface.
|||
||| This is the interface-style definition of a comonad. For the
||| record-style definition, see `Control.Category.Records.ComonadR`.
|||
||| Laws (when `cat` is a category):
||| * `counit . cojoin = id`
||| * `map counit . cojoin = id`
||| * `cojoin . cojoin = map cojoin . cojoin`
public export
interface CatFunctor cat cat w => CatComonad
    (0 cat : Hom obj)
    (0 w : obj -> obj) | cat,w where
  constructor MkCatComonad
  ||| The cojoin transformation of the comonad.
  cojoin : {a : _} -> cat (w a) (w (w a))
  ||| The counit transformation of the comonad.
  counit : {a : _} -> cat (w a) a

||| A strong comonad is a comonad that is also a costrong functor,
||| with additional compatibility laws.
|||
||| Laws:
||| * `mapr counit . costrongl = counit`
||| * `mapl counit . costrongr = counit`
||| * `costrongl . map costrongl . cojoin = mapr cojoin . costrongl`
||| * `costrongr . map costrongr . cojoin = mapl cojoin . costrongr`
public export
StrongComonad : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (w : obj -> obj) -> Type
StrongComonad cat ten w = (CatComonad cat w, CostrongFunctor cat ten w)


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace CatComonad
  public export
  [Id] Category cat => CatComonad cat Prelude.id
      using CatFunctor.Id where
    cojoin = id
    counit = id

namespace StrongComonad
  public export
  Id : {ten : _} -> Category cat => StrongComonad cat ten Prelude.id
  Id = (Id, Id)
