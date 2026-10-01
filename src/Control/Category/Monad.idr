module Control.Category.Monad

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Control.Category.MonFunctor
import Data.Morphisms

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *monad* `m` is a monoid object in the category of endofunctors 
||| in `cat`, where the tensor product is given by composition.
||| Generally, `cat` is a category, though this is not enforced by the
||| interface.
|||
||| This is the interface-style definition of a monad. For the
||| record-style definition, see `Control.Category.Records.MonadR`.
|||
||| Laws (when `cat` is a category):
||| * `join . unit = id`
||| * `join . map unit = id`
||| * `join . join = join . map join`
public export
interface CatFunctor cat cat m => CatMonad
    (0 cat : Hom obj)
    (0 m : obj -> obj) | cat,m where
  constructor MkCatMonad
  ||| The join transformation of the monad.
  join : {a : _} -> cat (m (m a)) (m a)
  ||| The unit transformation of the monad.
  unit : {a : _} -> cat a (m a)

||| A strong monad is a monad that is also a strong functor, with
||| additional compatibility laws.
|||
||| Laws:
||| * `strongl . mapr unit = unit`
||| * `strongr . mapl unit = unit`
||| * `join . map strongl . strongl = strongl . mapr join`
||| * `join . map strongr . strongr = strongr . mapl join`
public export
StrongMonad : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (m : obj -> obj) -> Type
StrongMonad cat ten m = (CatMonad cat m, StrongFunctor cat ten m)


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace CatMonad
  public export
  [Id] Category cat => CatMonad cat Prelude.id
      using CatFunctor.Id where
    join = id
    unit = id

namespace StrongMonad
  public export
  Id : {ten : _} -> Category cat => StrongMonad cat ten Prelude.id
  Id = (Id, Id)


-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

namespace CatMonad
  ||| Convert a Prelude `Monad` into a `CatMonad` over `Morphism`.
  public export
  [MorFromMonad] Monad m => CatMonad Morphism m
      using CatFunctor.MorFromFunctor where
    join = Mor join
    unit = Mor pure

  ||| Convert a Prelude `Monad` into a `CatMonad` over the function
  ||| category.
  public export
  [FuncFromMonad] Monad m => CatMonad (~~>) m
      using CatFunctor.FuncFromFunctor where
    join = Prelude.join
    unit = Prelude.pure

namespace StrongMonad
  ||| Convert a Prelude `Monad` into a strong monad over `Morphism`.
  public export
  MorFromMonad : Monad m => Bitraversable ten => StrongMonad Morphism ten m
  MorFromMonad = (MorFromMonad, MorFromApplicative)

  ||| Convert a Prelude `Monad` into a strong monad over the function
  ||| category.
  public export
  FuncFromMonad : Monad m => Bitraversable ten => StrongMonad (~~>) ten m
  FuncFromMonad = (FuncFromMonad, FuncFromApplicative)
