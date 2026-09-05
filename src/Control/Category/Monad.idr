module Control.Category.Monad

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
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

||| A monad has *tensorial strength* if it is compatible with a
||| monoidal category's tensor product. Generally, `cat` is a monoidal
||| category with `ten` as its tensor produt, though this is not
||| enforced by the interface.
|||
||| Note that while all Prelude monads have strength over `Pair`, this
||| does not necessarily hold for other tensor products or in other
||| categories.
|||
||| This is the interface-style definition of a strong monad. For
||| the record-style definition, see `Control.Category.Records.StrongMonadR`.
|||
||| Laws (when `cat` is a monoidal category):
||| * `map unitl . strongl = unitl`
||| * `map unitr . strongr = unitr`
||| * `strongl . mapr unit = unit`
||| * `strongr . mapl unit = unit`
||| * `map assoc . strongl = strongl . mapr strongl . assoc`
||| * `map assoc' . strongr = strongr . mapl strongr . assoc'`
||| * `join . map strongl . strongl = strongl . mapr join`
||| * `join . map strongr . strongr = strongr . mapl join`
||| * `strongr . mapl strongl = strongl . mapr strongr . assoc`
public export
interface CatMonad cat m => StrongMonad
    (0 cat : Hom obj)
    (0 ten : obj -> obj -> obj)
    (0 m : obj -> obj) | cat,ten,m where
  constructor MkStrongMonad
  ||| The left tensor strength.
  strongl : {a,b : _} -> cat (a `ten` m b) (m $ a `ten` b)
  ||| The right tensor strength.
  strongr : {a,b : _} -> cat (m a `ten` b) (m $ a `ten` b)


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

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
  [MorFromMonad] Monad m => Bitraversable ten => StrongMonad Morphism ten m
      using CatMonad.MorFromMonad where
    strongl = Mor $ bitraverse pure id
    strongr = Mor $ bitraverse id pure

  ||| Convert a Prelude `Monad` into a strong monad over the function
  ||| category.
  public export
  [FuncFromMonad] Monad m => Bitraversable ten => StrongMonad (~~>) ten m
      using CatMonad.FuncFromMonad where
    strongl = bitraverse pure id
    strongr = bitraverse id pure
