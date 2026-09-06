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

||| An endofunctor has *tensorial strength* if it is compatible with a
||| monoidal category's tensor product. Generally, `cat` is a monoidal
||| category with `ten` as its tensor produt, though this is not
||| enforced by the interface.
|||
||| Note that while all Prelude functors have strength over `Pair`,
||| this does not necessarily hold for other tensor products or in
||| other categories.
|||
||| This is the interface-style definition of a strong functor. For
||| the record-style definition, see `Control.Category.Records.StrongFunctorR`.
|||
||| Laws (when `cat` is a monoidal category):
||| * `map unitl . strongl = unitl`
||| * `map unitr . strongr = unitr`
||| * `map assoc . strongl = strongl . mapr strongl . assoc`
||| * `map assoc' . strongr = strongr . mapl strongr . assoc'`
||| * `strongr . mapl strongl = strongl . mapr strongr . assoc`
public export
interface CatFunctor cat cat f => StrongFunctor
    (0 cat : Hom obj)
    (0 ten : obj -> obj -> obj)
    (0 f : obj -> obj) | cat,ten,f where
  constructor MkStrongFunctor
  ||| The left tensor strength.
  strongl : {a,b : _} -> cat (a `ten` f b) (f $ a `ten` b)
  ||| The right tensor strength.
  strongr : {a,b : _} -> cat (f a `ten` b) (f $ a `ten` b)

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

namespace StrongFunctor
  ||| Convert a Prelude `Functor` into a strong functor over
  ||| `Morphism`.
  public export
  [MorFromFunctor] Functor f => StrongFunctor Morphism Pair f
      using CatFunctor.MorFromFunctor where
    strongl = Mor $ \(x,y) => map (x,) y
    strongr = Mor $ \(x,y) => map (,y) x

  ||| Convert a Prelude `Functor` into a strong functor over the
  ||| function category.
  public export
  [FuncFromFunctor] Functor m => StrongFunctor (~~>) Pair m
      using CatFunctor.FuncFromFunctor where
    strongl (x,y) = map (x,) y
    strongr (x,y) = map (,y) x

namespace StrongMonad
  ||| Convert a Prelude `Monad` into a strong monad over `Morphism`.
  public export
  MorFromMonad : Monad m => Bitraversable ten => StrongMonad Morphism ten m
  MorFromMonad = (MorFromMonad,
                  MkStrongFunctor @{MorFromFunctor}
                    (Mor $ bitraverse pure id)
                    (Mor $ bitraverse id pure))

  ||| Convert a Prelude `Monad` into a strong monad over the function
  ||| category.
  public export
  FuncFromMonad : Monad m => Bitraversable ten => StrongMonad (~~>) ten m
  FuncFromMonad = (FuncFromMonad,
                    MkStrongFunctor @{FuncFromFunctor}
                      (bitraverse pure id)
                      (bitraverse id pure))
