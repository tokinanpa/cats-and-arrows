module Control.Category.MonFunctor

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Data.Morphisms

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A lax monoidal functor from `cat` to `cat'`.
|||
||| This is the interface-style definition of a lax monoidal functor.
||| For the record-style definition, see `Control.Category.Records.LaxMonFunctorR`.
|||
||| Laws:
||| * `map assoc . mjoin . mapl mjoin = mjoin . mapr mjoin . assoc`
||| * `map unitl . mjoin . mapl munit = unitl`
||| * `map unitr . mjoin . mapr munit = unitr`
public export
interface CatFunctor cat cat' f => LaxMonFunctor
    (0 cat : Hom obj) (0 ten : obj -> obj -> obj) (0 i : obj)
    (0 cat' : Hom obj') (0 ten' : obj' -> obj' -> obj') (0 i' : obj')
    (0 f : obj -> obj') | cat,ten,cat',ten',f where
  constructor MkLaxMonFunctor
  ||| The lax monoidal functor action on the tensor product.
  mjoin : {a,b : _} -> cat' (f a `ten'` f b) (f (a `ten` b))
  ||| The lax monoidal functor action on the unit object.
  munit : cat' i' (f i)

||| A type synonym for a lax monoidal endofunctor, a lax monoidal
||| functor from a monoidal category to itself.
|||
||| This is the interface-style definition of a lax monoidal
||| endofunctor. For the record-style definition, see
||| `Control.Category.Records.LaxMonEndofunctorR`.
public export %inline
LaxMonEndofunctor : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> (f : obj -> obj) -> Type
LaxMonEndofunctor cat ten i = LaxMonFunctor cat ten i cat ten i


||| A (strong) monoidal functor from `cat` to `cat'`.
|||
||| This is the interface-style definition of a monoidal functor. For
||| the record-style definition, see `Control.Category.Records.MonFunctorR`.
|||
||| Laws:
||| * `munit . munit' = munit' . munit = id`
||| * `mjoin . mjoin' = mjoin' . mjoin = id`
public export
interface LaxMonFunctor cat ten i cat' ten' i' f => MonFunctor
    (0 cat : Hom obj) (0 ten : obj -> obj -> obj) (0 i : obj)
    (0 cat' : Hom obj') (0 ten' : obj' -> obj' -> obj') (0 i' : obj')
    (0 f : obj -> obj') | cat,ten,cat',ten',f where
  constructor MkMonFunctor
  ||| The inverse monoidal functor action on the tensor product.
  |||
  ||| This is the inverse of `mjoin`.
  mjoin' : {a,b : _} -> cat' (f (a `ten` b)) (f a `ten'` f b)
  ||| The inverse monoidal functor action on the unit object.
  |||
  ||| This is the inverse of `munit`.
  munit' : cat' (f i) i'

||| A type synonym for a monoidal endofunctor, a monoidal functor from
||| a monoidal category to itself.
|||
||| This is the interface-style definition of a monoidal endofunctor.
||| For the record-style definition, see `Control.Category.Records.MonEndofunctorR`.
public export %inline
MonEndofunctor : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> (f : obj -> obj) -> Type
MonEndofunctor cat ten i = MonFunctor cat ten i cat ten i

||| An endofunctor has *tensorial strength* if it is compatible with a
||| monoidal category's tensor product. Generally, `cat` is a monoidal
||| category with `ten` as its tensor product, though this is not
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

||| An endofunctor has *tensorial costrength* if it is compatible with
||| a monoidal category's tensor product in a way that is dual to a
||| tensorial strength. Generally, `cat` is a monoidal category with
||| `ten` as its tensor product, though this is not enforced by the
||| interface.
|||
||| This is the interface-style definition of a costrong functor. For
||| the record-style definition, see `Control.Category.Records.CostrongFunctorR`.
|||
||| Laws (when `cat` is a monoidal category):
||| * `unitl . costrongl = map unitl`
||| * `unitr . costrongr = map unitr`
||| * `costrongl . map assoc' = assoc' . mapr costrongl . costrongl`
||| * `costrongr . map assoc' = assoc' . mapl costrongr . costrongr`
||| * `mapl costrongl . cstrongr = assoc' . mapr costrongr . costrongl`
public export
interface CatFunctor cat cat f => CostrongFunctor
    (0 cat : Hom obj)
    (0 ten : obj -> obj -> obj)
    (0 f : obj -> obj) | cat,ten,f where
  constructor MkCostrongFunctor
  ||| The left tensor costrength.
  costrongl : {a,b : _} -> cat (f $ a `ten` b) (a `ten` f b)
  ||| The right tensor costrength.
  costrongr : {a,b : _} -> cat (f $ a `ten` b) (f a `ten` b)


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace LaxMonFunctor
  public export
  [Id] {ten,i : _} -> Category cat => LaxMonFunctor cat ten i cat ten i Prelude.id
      using CatFunctor.Id where
    mjoin = id
    munit = id

namespace MonFunctor
  public export
  [Id] {ten,i : _} -> Category cat => MonFunctor cat ten i cat ten i Prelude.id
      using LaxMonFunctor.Id where
    mjoin' = id
    munit' = id

namespace StrongFunctor
  public export
  [Id] {ten : _} -> Category cat => StrongFunctor cat ten Prelude.id
      using CatFunctor.Id where
    strongl = id
    strongr = id

namespace CostrongFunctor
  public export
  [Id] {ten : _} -> Category cat => CostrongFunctor cat ten Prelude.id
      using CatFunctor.Id where
    costrongl = id
    costrongr = id


-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

namespace LaxMonFunctor
  ||| Convert a Prelude `Applicative` into a lax monoidal endofunctor
  ||| over `Morphism`.
  public export
  [MorFromApplicative] Applicative f => LaxMonFunctor Morphism Pair () Morphism Pair () f
      using CatFunctor.MorFromFunctor where
    mjoin = Mor $ \(x,y) => (,) <$> x <*> y
    munit = Mor $ const $ pure ()

  ||| Convert a Prelude `Applicative` into a lax monoidal endofunctor
  ||| over the function category.
  public export
  [FuncFromApplicative] Applicative f => LaxMonFunctor (~~>) Pair () (~~>) Pair () f
      using CatFunctor.FuncFromFunctor where
    mjoin (x,y) = (,) <$> x <*> y
    munit = const $ pure ()

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

  ||| Convert a Prelude `Applicative` into a strong functor over
  ||| `Morphism`.
  public export
  [MorFromApplicative] Applicative f => Bitraversable ten => StrongFunctor Morphism ten f
      using CatFunctor.MorFromFunctor where
    strongl = Mor $ bitraverse pure id
    strongr = Mor $ bitraverse id pure

  ||| Convert a Prelude `Applicative` into a strong functor over the
  ||| function category.
  public export
  [FuncFromApplicative] Applicative f => Bitraversable ten => StrongFunctor (~~>) ten f
      using CatFunctor.FuncFromFunctor where
    strongl = bitraverse pure id
    strongr = bitraverse id pure
