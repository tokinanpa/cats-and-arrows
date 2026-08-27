module Control.Category.Functor

import Control.Category.Core
import Data.Morphisms
import Data.Fun

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *functor* is a mapping between categories that preserves their
||| structure. Generally, `cat` and `cat'` are categories, though
||| this is not enforced by the interface.
|||
||| This is the interface-style definition of a functor. For the
||| record-style definition, see `Control.Category.Records.FunctorR`.
|||
||| Laws (when `cat`, `cat'` are categories):
||| * `map id = id`
||| * `map f . map g = map (f . g)`
public export
interface CatFunctor
    (0 cat : Hom obj)
    (0 cat' : Hom obj')
    (0 f : obj -> obj') | cat,cat',f where
  constructor MkCatFunctor
  ||| Apply the functor to a morphism in `cat`, translating it into `cat'`.
  map : forall a,b. cat a b -> cat' (f a) (f b)

||| A type synonym for an *endofunctor*, a functor from a category to
||| itself.
|||
||| This is the interface-style definition of an endofunctor. For the
||| record-style definition, see `Control.Category.Records.EndofunctorR`.
public export
CatEndofunctor : (cat : Hom obj) -> (f : obj -> obj) -> Type
CatEndofunctor cat f = CatFunctor cat cat f

||| A synonym of `map` that only works for endofunctors. May help
||| typechecking and interface resolution.
public export
map' : CatEndofunctor cat f => cat a b -> cat (f a) (f b)
map' = map


||| A *bifunctor* is a binary functor, i.e. a functor that maps two
||| categories to one. Generally, `catA`, `catB` and `cat'` are
||| categories, though this is not enforced by the interface.
|||
||| This is the interface-style definition of a bifunctor. For the
||| record-style definition, see `Control.Category.Records.BifunctorR`.
|||
||| Laws (when `catA`, `catB`, `cat'` are categories):
||| * `bimap id id = id`
||| * `bimap f f' . bimap g g' = bimap (f . g) (f' . g')`
public export
interface CatBifunctor
    (0 catA : Hom objA)
    (0 catB : Hom objB)
    (0 cat' : Hom obj')
    (0 f : objA -> objB -> obj') | catA,catB,cat',f where
  constructor MkCatBifunctor
  ||| Apply the bifunctor to morphism in `catA` and `catB`, translating
  ||| them into a combined morphism in `cat'`.
  bimap : forall a,a',b,b'. catA a b -> catB a' b' -> cat' (f a a') (f b b')

||| A type synonym that can be used to mark an operator as merely being
||| a binoidal functor, rather than a proper bifunctor. These have the
||| same data, but weaker laws.
|||
||| Laws for a binoidal functor:
||| * `bimap id id = id`
||| * `bimap id f . bimap id g = bimap id (f . g)`
||| * `bimap f id . bimap g id = bimap (f . g) id`
||| * `bimap f g = bimap id g . bimap f id` (NOTE: order matters here)
public export
CatBinoidal : (catA : Hom objA) -> (catB : Hom objB) -> (cat' : Hom obj') ->
              (f : objA -> objB -> obj') -> Type
CatBinoidal = CatBifunctor

||| Apply a morphism to a bifunctor only on the left.
public export
mapl : CatBifunctor catA catB cat' f => Category catB =>
       forall a,b,c. catA a b -> cat' (f a c) (f b c)
mapl m = bimap {catA,catB,cat',f} m id

||| Apply a morphism to a bifunctor only on the right.
public export
mapr : CatBifunctor catA catB cat' f => Category catA =>
       forall a,b,c. catB a b -> cat' (f c a) (f c b)
mapr = bimap {catA,catB,cat',f} id


||| A type synonym for an *endo-bifunctor*, a bifunctor from a category
||| to itself.
|||
||| This is the interface-style definition of an endo-bifunctor. For the
||| record-style definition, see `Control.Category.Records.EndoBifunctorR`.
public export
CatEndoBifunctor : (cat : Hom obj) -> (f : obj -> obj -> obj) -> Type
CatEndoBifunctor cat f = CatBifunctor cat cat cat f

||| See `CatBinoidal`.
public export
CatEndoBinoidal : (cat : Hom obj) -> (f : obj -> obj -> obj) -> Type
CatEndoBinoidal = CatEndoBifunctor


||| A synonym of `bimap` that only works for endo-bifunctors. May help
||| typechecking and interface resolution.
public export
bimap' : CatEndoBifunctor cat f => cat a b -> cat a' b' -> cat (f a a') (f b b')
bimap' = bimap {catA=cat,catB=cat,cat'=cat}

||| A synonym of `mapl` that only works for endo-bifunctors. May help
||| typechecking and interface resolution.
public export
mapl' : CatEndoBifunctor cat f => Category cat => cat a b -> cat (f a c) (f b c)
mapl' = mapl {catA=cat,catB=cat,cat'=cat}

||| A synonym of `mapr` that only works for endo-bifunctors. May help
||| typechecking and interface resolution.
public export
mapr' : CatEndoBifunctor cat f => Category cat => cat a b -> cat (f c a) (f c b)
mapr' = mapr {catA=cat,catB=cat,cat'=cat}


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace CatFunctor
  ||| Convert an ordinary Prelude `Functor` into a `CatFunctor` over the
  ||| `Morphism` category.
  public export
  [MorFromFunctor] Functor f => CatFunctor Morphism Morphism f where
    map (Mor f) = Mor (map f)

  ||| Convert an ordinary Prelude `Functor` into a `CatFunctor` over the
  ||| function category.
  public export
  [FuncFromFunctor] Functor f => CatFunctor (~~>) (~~>) f where
    map = Prelude.map

  ||| Convert a Prelude `Traversable` into a `CatFunctor` over the
  ||| Kleisli category.
  public export
  [KleisliFromTraversable] (Traversable f, Applicative m) =>
      CatFunctor (Kleislimorphism m) (Kleislimorphism m) f where
    map (Kleisli f) = Kleisli $ traverse f

  ||| Compose two functors into a composite functor.
  public export
  [Compose] CatFunctor cat' cat'' f => CatFunctor cat cat' g =>
      CatFunctor cat cat'' (Prelude.(.) f g) where
    map = map {cat=cat',cat'=cat'',f} . map {cat,cat',f=g}

  ||| The identity functor on a category.
  public export
  [Id] CatFunctor cat cat Prelude.id where
    map = id

  ||| The constant functor on a category. It maps all morphisms to the
  ||| identity morphism.
  public export
  [Const] Category cat' => CatFunctor cat cat' (const x) where
    map _ = id

namespace CatBifunctor
  ||| Convert an ordinary Prelude `Bifunctor` into a `CatBifunctor` over
  ||| the `Morphism` category.
  public export
  [MorFromBifunctor] Bifunctor f => CatBifunctor Morphism Morphism Morphism f where
    bimap (Mor f) (Mor g) = Mor (bimap f g)

  ||| Convert an ordinary Prelude `Bifunctor` into a `CatBifunctor` over
  ||| the function category.
  public export
  [FuncFromBifunctor] Bifunctor f => CatBifunctor (~~>) (~~>) (~~>) f where
    bimap = Prelude.bimap

  ||| Convert a Prelude `Bitraversable` into a `CatBifunctor` over the
  ||| Kleisli category.
  |||
  ||| WARNING: Whether this implementation satisfies the bifunctor laws
  ||| is dependent on the behavior of the `Bitraversable` implementation.
  ||| In particular, this is usually a binoidal functor, rather than a
  ||| true bifunctor.
  public export
  [KleisliFromBitraversable] (Applicative m, Bitraversable f) =>
      CatBifunctor (Kleislimorphism m)
                   (Kleislimorphism m)
                   (Kleislimorphism m) f where
    bimap (Kleisli f) (Kleisli g) = Kleisli $ bitraverse f g

  ||| Convert a bifunctor (or binoidal functor) into its left functor.
  public export
  [Left] {0 r : _} -> CatBifunctor catA catB cat' f => Category catB =>
      CatFunctor catA cat' (`f` r) where
    map = mapl {catA,catB,cat'}

  ||| Convert a bifunctor (or binoidal functor) into its right functor.
  public export
  [Right] {0 l : _} -> CatBifunctor catA catB cat' f => Category catA =>
      CatFunctor catB cat' (l `f`) where
    map = mapr {catA,catB,cat'}

  ||| Compose a functor with a bifunctor to form a composite bifunctor.
  public export
  [Compose] CatFunctor cat' cat'' f => CatBifunctor catA catB cat' g =>
      CatBifunctor catA catB cat'' (f .: g) where
    bimap = map {cat=cat',cat'=cat'',f} .: bimap {catA,catB,cat',f=g}


public export %hint
CatBifunctorMorPair : CatEndoBifunctor Morphism Pair
CatBifunctorMorPair = MorFromBifunctor

public export %hint
CatBifunctorMorEither : CatEndoBifunctor Morphism Either
CatBifunctorMorEither = MorFromBifunctor

||| WARNING: This is a binoidal functor, not a true bifunctor.
public export %hint
CatBifunctorKleisliPair : Applicative m => CatEndoBinoidal (Kleislimorphism m) Pair
CatBifunctorKleisliPair = KleisliFromBitraversable

public export %hint
CatBifunctorKleisliEither : Applicative m => CatEndoBifunctor (Kleislimorphism m) Either
CatBifunctorKleisliEither = KleisliFromBitraversable

