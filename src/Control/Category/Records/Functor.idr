module Control.Category.Records.Functor

import Control.Category
import Control.Category.Records.Category

%default total
%prefix_record_projections off

||| A *functor* is a mapping between categories that preserves their
||| structure.
|||
||| See `CatFunctor` for required laws.
public export
record FunctorR (cat,cat' : CategoryR) where
  constructor MkFunctorR
  fun : cat.obj -> cat'.obj
  {auto con : CatFunctor cat.hom cat'.hom fun}

||| A type synonym for an *endofunctor*, a functor from a category to
||| itself.
public export
EndofunctorR : (cat : CategoryR) -> Type
EndofunctorR cat = FunctorR cat cat


namespace FunctorR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : FunctorR cat cat') -> FunctorR cat cat'
  (.functorR) = id

  ||| Apply the functor to a morphism in `cat`, translating it into `cat'`.
  public export %inline
  (.map) : (rec : FunctorR cat cat') -> forall a,b.
           cat.hom a b -> cat'.hom (rec.fun a) (rec.fun b)
  (.map) rec = map @{rec.con}


||| A *bifunctor* is a binary functor, i.e. a functor that maps two
||| categories to one.
|||
||| See `CatBifunctor` for required laws.
public export
record BifunctorR (catA,catB,cat' : CategoryR) where
  constructor MkBifunctorR
  fun : catA.obj -> catB.obj -> cat'.obj
  {auto con : CatBifunctor catA.hom catB.hom cat'.hom fun}

||| See `CatBinoidal`.
public export
BinoidalR : (catA,catB,cat' : CategoryR) -> Type
BinoidalR = BifunctorR

||| A type synonym for an *endo-bifunctor*, a bifunctor from a category
||| to itself.
public export
EndoBifunctorR : (cat : CategoryR) -> Type
EndoBifunctorR cat = BifunctorR cat cat cat

||| See `CatBinoidal`.
public export
EndoBinoidalR : (cat : CategoryR) -> Type
EndoBinoidalR = EndoBifunctorR

namespace BifunctorR
  ||| Apply the bifunctor to morphism in `catA` and `catB`, translating
  ||| them into a combined morphism in `cat'`.
  public export %inline
  (.bimap) : (rec : BifunctorR catA catB cat') -> forall a,a',b,b'.
             catA.hom a b -> catB.hom a' b' -> cat'.hom (rec.fun a a') (rec.fun b b')
  (.bimap) rec = bimap @{rec.con}

  ||| Apply a morphism to a bifunctor only on the left.
  public export %inline
  (.mapl) : {catB : _} -> (rec : BifunctorR catA catB cat') -> forall a,b,c.
            catA.hom a b -> cat'.hom (rec.fun a c) (rec.fun b c)
  (.mapl) rec = mapl @{rec.con} @{catB.con}

  ||| Apply a morphism to a bifunctor only on the right.
  public export %inline
  (.mapr) : {catA : _} -> (rec : BifunctorR catA catB cat') -> forall a,b,c.
            catB.hom a b -> cat'.hom (rec.fun c a) (rec.fun c b)
  (.mapr) rec = mapr @{rec.con} @{catA.con}

  -- Functor Projections

  ||| Convert a bifunctor (or binoidal functor) into its left functor.
  public export %inline
  (.left) : {catB : _} -> (rec : BifunctorR catA catB cat') ->
            (l : catB.obj) -> FunctorR catA cat'
  (.left) {catB=MkCategoryR {}} (MkBifunctorR {} {fun,con}) l =
    MkFunctorR (`fun` l) {con = Left @{con}}

  ||| Convert a bifunctor (or binoidal functor) into its right functor.
  public export %inline
  (.right) : {catA : _} -> (rec : BifunctorR catA catB cat') ->
             (l : catA.obj) -> FunctorR catB cat'
  (.right) {catA=MkCategoryR {}} (MkBifunctorR {} {fun,con}) l =
    MkFunctorR (l `fun`) {con = Right @{con}}
