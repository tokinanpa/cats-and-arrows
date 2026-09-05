module Control.Category.Monoidal

import Control.Category.Core
import Control.Category.Functor
import Data.Morphisms
import Data.Tensor
import Data.List
import Data.Singleton

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *monoidal category* is a category equipped with a binary operator
||| on its objects called the *tensor product* that respects its
||| internal structure. This operation is required to be a monoid,
||| that is to be associative and have an identity object (up to
||| isomorphism).
|||
||| This is the interface-style definition of a monoidal category. For
||| the record-style definition, see `Control.Category.Records.MonoidalR`.
|||
||| Laws:
||| * `assoc . assoc' = assoc' . assoc = id`
||| * `unitl . unitl' = unitl' . unitl = id`
||| * `unitr . unitr' = unitr' . unitr = id`
||| * `mapr unitl . assoc = mapl unitr` (triangle identity)
||| * `assoc . assoc = mapr assoc . assoc . mapl assoc` (pentagon identity)
public export
interface (Category cat, CatEndoBifunctor cat ten) =>
    Monoidal (0 cat : Hom obj) (ten : obj -> obj -> obj) (i : obj) | cat,ten where
  constructor MkMonoidal
  ||| The left-biased associator. This must be the inverse of `assoc'`.
  assoc : {a,b,c : _} -> cat ((a `ten` b) `ten` c) (a `ten` (b `ten` c))
  ||| The right-biased associator. This must be the inverse of `assoc`.
  assoc' : {a,b,c : _} -> cat (a `ten` (b `ten` c)) ((a `ten` b) `ten` c)

  ||| The left unitor.
  unitl : {a : _} -> cat (i `ten` a) a
  ||| The inverse of `unitl`, the left unitor.
  unitl' : {a : _} -> cat a (i `ten` a)

  ||| The right unitor.
  unitr : {a : _} -> cat (a `ten` i) a
  ||| The inverse of `unitr`, the right unitor.
  unitr' : {a : _} -> cat a (a `ten` i)

||| A type synonym that can be used to mark a category as merely being
||| premonoidal, rather than a true monoidal category. These have the
||| same laws, but allow the tensor product to be a binoidal functor.
|||
||| See https://github.com/tokinanpa/cats-and-arrows/tree/main/docs/CategoricalSins.md
||| for more information on when/why this matters.
public export
PreMonoidal : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> Type
PreMonoidal = Monoidal


-- ------------------------------------------------------------
-- -- Characterization
-- ------------------------------------------------------------

||| A *tensor product sequence*, meaning a right-associated nested
||| tensor product of objects. This structure is used by string
||| diagram notation.
public export
TenSeq : (ten : obj -> obj -> obj) -> (i : obj) -> List obj -> obj
TenSeq _ i [] = i
TenSeq _ _ [x] = x
TenSeq ten i (o :: os@(_ :: _)) = o `ten` TenSeq ten i os

||| Split a tensor product sequence into two by reassociating.
public export
splitAssoc : Monoidal cat ten i => {xs,ys : _} ->
             cat (TenSeq ten i (xs ++ ys)) (TenSeq ten i xs `ten` TenSeq ten i ys)
splitAssoc @{c@(MkMonoidal {})} {xs=[]} = unitl'
splitAssoc @{c@(MkMonoidal {})} {xs=[_],ys=[]} =  unitr'
splitAssoc @{c@(MkMonoidal {})} {xs=[_],ys=_::_} = id
splitAssoc @{c@(MkMonoidal {})} {xs=[_,_],ys=_::_} = assoc'
splitAssoc @{c@(MkMonoidal {})} {xs=_::_::_} = assoc' . mapr' splitAssoc

||| Merge two tensor product sequences into one by reassociating.
public export
mergeAssoc : Monoidal cat ten i => {xs,ys : _} ->
             cat (TenSeq ten i xs `ten` TenSeq ten i ys) (TenSeq ten i (xs ++ ys))
mergeAssoc @{c@(MkMonoidal {})} {xs=[]} = unitl
mergeAssoc @{c@(MkMonoidal {})} {xs=[_],ys=[]} = unitr
mergeAssoc @{c@(MkMonoidal {})} {xs=[_],ys=_::_} = id
mergeAssoc @{c@(MkMonoidal {})} {xs=[_,_],ys=_::_} = assoc
mergeAssoc @{c@(MkMonoidal {})} {xs=_::_::_} = mapr' mergeAssoc . assoc

||| Apply a morphism to the middle of a tensor product sequence.
public export
applyAssoc : Monoidal cat ten i => {xs,ys,ys',zs : _} ->
             cat (TenSeq ten i ys) (TenSeq ten i ys') ->
             cat (TenSeq ten i (xs ++ ys ++ zs)) (TenSeq ten i (xs ++ ys' ++ zs))
applyAssoc @{c@(MkMonoidal {})} f =
  mergeAssoc . mapr' (mergeAssoc . mapl' f . splitAssoc) . splitAssoc


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

namespace Monoidal
  ||| Convert a `Tensor` into a monoidal structure on `Morphism`.
  public export
  [MorFromTensor] {ten,i : _} -> Tensor ten i => Monoidal Morphism ten i
      using CatBifunctor.MorFromBifunctor where
    assoc = Mor assocr
    assoc' = Mor assocl
    unitl = Mor unitl.leftToRight
    unitl' = Mor unitl.rightToLeft
    unitr = Mor unitr.leftToRight
    unitr' = Mor unitr.rightToLeft

  ||| Convert a `Tensor` into a monoidal structure on the function
  ||| category.
  public export
  [FuncFromTensor] {ten,i : _} -> Tensor ten i => Monoidal (~~>) ten i
      using Category.Function CatBifunctor.FuncFromBifunctor where
    assoc = Tensor.assocr
    assoc' = Tensor.assocl
    unitl = Tensor.unitl.leftToRight
    unitl' = Tensor.unitl.rightToLeft
    unitr = Tensor.unitr.leftToRight
    unitr' = Tensor.unitr.rightToLeft

  ||| Convert a `Tensor` into a monoidal structure on the Klesli
  ||| category.
  |||
  ||| WARNING: Whether this forms a proper monoidal category is
  ||| dependent on the behavior of the `Bitraversable` implementation.
  ||| In particular, this is usually a premonoidal category.
  public export
  [KleisliFromTensor] {ten,i : _} ->(Tensor ten i, Bitraversable ten, Monad m) =>
      Monoidal (Kleislimorphism m) ten i using KleisliFromBitraversable where
    assoc = Kleisli $ Prelude.pure . assocr
    assoc' = Kleisli $ Prelude.pure . assocl
    unitl = Kleisli $ Prelude.pure . unitl.leftToRight
    unitl' = Kleisli $ Prelude.pure . unitl.rightToLeft
    unitr = Kleisli $ Prelude.pure . unitr.leftToRight
    unitr' = Kleisli $ Prelude.pure . unitr.rightToLeft


  public export
  FuncPair : Monoidal (~~>) Pair ()
  FuncPair = FuncFromTensor

  public export
  FuncEither : Monoidal (~~>) Either Void
  FuncEither = FuncFromTensor


public export %hint
MonoidalMorPair : Monoidal Morphism Pair ()
MonoidalMorPair = MorFromTensor

public export %hint
MonoidalMorEither : Monoidal Morphism Either Void
MonoidalMorEither = MorFromTensor

||| WARNING: This is a premonoidal category, not truly monoidal.
public export %hint
MonoidalKleisliPair : Monad m => PreMonoidal (Kleislimorphism m) Pair ()
MonoidalKleisliPair = KleisliFromTensor

public export %hint
MonoidalKleisliEither : Monad m => Monoidal (Kleislimorphism m) Either Void
MonoidalKleisliEither = KleisliFromTensor
