module Control.Category.Monoidal

import Control.Category.Core
import Control.Category.Functor
import Data.Morphisms
import Data.Tensor
import Data.Vect

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
    Monoidal (0 cat : Hom obj) (0 ten : obj -> obj -> obj) (0 i : obj) | cat,ten where
  constructor MkMonoidal
  ||| The left-biased associator. This must be the inverse of `assoc'`.
  assoc : forall a,b,c. cat ((a `ten` b) `ten` c) (a `ten` (b `ten` c))
  ||| The right-biased associator. This must be the inverse of `assoc`.
  assoc' : forall a,b,c. cat (a `ten` (b `ten` c)) ((a `ten` b) `ten` c)

  ||| The left unitor.
  unitl : forall a. cat (i `ten` a) a
  ||| The inverse of `unitl`, the left unitor.
  unitl' : forall a. cat a (i `ten` a)

  ||| The right unitor.
  unitr : forall a. cat (a `ten` i) a
  ||| The inverse of `unitr`, the right unitor.
  unitr' : forall a. cat a (a `ten` i)

||| A type synonym that can be used to mark a category as merely being
||| premonoidal, rather than a true monoidal category. These have the
||| same laws, but allow the tensor product to be a binoidal functor.
|||
||| See https://github.com/tokinanpa/cats-and-arrows/tree/main/docs/CategoricalSins.md
||| for more information on when/why this matters.
public export
PreMonoidal : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> Type
PreMonoidal = Monoidal


------------------------------------------------------------
-- Characterization
------------------------------------------------------------

||| A nested tensor product sequence of the objects in `objs`.
public export
Tensor : (ten : obj -> obj -> obj) -> (i : obj) -> (objs : Vect n obj) -> obj
Tensor {n=Z} _ i [] = i
Tensor {n=S _} ten _ objs@(_::_) = foldr1 ten objs

||| Split a tensor product sequence into two by reassociating.
public export
splitAssoc : Monoidal cat ten i => {m,n : _} -> {0 xs : Vect m _} -> {0 ys : Vect n _} ->
             cat (Tensor ten i (xs ++ ys)) (Tensor ten i xs `ten` Tensor ten i ys)
splitAssoc {m=Z,xs=[]} = unitl'
splitAssoc {m=S Z,n=Z,xs=_::xs',ys=[]} = rewrite invertVectZ xs' in unitr'
splitAssoc {m=S Z,n=S _,xs=_::xs',ys=_::_} = rewrite invertVectZ xs' in id
splitAssoc {m=S (S _),xs=_::xs'} =
  rewrite invertVectS xs' in assoc' . mapr' (splitAssoc {xs=head xs'::tail xs',ys})

||| Merge two tensor product sequences into one by reassociating.
public export
mergeAssoc : Monoidal cat ten i => {m,n : _} -> {0 xs : Vect m _} -> {0 ys : Vect n _} ->
             cat (Tensor ten i xs `ten` Tensor ten i ys) (Tensor ten i (xs ++ ys))
mergeAssoc {m=Z,xs=[]} = unitl
mergeAssoc {m=S Z,n=Z,xs=_::xs',ys=[]} = rewrite invertVectZ xs' in unitr
mergeAssoc {m=S Z,n=S _,xs=_::xs',ys=_::_} = rewrite invertVectZ xs' in id
mergeAssoc {m=S (S _),xs=_::xs'} =
  rewrite invertVectS xs' in mapr' (mergeAssoc {xs=head xs'::tail xs',ys}) . assoc

||| Apply a morphism to the middle of a tensor product sequence.
public export
applyAssoc : Monoidal cat ten i => {m,n,n',o : _} ->
             {0 xs : Vect m _} -> {0 ys : Vect n _} -> {0 ys' : Vect n' _} -> {0 zs : Vect o _} ->
             cat (Tensor ten i ys) (Tensor ten i ys') -> cat (Tensor ten i (xs ++ ys ++ zs)) (Tensor ten i (xs ++ ys' ++ zs))
applyAssoc f = mergeAssoc . mapr' (mergeAssoc . mapl' f . splitAssoc) . splitAssoc


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace Monoidal
  ||| Convert a `Tensor` into a monoidal structure on `Morphism`.
  public export
  [MorFromTensor] Tensor ten i => Monoidal Morphism ten i
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
  [FuncFromTensor] Tensor ten i => Monoidal (~~>) ten i
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
  [KleisliFromTensor] (Tensor ten i, Bitraversable ten, Monad m) =>
      Monoidal (Kleislimorphism m) ten i using KleisliFromBitraversable where
    assoc = Kleisli $ pure . assocr
    assoc' = Kleisli $ pure . assocl
    unitl = Kleisli $ pure . unitl.leftToRight
    unitl' = Kleisli $ pure . unitl.rightToLeft
    unitr = Kleisli $ pure . unitr.leftToRight
    unitr' = Kleisli $ pure . unitr.rightToLeft


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
