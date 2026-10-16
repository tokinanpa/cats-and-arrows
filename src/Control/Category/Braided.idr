module Control.Category.Braided

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Data.Morphisms
import public Data.Permutation
import Data.Tensor
import Data.List
import Data.List.Quantifiers
import Data.Vect

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

public export
permuteDefault : Monoidal cat ten i => ({a,b : _} -> cat (a `ten` b) (b `ten` a)) ->
                  {xs : _} -> (p : Permutation (length xs)) -> cat (TenSeq ten i xs) (TenSeq ten i $ permuteList xs p)

||| A monoidal category is *braided* when it is possible to flip the
||| order of the tensor product in a coherent way, determined by the
||| braiding isomorphism.
|||
||| This is the interface-style definition of a braided monoidal category.
||| For the record-style definition, see `Control.Category.Records.BraidedR`.
|||
||| Laws:
||| * `braid . braid' = braid' . braid = id`
||| * `assoc . braid . assoc = mapr braid . assoc . mapl braid`
||| * `assoc' . braid . assoc' = mapl braid . assoc' . mapr braid`
|||
||| Additionally, a braided monoidal category may be *symmetric*,
||| requiring that `braid = braid'`. Since the only difference is in
||| laws, the same interface is used for this case.
public export
interface Monoidal cat ten i =>
    Braided (0 cat : Hom obj) (ten : obj -> obj -> obj) (i : obj) | cat,ten where
  constructor MkBraided
  ||| The braiding of the category.
  braid : {a,b : _} -> cat (a `ten` b) (b `ten` a)

  ||| The inverse of `braid`, the braiding of the category.
  |||
  ||| The default definition sets this equal to `braid`, making the
  ||| assumption that this braiding is symmetric. If it isn't, then
  ||| both methods must be defined.
  braid' : {a,b : _} -> cat (b `ten` a) (a `ten` b)
  braid' = braid

  permute : {xs : _} -> (p : Permutation (length xs)) ->
            cat (TenSeq ten i xs) (TenSeq ten i $ permuteList xs p)
  permute = permuteDefault (braid {ten})

||| See `PreMonoidal`.
public export
PreBraided : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> Type
PreBraided = Braided


------------------------------------------------------------
-- Characterization
------------------------------------------------------------

||| Swap two halves of a tensor product sequence using the braiding.
public export
swapAssoc : Braided cat ten i => {xs,ys : _} ->
             cat (TenSeq ten i (xs ++ ys)) (TenSeq ten i (ys ++ xs))
swapAssoc @{c@(MkBraided{})} = mergeAssoc . braid . splitAssoc

||| Swap two halves of a tensor product sequence using the braiding.
|||
||| This uses `braid'` instead of `braid`. For symmetric monoidal
||| categories, this is identical to `swapAssoc`.
public export
swapAssoc' : Braided cat ten i => {xs,ys : _} ->
             cat (TenSeq ten i (xs ++ ys)) (TenSeq ten i (ys ++ xs))
swapAssoc' @{c@(MkBraided{})} = mergeAssoc . braid' . splitAssoc

||| Bring a single object of a tensor product sequence to the front.
public export
bringToFront : Braided cat ten i => {xs,x,ys : _} ->
               cat (TenSeq ten i (xs ++ x :: ys)) (TenSeq ten i (x :: xs ++ ys))
bringToFront @{c@(MkBraided{})} {ys=[]} =
  rewrite appendNilRightNeutral xs in mergeAssoc . braid . splitAssoc
bringToFront @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc {xs=x::xs} .  mapl' (mergeAssoc {xs=[x]} . braid) . assoc' . splitAssoc

||| Bring a single object of a tensor product sequence to the front.
|||
||| This uses `braid'` instead of `braid`. For symmetric monoidal
||| categories, this is identical to `bringToFront`.
public export
bringToFront' : Braided cat ten i => {xs,x,ys : _} ->
               cat (TenSeq ten i (xs ++ x :: ys)) (TenSeq ten i (x :: xs ++ ys))
bringToFront' @{c@(MkBraided{})} {ys=[]} =
  rewrite appendNilRightNeutral xs in mergeAssoc . braid' . splitAssoc
bringToFront' @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc {xs=x::xs} .  mapl' (mergeAssoc {xs=[x]} . braid') . assoc' . splitAssoc

||| Insert the first object of a tensor product sequence into a later
||| position.
|||
||| This is the inverse of `bringToFront'`.
public export
insertFromFront : Braided cat ten i => {x,xs,ys : _} ->
              cat (TenSeq ten i (x :: xs ++ ys)) (TenSeq ten i (xs ++ x :: ys))
insertFromFront @{c@(MkBraided{})} {ys=[]} =
  rewrite appendNilRightNeutral xs in mergeAssoc . braid . splitAssoc {xs=[_]}
insertFromFront @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc . assoc . mapl' (Core.(.) braid $ splitAssoc {xs=[x]}) . splitAssoc {xs=x::xs}

||| Insert the first object of a tensor product sequence into a later
||| position.
|||
||| This is the inverse of `bringToFront`. This uses `braid'` instead
||| of `braid`. For symmetric monoidal categories, this is equivalent
||| to `insertFromFront`.
public export
insertFromFront' : Braided cat ten i => {x,xs,ys : _} ->
               cat (TenSeq ten i (x :: xs ++ ys)) (TenSeq ten i (xs ++ x :: ys))
insertFromFront' @{c@(MkBraided{})} {ys=[]} =
  rewrite appendNilRightNeutral xs in mergeAssoc . braid' . splitAssoc {xs=[_]}
insertFromFront' @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc . assoc . mapl' (Core.(.) braid' $ splitAssoc {xs=[x]}) . splitAssoc {xs=x::xs}

||| Send a single object of a tensor product sequence to the back.
public export
sendToBack : Braided cat ten i => {xs,x,ys : _} ->
               cat (TenSeq ten i (xs ++ x :: ys)) (TenSeq ten i (xs ++ ys ++ [x]))
sendToBack @{c@(MkBraided{})} {ys=[]} = id
sendToBack @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc . mapr' (mergeAssoc {ys=[x]} . braid) . splitAssoc

||| Send a single object of a tensor product sequence to the back.
|||
||| This uses `braid'` instead of `braid`. For symmetric monoidal
||| categories, this is identical to `sendToBack`.
public export
sendToBack' : Braided cat ten i => {xs,x,ys : _} ->
               cat (TenSeq ten i (xs ++ x :: ys)) (TenSeq ten i (xs ++ ys ++ [x]))
sendToBack' @{c@(MkBraided{})} {ys=[]} = id
sendToBack' @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc . mapr' (mergeAssoc {ys=[x]} . braid') . splitAssoc

||| Insert the last object of a tensor product sequence into an earlier
||| position.
|||
||| This is the inverse of `sendToBack'`.
public export
insertFromBack : Braided cat ten i => {xs,x,ys : _} ->
                 cat (TenSeq ten i (xs ++ ys ++ [x])) (TenSeq ten i (xs ++ x :: ys))
insertFromBack @{c@(MkBraided{})} {ys=[]} = id
insertFromBack @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc . mapr' (braid . splitAssoc {ys=[x]}) . splitAssoc

||| Insert the last object of a tensor product sequence into an earlier
||| position.
|||
||| This is the inverse of `sendToBack`. This uses `braid'` instead
||| of `braid`. For symmetric monoidal categories, this is equivalent
||| to `insertFromBack`.
public export
insertFromBack' : Braided cat ten i => {xs,x,ys : _} ->
                 cat (TenSeq ten i (xs ++ ys ++ [x])) (TenSeq ten i (xs ++ x :: ys))
insertFromBack' @{c@(MkBraided{})} {ys=[]} = id
insertFromBack' @{c@(MkBraided{})} {ys=_::_} =
  mergeAssoc . mapr' (braid' . splitAssoc {ys=[x]}) . splitAssoc

-- This definition cheats HARD, but it only uses `believe_me` for
-- unifying expressions that are actually equal, so it *should* work.
-- TODO: Replace this with something far, far less jank
permuteDefault @{c@(MkMonoidal{})} {xs} br p = go (toList $ inverse p)
  where
    brc : Braided cat ten i
    brc = MkBraided br br (believe_me ())

    believeFst : forall a,b,c. cat a c -> cat b c
    believeFst x = replace {p = flip cat _} (believe_me $ Refl {x=()}) x
    believeSnd : forall a,b,c. cat a b -> cat a c
    believeSnd x = replace {p = cat _} (believe_me $ Refl {x=()}) x

    go : {xs' : _} -> List Nat -> cat (TenSeq ten i xs') (TenSeq ten i $ permuteList xs p)
    go [] = believeSnd id
    go (i :: is) =
      believeSnd
        (go {xs' = take i xs' ++ drop (S i) xs' ++
                    [index' xs' (natToFinLt i @{believe_me Oh})]}
            is)
      .
      believeFst
        (sendToBack @{brc}
          {xs = take i xs',
          x = index' xs' (natToFinLt i @{believe_me Oh}),
          ys = drop (S i) xs'})


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace Braided
  ||| Invert the braiding of the monoidal category. If the braiding is
  ||| symmetric, this does nothing.
  public export
  [FlipBraid] {ten,i : _} -> Braided cat ten i => Braided cat ten i where
    braid = braid'
    braid' = braid
    permute = permuteDefault {ten} braid

-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

namespace Braided
  ||| Convert a `Symmetric` `Tensor` into a braided monoidal structure
  ||| on `Morphism`.
  public export
  [MorFromTensor] {ten,i : _} -> (Tensor.Symmetric ten, Tensor ten i) =>
      Braided Morphism ten i using Monoidal.MorFromTensor where
    braid = Mor swap'
    permute = permuteDefault @{MorFromTensor} (Mor swap')

  ||| Convert a `Symmetric` `Tensor` into a braided monoidal structure
  ||| on the function category.
  public export
  [FuncFromTensor] {ten,i : _} -> (Tensor.Symmetric ten, Tensor ten i) =>
      Braided (~~>) ten i using Category.Function Monoidal.FuncFromTensor where
    braid = swap'
    permute = permuteDefault @{FuncFromTensor} swap'

  ||| Convert a `Symmetric` `Tensor` into a braided monoidal structure
  ||| on the Kleisli category.
  |||
  ||| WARNING: Whether this forms a proper monoidal category is
  ||| dependent on the behavior of the `Bitraversable` implementation.
  ||| In particular, this is usually a premonoidal category.
  public export
  [KleisliFromTensor] {ten,i : _} -> (Tensor.Symmetric ten, Tensor ten i, Bitraversable ten, Monad m) =>
      Braided (Kleislimorphism m) ten i using Monoidal.KleisliFromTensor where
    braid = Kleisli $ pure . swap'
    permute p = Kleisli $ Prelude.(.) pure $ permute @{FuncFromTensor} p

public export
Braided Morphism Pair () where
  braid = Mor swap
  permute p = Mor $ \xs => pairFromHList $ permuteHList p $ pairToHList xs

public export %hint
BraidedMorEither : Braided Morphism Either Void
BraidedMorEither = MorFromTensor

||| WARNING: This is a premonoidal category, not truly monoidal.
public export %hint
BraidedKleisliPair : Monad m => PreBraided (Kleislimorphism m) Pair ()
BraidedKleisliPair = MkBraided
  (Kleisli $ pure . swap)
  (Kleisli $ pure . swap)
  (\p => Kleisli $ \xs => pure $ pairFromHList $ permuteHList p $ pairToHList xs)

public export %hint
BraidedKleisliEither : Monad m => Braided (Kleislimorphism m) Either Void
BraidedKleisliEither = KleisliFromTensor

namespace Braided
  public export
  [FuncPair] Braided (~~>) Pair () using Monoidal.FuncPair where
    braid = swap
    permute p xs = pairFromHList $ permuteHList p $ pairToHList xs

  public export
  FuncEither : Braided (~~>) Either Void
  FuncEither = FuncFromTensor
