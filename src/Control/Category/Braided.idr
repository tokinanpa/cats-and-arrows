module Control.Category.Braided

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Data.Morphisms
import Data.Tensor
import Data.Vect

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

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

||| Bring a single object of a tensor product sequence to the front.
public export
bringToFront : Braided cat ten i => {xs,x,ys : _} ->
               cat (TenSeq ten i ((xs ++ [x]) ++ ys)) (TenSeq ten i (x :: xs ++ ys))
bringToFront @{c@(MkBraided{})} = mergeAssoc . mapl' swapAssoc . splitAssoc


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

  ||| Convert a `Symmetric` `Tensor` into a braided monoidal structure
  ||| on the function category.
  public export
  [FuncFromTensor] {ten,i : _} -> (Tensor.Symmetric ten, Tensor ten i) =>
      Braided (~~>) ten i using Category.Function Monoidal.FuncFromTensor where
    braid = swap'

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

public export %hint
BraidedMorPair : Braided Morphism Pair ()
BraidedMorPair = MorFromTensor

public export %hint
BraidedMorEither : Braided Morphism Either Void
BraidedMorEither = MorFromTensor

||| WARNING: This is a premonoidal category, not truly monoidal.
public export %hint
BraidedKleisliPair : Monad m => PreBraided (Kleislimorphism m) Pair ()
BraidedKleisliPair = KleisliFromTensor

public export %hint
BraidedKleisliEither : Monad m => Braided (Kleislimorphism m) Either Void
BraidedKleisliEither = KleisliFromTensor

namespace Braided
  public export
  FuncPair : Braided (~~>) Pair ()
  FuncPair = FuncFromTensor

  public export
  FuncEither : Braided (~~>) Either Void
  FuncEither = FuncFromTensor
