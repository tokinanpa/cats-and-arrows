module Control.Category.Braided

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Data.Morphisms
import Data.Tensor

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
    Braided (0 cat : Hom obj) (0 ten : obj -> obj -> obj) (0 i : obj) | cat where
  constructor MkBraided
  ||| The braiding of the category.
  braid : forall a,b. cat (a `ten` b) (b `ten` a)

  ||| The inverse of `braid`, the braiding of the category.
  |||
  ||| The default definition sets this equal to `braid`, making the
  ||| assumption that this braiding is symmetric. If it isn't, then
  ||| both methods must be defined.
  braid' : forall a,b. cat (b `ten` a) (a `ten` b)
  braid' = braid

||| See `PreMonoidal`.
public export
PreBraided : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> Type
PreBraided = Braided


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace Braided
  ||| Convert a `Symmetric` `Tensor` into a braided monoidal structure
  ||| on `Morphism`.
  public export
  [MorFromTensor] (Tensor.Symmetric ten, Tensor ten i) => Braided Morphism ten i
      using Monoidal.MorFromTensor where
    braid = Mor swap'

  ||| Convert a `Symmetric` `Tensor` into a braided monoidal structure
  ||| on the function category.
  public export
  [FuncFromTensor] (Tensor.Symmetric ten, Tensor ten i) => Braided (~~>) ten i
      using Category.Function Monoidal.FuncFromTensor where
    braid = swap'

  ||| Convert a `Symmetric` `Tensor` into a braided monoidal structure
  ||| on the Kleisli category.
  |||
  ||| WARNING: Whether this forms a proper monoidal category is
  ||| dependent on the behavior of the `Bitraversable` implementation.
  ||| In particular, this is usually a premonoidal category.
  public export
  [KleisliFromTensor] (Tensor.Symmetric ten, Tensor ten i, Bitraversable ten, Monad m) =>
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

  ||| Invert the braiding of the monoidal category. If the braiding is
  ||| symmetric, this does nothing.
  public export
  [FlipBraid] Braided cat ten i => Braided cat ten i where
    braid = braid'
    braid' = braid
