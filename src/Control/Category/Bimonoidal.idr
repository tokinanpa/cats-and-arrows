module Control.Category.Bimonoidal

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Control.Category.Braided
import Control.Category.Cartesian
import Control.Category.Cocartesian
import Data.Morphisms

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

private infixl 8 `add`
private infixl 9 `mul`

||| A *bimonoidal category* is a category with two monoidal structures,
||| one additive and one multiplicative, that are compatible with each
||| other in a similar way to elementary algebra.
|||
||| This is the interface-style definition of a bimonoidal category.
||| For the record-style definition, see `Control.Category.Records.BimonoidalR`.
|||
||| As for coherence laws: they do exist, but they are so numerous as
||| to be impractical to write here. (You wouldn't check them anyway.)
||| If you do wish to be fully rigorous, here's a textbook on
||| bimonoidal categories to read:
||| * https://nilesjohnson.net/En-monoidal.html
public export
interface (Monoidal cat add z, Monoidal cat mul i) =>
    Bimonoidal (0 cat : Hom obj) (0 add,mul : obj -> obj -> obj) (0 z,i : obj) | cat,add,mul where
  constructor MkBimonoidal
  ||| The left distributor.
  distribl : forall a,b,c. cat (a `mul` (b `add` c)) (a `mul` b `add` a `mul` c)
  ||| The inverse of `distribl`, the left distributor.
  distribl' : forall a,b,c. cat (a `mul` b `add` a `mul` c) (a `mul` (b `add` c))

  ||| The right distributor.
  distribr : forall a,b,c. cat ((a `add` b) `mul` c) (a `mul` c `add` b `mul` c)
  ||| The inverse of `distribr`, the right distributor.
  distribr' : forall a,b,c. cat (a `mul` c `add` b `mul` c) ((a `add` b) `mul` c)

  ||| The left absorbor.
  absorbl : forall a. cat (a `mul` z) z
  ||| The inverse of `absorbl`, the left absorbor.
  absorbl' : forall a. cat z (a `mul` z)

  ||| The right absorbor.
  absorbr : forall a. cat (z `mul` a) z
  ||| The inverse of `absorbr`, the right absorbor.
  absorbr' : forall a. cat z (z `mul` a)

||| A pre-bimonoidal category has a multiplicative structure that is
||| premonoidal. See `PreMonoidal`.
public export
PreBimonoidal : (cat : Hom obj) -> (add,mul : obj -> obj -> obj) -> (z,i : obj) -> Type
PreBimonoidal = Bimonoidal

||| A rig category is a bimonoidal category whose additive structure
||| is symmetric. The name "rig" comes from the algebraic structure
||| the definition is based on (a ring without negatives).
|||
||| This is the interface-style definition of a rig category. For the
||| record-style definition, see `Control.Category.Records.RigCategoryR`.
public export
RigCategory : (cat : Hom obj) -> (add,mul : obj -> obj -> obj) -> (z,i : obj) -> Type
RigCategory cat add mul z i = (Bimonoidal cat add mul z i, Braided cat add z)

||| A pre-bimonoidal category has a multiplicative structure that is
||| premonoidal. See `PreMonoidal`.
public export
PreRigCategory : (cat : Hom obj) -> (add,mul : obj -> obj -> obj) -> (z,i : obj) -> Type
PreRigCategory = RigCategory

||| A symmetric rig category is a bimonoidal category where both the
||| additive and multiplicative structures are symmetric.
|||
||| This is the interface-style definition of a symmetric rig category.
||| For the record-style definition, see `Control.Category.Records.SymRigCategoryR`.
public export
SymRigCategory : (cat : Hom obj) -> (add,mul : obj -> obj -> obj) -> (z,i : obj) -> Type
SymRigCategory cat add mul z i = (RigCategory cat add mul z i, Braided cat mul i)

||| A pre-bimonoidal category has a multiplicative structure that is
||| premonoidal. See `PreMonoidal`.
public export
PreSymRigCategory : (cat : Hom obj) -> (add,mul : obj -> obj -> obj) -> (z,i : obj) -> Type
PreSymRigCategory = SymRigCategory

||| A distributive category is a bimonoidal category whose
||| multiplicative and additive structures are cartesian and
||| cocartesian respectively.
|||
||| This is the interface-style definition of a distributuve category.
||| For the record-style definition, see `Control.Category.Records.DistributiveR`.
public export
Distributive : (cat : Hom obj) -> (add,mul : obj -> obj -> obj) -> (z,i : obj) -> Type
Distributive cat add mul z i =
  (SymRigCategory cat add mul z i, Cartesian cat mul i, Cocartesian cat add z)

||| A pre-bimonoidal category has a multiplicative structure that is
||| premonoidal. See `PreMonoidal`.
public export
PreDistributive : (cat : Hom obj) -> (add,mul : obj -> obj -> obj) -> (z,i : obj) -> Type
PreDistributive = Distributive


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

public export
Bimonoidal Morphism Either Pair Void () where
  distribl = Mor $ \(x,y) => bimap (x,) (x,) y
  distribl' = Mor $ either (mapSnd Left) (mapSnd Right)
  distribr = Mor $ \(x,y) => bimap (,y) (,y) x
  distribr' = Mor $ either (mapFst Left) (mapFst Right)
  absorbl = Mor snd
  absorbl' = Mor absurd
  absorbr = Mor fst
  absorbr' = Mor absurd

namespace Bimonoidal
  public export
  [Function] Bimonoidal (~~>) Either Pair Void ()
      using Monoidal.FuncPair Monoidal.FuncEither where
    distribl = \(x,y) => bimap (x,) (x,) y
    distribl' = either (mapSnd Left) (mapSnd Right)
    distribr = \(x,y) => bimap (,y) (,y) x
    distribr' = either (mapFst Left) (mapFst Right)
    absorbl = snd
    absorbl' = absurd
    absorbr = fst
    absorbr' = absurd

namespace RigCategory
  public export
  Function : RigCategory (~~>) Either Pair Void ()
  Function = (Function, FuncEither)

namespace SymRigCategory
  public export
  Function : SymRigCategory (~~>) Either Pair Void ()
  Function = (Function, FuncPair)

namespace Distributive
  public export
  Function : Distributive (~~>) Either Pair Void ()
  Function = (Function, Function, Function)

public export
Monad m => Bimonoidal (Kleislimorphism m) Either Pair Void () where
  distribl = Kleisli $ \(x,y) => pure $ bimap (x,) (x,) y
  distribl' = Kleisli $ pure . either (mapSnd Left) (mapSnd Right)
  distribr = Kleisli $ \(x,y) => pure $ bimap (,y) (,y) x
  distribr' = Kleisli $ pure . either (mapFst Left) (mapFst Right)
  absorbl = Kleisli $ pure . snd
  absorbl' = Kleisli absurd
  absorbr = Kleisli $ pure . fst
  absorbr' = Kleisli absurd
