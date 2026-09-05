||| This module defines `Linear`, the category of types and linear
||| functions. Unlike the unrestricted function category `Typ`, this
||| is a non-distributive bimonoidal category.
module Control.Category.Instances.Linear

import Control.Category
import Control.Category.Records
import Control.Category.Instances.Type
import Data.Linear
import Data.Linear.LEither
import Data.Linear.LMaybe
import Data.Morphisms
import Data.Wrap0

%default total

||| The category of types and linear functions.
public export
data Linear : (a,b : Type0) -> Type where
  MkLinear : (1 _ : a.runW0 -@ b.runW0) -> Linear a b

public export %inline %tcinline
runLinear : Linear a b -@ a.runW0 -@ b.runW0
runLinear (MkLinear f) = f

public export %inline %tcinline
(.runLinear) : Linear a b -@ a.runW0 -@ b.runW0
(.runLinear) = runLinear


public export
LPair : Type0 -> Type0 -> Type0
LPair = liftW2 LPair

public export
LEither : Type0 -> Type0 -> Type0
LEither = liftW2 LEither

public export
LinearHom : Type0 -> Type0 -> Type0
LinearHom a b = W0 (Linear a b)


public export
leither : a -@ c -> b -@ c -> LEither a b -@ c
leither f g (Left x) = f x
leither f g (Right y) = g y


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Category Linear where
  id = MkLinear id
  MkLinear f . MkLinear g = MkLinear (f . g)

public export %hint
LinearSemigroupoid : Semigroupoid Linear
LinearSemigroupoid = FromCategory


-- NOTE: Functors defined on `Linear` can be thought of as "weak"
-- linear functors, as in they have the type `(a -@ b) -> (f a -@ f b)`
-- rather than `(a -@ b) -@ (f a -@ f b)`

public export
CatFunctor Linear Typ Prelude.id where
  map (MkLinear f) = MkTyp $ \x => f x

public export
CatFunctor Linear Linear (liftW LMaybe) where
  map (MkLinear f) = MkLinear $ (<$>) f

public export
CatBifunctor Linear Linear Linear LPair where
  bimap (MkLinear f) (MkLinear g) = MkLinear (\(x # y) => f x # g y)

public export
CatBifunctor Linear Linear Linear LEither where
  bimap (MkLinear f) (MkLinear g) = MkLinear (leither (Left . f) (Right . g))

public export
Monoidal Linear LPair (W0 ()) where
  assoc = MkLinear $ \((x # y) # z) => x # (y # z)
  assoc' = MkLinear $ \(x # (y # z)) => (x # y) # z
  unitl = MkLinear $ \(() # x) => x
  unitl' = MkLinear (() #)
  unitr = MkLinear $ \(x # ()) => x
  unitr' = MkLinear (# ())

public export
Monoidal Linear LEither (W0 Void) where
  assoc = MkLinear $ leither (leither Left (Right . Left)) (Right . Right)
  assoc' = MkLinear $ leither (Left . Left) (leither (Left . Right) Right)
  unitl = MkLinear $ leither (\_ impossible) id
  unitl' = MkLinear Right
  unitr = MkLinear $ leither id (\_ impossible)
  unitr' = MkLinear Left

public export
Braided Linear LPair (W0 ()) where
  braid = MkLinear $ \(x # y) => y # x

public export
Braided Linear LEither (W0 Void) where
  braid = MkLinear $ leither Right Left

public export
Bimonoidal Linear LEither LPair (W0 Void) (W0 ()) where
  distribl = MkLinear $ \(x # y) => case y of
                                      Left y' => Left (x # y')
                                      Right y' => Right (x # y')
  distribl' = MkLinear $ leither (\(x # y) => x # Left y) (\(x # y) => x # Right y)
  distribr = MkLinear $ \(x # y) => case x of
                                      Left x' => Left (x' # y)
                                      Right x' => Right (x' # y)
  distribr' = MkLinear $ leither (\(x # y) => Left x # y) (\(x # y) => Right x # y)
  absorbl = MkLinear $ \(_ # _) impossible
  absorbl' = MkLinear $ \_ impossible
  absorbr = MkLinear $ \(_ # _) impossible
  absorbr' = MkLinear $ \_ impossible

public export
Closed Linear LPair LinearHom (W0 ()) where
  curry (MkLinear f) = MkLinear $ \x => MkLinear $ \y => f (x # y)
  uncurry (MkLinear f) = MkLinear $ \(x # y) => case f x of MkLinear f' => f' y


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Linear : SemigroupoidR
  Linear = MkSemigroupoidR Linear

namespace CategoryR
  public export
  Linear : CategoryR
  Linear = MkCategoryR Linear

namespace FunctorR
  public export
  LinearToTyp : FunctorR Linear Typ
  LinearToTyp = MkFunctorR id
    {impl = MkCatFunctor $ \(MkLinear f) => MkTyp (\x => f x)}

  public export
  LMaybe : EndofunctorR Linear
  LMaybe = MkFunctorR (liftW LMaybe)

namespace BifunctorR
  public export
  LPair : EndoBifunctorR Linear
  LPair = MkBifunctorR LPair

  public export
  LEither : EndoBifunctorR Linear
  LEither = MkBifunctorR LEither

namespace MonoidalR
  public export
  LinearLPair : MonoidalR
  LinearLPair = MkMonoidalR Linear LPair (W0 ())

  public export
  LinearLEither : MonoidalR
  LinearLEither = MkMonoidalR Linear LEither (W0 Void)

namespace BraidedR
  public export
  LinearLPair : BraidedR
  LinearLPair = MkBraidedR Linear LPair (W0 ())

  public export
  LinearLEither : BraidedR
  LinearLEither = MkBraidedR Linear LEither (W0 Void)

namespace BimonoidalR
  public export
  Linear : BimonoidalR
  Linear = MkBimonoidalR Linear LEither LPair (W0 Void) (W0 ())

namespace RigCategoryR
  public export
  Linear : RigCategoryR
  Linear = MkRigCategoryR Linear LEither LPair (W0 Void) (W0 ())

namespace SymRigCategoryR
  public export
  Linear : SymRigCategoryR
  Linear = MkSymRigCategoryR Linear LEither LPair (W0 Void) (W0 ())

namespace ClosedR
  public export
  Linear : ClosedR
  Linear = MkClosedR Linear LPair LinearHom (W0 ())
