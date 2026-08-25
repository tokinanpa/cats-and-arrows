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

%default total

||| The category of types and linear functions.
public export
data Linear : (a,b : Type) -> Type where
  MkLinear : (1 _ : a -@ b) -> Linear a b

public export %inline %tcinline
runLinear : Linear a b -@ a -@ b
runLinear (MkLinear f) = f

public export %inline %tcinline
(.runLinear) : Linear a b -@ a -@ b
(.runLinear) = runLinear


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


public export
CatFunctor Linear Morphism Prelude.id where
  map (MkLinear f) = Mor $ \x => f x

public export
CatFunctor Linear Linear LMaybe where
  map (MkLinear f) = MkLinear $ (<$>) f

public export
CatBifunctor Linear Linear Linear LPair where
  bimap (MkLinear f) (MkLinear g) = MkLinear (\(x # y) => f x # g y)

public export
CatBifunctor Linear Linear Linear LEither where
  bimap (MkLinear f) (MkLinear g) = MkLinear (leither (Left . f) (Right . g))

public export
Monoidal Linear LPair () where
  assoc = MkLinear $ \((x # y) # z) => x # (y # z)
  assoc' = MkLinear $ \(x # (y # z)) => (x # y) # z
  unitl = MkLinear $ \(() # x) => x
  unitl' = MkLinear (() #)
  unitr = MkLinear $ \(x # ()) => x
  unitr' = MkLinear (# ())

public export
Monoidal Linear LEither Void where
  assoc = MkLinear $ leither (leither Left (Right . Left)) (Right . Right)
  assoc' = MkLinear $ leither (Left . Left) (leither (Left . Right) Right)
  unitl = MkLinear $ leither (\_ impossible) id
  unitl' = MkLinear Right
  unitr = MkLinear $ leither id (\_ impossible)
  unitr' = MkLinear Left

public export
Braided Linear LPair () where
  braid = MkLinear $ \(x # y) => y # x

public export
Braided Linear LEither Void where
  braid = MkLinear $ leither Right Left

public export
Bimonoidal Linear LEither LPair Void () where
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
Closed Linear LPair Linear () where
  curry (MkLinear f) = MkLinear $ \x => MkLinear $ \y => f (x # y)
  uncurry (MkLinear f) = MkLinear $ \(x # y) => case f x of MkLinear f' => f' y

public export
Closed Linear LPair (-@) () where
  curry (MkLinear f) = MkLinear $ \x,y => f (x # y)
  uncurry (MkLinear f) = MkLinear $ \(x # y) => f x y


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
  LinearToTyp = MkFunctorR id {impl = MkCatFunctor $ \(MkLinear f),x => f x}

  public export
  LMaybe : EndofunctorR Linear
  LMaybe = MkFunctorR LMaybe

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
  LinearLPair = MkMonoidalR Linear LPair ()

  public export
  LinearLEither : MonoidalR
  LinearLEither = MkMonoidalR Linear LEither Void

namespace BraidedR
  public export
  LinearLPair : BraidedR
  LinearLPair = MkBraidedR Linear LPair ()

  public export
  LinearLEither : BraidedR
  LinearLEither = MkBraidedR Linear LEither Void

namespace BimonoidalR
  public export
  Linear : BimonoidalR
  Linear = MkBimonoidalR Linear LEither LPair Void ()

namespace RigCategoryR
  public export
  Linear : RigCategoryR
  Linear = MkRigCategoryR Linear LEither LPair Void ()

namespace SymRigCategoryR
  public export
  Linear : SymRigCategoryR
  Linear = MkSymRigCategoryR Linear LEither LPair Void ()

namespace ClosedR
  public export
  Linear : ClosedR
  Linear = MkClosedR Linear LPair (-@) ()
