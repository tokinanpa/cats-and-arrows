||| This module defines `Zero`, the zero category, which contains no
||| objects and no morphisms.
module Control.Category.Instances.Zero

import Control.Category
import Control.Category.Records

%default total

||| The zero category, or initial category. This category contains
||| no objects and no morphisms.
public export
data Zero : (a,b : Void) -> Type where
  
public export
Uninhabited (Zero a b) where
  uninhabited _ impossible


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Category Zero where
  id {a} = void a
  (.) {a} = void a

%hint
SemigroupoidZero : Semigroupoid Zero
SemigroupoidZero = FromCategory

public export
Either (cat ~=~ Zero) (cat' ~=~ Zero) => CatFunctor cat cat' f where
  map @{Left Refl} {a} = void a
  map @{Right Refl} {a} = void (f a)

public export
Either (catA ~=~ Zero) (Either (catB ~=~ Zero) (cat' ~=~ Zero)) =>
    CatBifunctor catA catB cat' f where
  bimap @{Left Refl} {a} = void a
  bimap @{Right (Left Refl)} {a'} = void a'
  bimap @{Right (Right Refl)} {a,a'} = void (f a a')

public export
CatMonad Zero m where
  join {a} = void a
  unit {a} = void a

public export
{ten,i : _} -> Monoidal Zero ten i where
  assoc = void i
  assoc' = void i
  unitl = void i
  unitl' = void i
  unitr = void i
  unitr' = void i

public export
{ten,i : _} -> Braided Zero ten i where
  braid = void i
  braid' = void i

public export
{ten,i : _} -> MonSymmetric Zero ten i where
  permute = void i

public export
{ten,i : _} -> Cartesian Zero ten i where
  projl = void i
  projr = void i
  prod = void i
  split = void i
  elim = void i

public export
{ten,i : _} -> Cocartesian Zero ten i where
  injl = void i
  injr = void i
  coprod = void i
  merge = void i
  intro = void i

public export
{ten,hom,i : _} -> Closed Zero ten hom i where
  curry = void i
  uncurry = void i

public export
{ten,i : _} -> Traced Zero ten i where
  tracel = void i
  tracer = void i

public export
{add,mul,z,i : _} -> Bimonoidal Zero add mul z i where
  distribl = void i
  distribl' = void i
  distribr = void i
  distribr' = void i
  absorbl = void i
  absorbl' = void i
  absorbr = void i
  absorbr' = void i


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Zero : SemigroupoidR
  Zero = MkSemigroupoidR Zero

namespace CategoryR
  public export
  Zero : CategoryR
  Zero = MkCategoryR Zero

namespace FunctorR
  public export
  ZeroInitial : FunctorR Zero cat
  ZeroInitial = MkFunctorR absurd
