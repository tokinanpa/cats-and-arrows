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
Monoidal Zero ten i where
  assoc {a} = void a
  assoc' {a} = void a
  unitl {a} = void a
  unitl' {a} = void a
  unitr {a} = void a
  unitr' {a} = void a

public export
Braided Zero ten i where
  braid {a} = void a
  braid' {a} = void a

public export
Cartesian Zero ten i where
  projl {a} = void a
  projr {a} = void a
  prod {a} = void a
  split {a} = void a
  elim {a} = void a

public export
Cocartesian Zero ten i where
  injl {a} = void a
  injr {a} = void a
  coprod {a} = void a
  merge {a} = void a
  intro {a} = void a

public export
Closed Zero ten hom i where
  curry {a} = void a
  uncurry {a} = void a

public export
Traced Zero ten i where
  tracel {a} = void a
  tracer {a} = void a

public export
Bimonoidal Zero add mul z i where
  distribl {a} = void a
  distribl' {a} = void a
  distribr {a} = void a
  distribr' {a} = void a
  absorbl {a} = void a
  absorbl' {a} = void a
  absorbr {a} = void a
  absorbr' {a} = void a


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
