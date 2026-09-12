||| This module defines `Zero`, the one category, which contains one
||| single object and one identity morphism.
module Control.Category.Instances.One

import Control.Category
import Control.Category.Records

%default total

||| The one category, or terminal category. This category contains one
||| object and one identity morphism.
public export
data One : (a,b : ()) -> Type where
  MkOne : One () ()

public export
UnitOp : a -> ()
UnitOp _ = ()

public export
UnitOp2 : a -> b -> ()
UnitOp2 _ _ = ()


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Category One where
  id {a=()} = MkOne
  MkOne . MkOne = MkOne

%hint
SemigroupoidOne : Semigroupoid One
SemigroupoidOne = FromCategory


public export
CatFunctor cat One UnitOp where
  map _ = MkOne

public export
CatMonad One UnitOp where
  unit {a=()} = MkOne
  join = MkOne

public export
CatBifunctor catA catB One UnitOp2 where
  bimap _ _ = MkOne

public export
Monoidal One UnitOp2 () where
  assoc = MkOne
  assoc' = MkOne
  unitl {a=()} = MkOne
  unitl' {a=()} = MkOne
  unitr {a=()} = MkOne
  unitr' {a=()} = MkOne

public export
Braided One UnitOp2 () where
  braid = MkOne
  braid' = MkOne

public export
Cartesian One UnitOp2 () where
  projl {a=()} = MkOne
  projr {b=()} = MkOne
  prod {a=()} _ _ = MkOne
  split {a=()} = MkOne
  elim {a=()} = MkOne

public export
Cocartesian One UnitOp2 () where
  injl {a=()} = MkOne
  injr {b=()} = MkOne
  coprod {b=()} _ _ = MkOne
  merge {a=()} = MkOne
  intro {a=()} = MkOne

public export
Closed One UnitOp2 UnitOp2 () where
  curry {a=()} _ = MkOne
  uncurry {c=()} _ = MkOne

public export
Traced One UnitOp2 () where
  tracel {b=(),c=()} _ = MkOne
  tracer {a=(),b=()} _ = MkOne

public export
Bimonoidal One UnitOp2 UnitOp2 () () where
  distribl = MkOne
  distribl' = MkOne
  distribr = MkOne
  distribr' = MkOne
  absorbl = MkOne
  absorbl' = MkOne
  absorbr = MkOne
  absorbr' = MkOne


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  One : SemigroupoidR
  One = MkSemigroupoidR One

namespace CategoryR
  public export
  One : CategoryR
  One = MkCategoryR One

namespace MonoidalR
  public export
  One : MonoidalR
  One = MkMonoidalR One UnitOp2 ()

namespace BraidedR
  public export
  One : BraidedR
  One = MkBraidedR One UnitOp2 ()

namespace CartesianR
  public export
  One : CartesianR
  One = MkCartesianR One UnitOp2 ()

namespace CocartesianR
  public export
  One : CocartesianR
  One = MkCocartesianR One UnitOp2 ()

namespace ClosedR
  public export
  One : ClosedR
  One = MkClosedR One UnitOp2 UnitOp2 ()

namespace TracedR
  public export
  One : TracedR
  One = MkTracedR One UnitOp2 ()

namespace BimonoidalR
  public export
  One : BimonoidalR
  One = MkBimonoidalR One UnitOp2 UnitOp2 () ()

namespace RigCategoryR
  public export
  One : RigCategoryR
  One = MkRigCategoryR One UnitOp2 UnitOp2 () ()

namespace SymRigCategoryR
  public export
  One : SymRigCategoryR
  One = MkSymRigCategoryR One UnitOp2 UnitOp2 () ()

namespace DistributiveR
  public export
  One : DistributiveR
  One = MkDistributiveR One UnitOp2 UnitOp2 () ()


namespace FunctorR
  public export
  OneTerminal : FunctorR cat One
  OneTerminal = MkFunctorR UnitOp

namespace MonadR
  public export
  OneM : MonadR One
  OneM = MkMonadR UnitOp

namespace BifunctorR
  public export
  OneBi : BifunctorR catA catB One
  OneBi = MkBifunctorR UnitOp2
