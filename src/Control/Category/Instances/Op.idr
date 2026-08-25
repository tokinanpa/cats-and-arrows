||| This module defines the opposite category, which is an operation
||| on a category that flips the direction of its morphisms.
module Control.Category.Instances.Op

import Control.Category
import Control.Category.Records

%default total

||| The opposite category of `cat`.
public export
record Op (cat : a -> b -> Type)
          (x : b) (y : a) where
  constructor MkOp
  runOp : cat y x


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Semigroupoid cat => Semigroupoid (Op cat) where
  MkOp f . MkOp g = MkOp (g . f)

public export
Category cat => Category (Op cat) where
  id = MkOp id
  MkOp f . MkOp g = MkOp (g . f)

public export
CatFunctor cat cat' f => CatFunctor (Op cat) (Op cat') f where
  map = MkOp . map . runOp

public export
CatBifunctor catA catB cat' f => CatBifunctor (Op catA) (Op catB) (Op cat') f where
  bimap (MkOp f) (MkOp g) = MkOp $ bimap f g

public export
Monoidal cat ten i => Monoidal (Op cat) ten i where
  assoc = MkOp assoc'
  assoc' = MkOp assoc
  unitl = MkOp unitl'
  unitl' = MkOp unitl
  unitr = MkOp unitr'
  unitr' = MkOp unitr

public export
Braided cat ten i => Braided (Op cat) ten i where
  braid = MkOp braid'
  braid' = MkOp braid

public export
Cocartesian cat ten i => Cartesian (Op cat) ten i where
  projl = MkOp injl
  projr = MkOp injr
  prod (MkOp f) (MkOp g) = MkOp $ coprod f g
  split = MkOp merge
  elim = MkOp $ intro {ten}

public export
Cartesian cat ten i => Cocartesian (Op cat) ten i where
  injl = MkOp projl
  injr = MkOp projr
  coprod (MkOp f) (MkOp g) = MkOp $ prod f g
  merge = MkOp split
  intro = MkOp $ elim {ten}

public export
Traced cat ten i => Traced (Op cat) ten i where
  tracel = MkOp . tracel . runOp
  tracer = MkOp . tracer . runOp


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Op : (cat : SemigroupoidR) -> SemigroupoidR
  Op (MkSemigroupoidR cat) = MkSemigroupoidR (Op cat)

namespace CategoryR
  public export
  Op : (cat : CategoryR) -> CategoryR
  Op (MkCategoryR cat) = MkCategoryR (Op cat)

namespace MonoidalR
  public export
  Op : (cat : MonoidalR) -> MonoidalR
  Op (MkMonoidalR cat ten i) = MkMonoidalR (Op cat) ten i

namespace BraidedR
  public export
  Op : (cat : BraidedR) -> BraidedR
  Op (MkBraidedR cat ten i) = MkBraidedR (Op cat) ten i

namespace CartesianR
  public export
  Op : (cat : CocartesianR) -> CartesianR
  Op (MkCocartesianR cat ten i) = MkCartesianR (Op cat) ten i

namespace CocartesianR
  public export
  Op : (cat : CartesianR) -> CocartesianR
  Op (MkCartesianR cat ten i) = MkCocartesianR (Op cat) ten i

namespace TracedR
  public export
  Op : (cat : TracedR) -> TracedR
  Op (MkTracedR cat ten i) = MkTracedR (Op cat) ten i


namespace FunctorR
  public export
  Op : (f : FunctorR cat cat') -> FunctorR (Op cat) (Op cat')
  Op {cat=MkCategoryR{},cat'=MkCategoryR{}} (MkFunctorR f) = MkFunctorR f
