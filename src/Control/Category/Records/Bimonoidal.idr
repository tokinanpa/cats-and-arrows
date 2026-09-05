module Control.Category.Records.Bimonoidal

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor
import Control.Category.Records.Monoidal
import Control.Category.Records.Braided
import Control.Category.Records.Cartesian
import Control.Category.Records.Cocartesian
import Data.Morphisms

%default total
%prefix_record_projections off

||| A *bimonoidal category* is a category with two monoidal structures,
||| one additive and one multiplicative, that are compatible with each
||| other in a similar way to elementary algebra.
public export
record BimonoidalR where
  constructor MkBimonoidalR
  hom : Hom obj
  add, mul : obj -> obj -> obj
  zero, one : obj
  {auto impl : Bimonoidal hom add mul zero one}

||| See `PreMonoidal`.
public export
PreBimonoidalR : Type
PreBimonoidalR = BimonoidalR

namespace BimonoidalR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : BimonoidalR) -> CategoryR
  (.categoryR) (MkBimonoidalR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : BimonoidalR) -> {a : _} -> rec.hom a a
  (.id) rec@(MkBimonoidalR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : BimonoidalR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkBimonoidalR {}) = rec.categoryR.comp


  ||| The additive tensor product as a `BifunctorR`.
  public export %inline
  (.addR) : (rec : BimonoidalR) -> EndoBifunctorR rec.categoryR
  (.addR) (MkBimonoidalR {} {add}) = MkBifunctorR add

  ||| The multiplicative tensor product as a `BifunctorR`.
  public export %inline
  (.mulR) : (rec : BimonoidalR) -> EndoBifunctorR rec.categoryR
  (.mulR) (MkBimonoidalR {} {mul}) = MkBifunctorR mul

  ||| Convert this into a `MonoidalR` with the additive tensor product.
  public export %inline
  (.addCatR) : (rec : BimonoidalR) -> MonoidalR
  (.addCatR) (MkBimonoidalR {} {hom,add,zero}) = MkMonoidalR hom add zero

  ||| Convert this into a `MonoidalR` with the multiplicative tensor product.
  public export %inline
  (.mulCatR) : (rec : BimonoidalR) -> MonoidalR
  (.mulCatR) (MkBimonoidalR {} {hom,mul,one}) = MkMonoidalR hom mul one


  ||| Convert this into a `BimonoidalR`.
  public export %inline
  (.bimonoidalR) : (rec : BimonoidalR) -> BimonoidalR
  (.bimonoidalR) = id

  ||| The left distributor.
  public export %inline
  (.distribl) : (rec : BimonoidalR) -> {a,b,c : _} ->
                rec.hom (rec.mul a (rec.add b c)) (rec.add (rec.mul a b) (rec.mul a c))
  (.distribl) rec = distribl @{rec.impl}

  ||| The inverse of `(.distribl)`, the left distributor.
  public export %inline
  (.distribl') : (rec : BimonoidalR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a b) (rec.mul a c)) (rec.mul a (rec.add b c))
  (.distribl') rec = distribl' @{rec.impl}

  ||| The right distributor.
  public export %inline
  (.distribr) : (rec : BimonoidalR) -> {a,b,c : _} ->
                rec.hom (rec.mul (rec.add a b) c) (rec.add (rec.mul a c) (rec.mul b c))
  (.distribr) rec = distribr @{rec.impl}

  ||| The inverse of `(.distribr)`, the right distributor.
  public export %inline
  (.distribr') : (rec : BimonoidalR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a c) (rec.mul b c)) (rec.mul (rec.add a b) c)
  (.distribr') rec = distribr' @{rec.impl}

  ||| The left absorbor.
  public export %inline
  (.absorbl) : (rec : BimonoidalR) -> {a : _} -> rec.hom (rec.mul a rec.zero) rec.zero
  (.absorbl) rec = absorbl @{rec.impl}

  ||| The inverse of `(.absorbl)`, the left absorbor.
  public export %inline
  (.absorbl') : (rec : BimonoidalR) -> {a : _} -> rec.hom rec.zero (rec.mul a rec.zero)
  (.absorbl') rec = absorbl' @{rec.impl}

  ||| The right absorbor.
  public export %inline
  (.absorbr) : (rec : BimonoidalR) -> {a : _} -> rec.hom (rec.mul rec.zero a) rec.zero
  (.absorbr) rec = absorbr @{rec.impl}

  ||| The inverse of `(.absorbr)`, the right absorbor.
  public export %inline
  (.absorbr') : (rec : BimonoidalR) -> {a : _} -> rec.hom rec.zero (rec.mul rec.zero a)
  (.absorbr') rec = absorbr' @{rec.impl}


||| A rig category is a bimonoidal category whose additive structure
||| is symmetric. The name "rig" comes from the algebraic structure
||| the definition is based on (a ring without negatives).
public export
record RigCategoryR where
  constructor MkRigCategoryR
  hom : Hom obj
  add, mul : obj -> obj -> obj
  zero, one : obj
  {auto impl : RigCategory hom add mul zero one}

||| See `PreMonoidal`.
public export
PreRigCategoryR : Type
PreRigCategoryR = RigCategoryR

namespace RigCategoryR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : RigCategoryR) -> CategoryR
  (.categoryR) (MkRigCategoryR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : RigCategoryR) -> {a : _} -> rec.hom a a
  (.id) rec@(MkRigCategoryR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : RigCategoryR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkRigCategoryR {}) = rec.categoryR.comp


  ||| The additive tensor product as a `BifunctorR`.
  public export %inline
  (.addR) : (rec : RigCategoryR) -> EndoBifunctorR rec.categoryR
  (.addR) (MkRigCategoryR {} {add}) = MkBifunctorR add

  ||| The multiplicative tensor product as a `BifunctorR`.
  public export %inline
  (.mulR) : (rec : RigCategoryR) -> EndoBifunctorR rec.categoryR
  (.mulR) (MkRigCategoryR {} {mul}) = MkBifunctorR mul

  ||| Convert this into a `BraidedR` with the additive tensor product.
  public export %inline
  (.addCatR) : (rec : RigCategoryR) -> BraidedR
  (.addCatR) (MkRigCategoryR {} {hom,add,zero}) = MkBraidedR hom add zero

  ||| Convert this into a `MonoidalR` with the multiplicative tensor product.
  public export %inline
  (.mulCatR) : (rec : RigCategoryR) -> MonoidalR
  (.mulCatR) (MkRigCategoryR {} {hom,mul,one}) = MkMonoidalR hom mul one


  ||| Convert this into a `BimonoidalR`.
  public export %inline
  (.bimonoidalR) : (rec : RigCategoryR) -> BimonoidalR
  (.bimonoidalR) (MkRigCategoryR hom add mul zero one) = MkBimonoidalR hom add mul zero one

  ||| The left distributor.
  public export %inline
  (.distribl) : (rec : RigCategoryR) -> {a,b,c : _} ->
                rec.hom (rec.mul a (rec.add b c)) (rec.add (rec.mul a b) (rec.mul a c))
  (.distribl) rec@(MkRigCategoryR {}) = rec.bimonoidalR.distribl

  ||| The inverse of `(.distribl)`, the left distributor.
  public export %inline
  (.distribl') : (rec : RigCategoryR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a b) (rec.mul a c)) (rec.mul a (rec.add b c))
  (.distribl') rec@(MkRigCategoryR {}) = rec.bimonoidalR.distribl'

  ||| The right distributor.
  public export %inline
  (.distribr) : (rec : RigCategoryR) -> {a,b,c : _} ->
                rec.hom (rec.mul (rec.add a b) c) (rec.add (rec.mul a c) (rec.mul b c))
  (.distribr) rec@(MkRigCategoryR {}) = rec.bimonoidalR.distribr

  ||| The inverse of `(.distribr)`, the right distributor.
  public export %inline
  (.distribr') : (rec : RigCategoryR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a c) (rec.mul b c)) (rec.mul (rec.add a b) c)
  (.distribr') rec@(MkRigCategoryR {}) = rec.bimonoidalR.distribr'

  ||| The left absorbor.
  public export %inline
  (.absorbl) : (rec : RigCategoryR) -> {a : _} -> rec.hom (rec.mul a rec.zero) rec.zero
  (.absorbl) rec@(MkRigCategoryR {}) = rec.bimonoidalR.absorbl

  ||| The inverse of `(.absorbl)`, the left absorbor.
  public export %inline
  (.absorbl') : (rec : RigCategoryR) -> {a : _} -> rec.hom rec.zero (rec.mul a rec.zero)
  (.absorbl') rec@(MkRigCategoryR {}) = rec.bimonoidalR.absorbl'

  ||| The right absorbor.
  public export %inline
  (.absorbr) : (rec : RigCategoryR) -> {a : _} -> rec.hom (rec.mul rec.zero a) rec.zero
  (.absorbr) rec@(MkRigCategoryR {}) = rec.bimonoidalR.absorbr

  ||| The inverse of `(.absorbr)`, the right absorbor.
  public export %inline
  (.absorbr') : (rec : RigCategoryR) -> {a : _} -> rec.hom rec.zero (rec.mul rec.zero a)
  (.absorbr') rec@(MkRigCategoryR {}) = rec.bimonoidalR.absorbr'


  ||| Convert this into a `RigCategoryR`.
  public export %inline
  (.rigCategoryR) : (rec : RigCategoryR) -> RigCategoryR
  (.rigCategoryR) = id


public export
record SymRigCategoryR where
  constructor MkSymRigCategoryR
  hom : Hom obj
  add, mul : obj -> obj -> obj
  zero, one : obj
  {auto impl : SymRigCategory hom add mul zero one}

public export
PreSymRigCategoryR : Type
PreSymRigCategoryR = SymRigCategoryR

namespace SymRigCategoryR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : SymRigCategoryR) -> CategoryR
  (.categoryR) (MkSymRigCategoryR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : SymRigCategoryR) -> {a : _} -> rec.hom a a
  (.id) rec@(MkSymRigCategoryR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : SymRigCategoryR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkSymRigCategoryR {}) = rec.categoryR.comp


  ||| The additive tensor product as a `BifunctorR`.
  public export %inline
  (.addR) : (rec : SymRigCategoryR) -> EndoBifunctorR rec.categoryR
  (.addR) (MkSymRigCategoryR {} {add}) = MkBifunctorR add

  ||| The multiplicative tensor product as a `BifunctorR`.
  public export %inline
  (.mulR) : (rec : SymRigCategoryR) -> EndoBifunctorR rec.categoryR
  (.mulR) (MkSymRigCategoryR {} {mul}) = MkBifunctorR mul

  ||| Convert this into a `BraidedR` with the additive tensor product.
  public export %inline
  (.addCatR) : (rec : SymRigCategoryR) -> BraidedR
  (.addCatR) (MkSymRigCategoryR {} {hom,add,zero}) = MkBraidedR hom add zero

  ||| Convert this into a `BraidedR` with the multiplicative tensor product.
  public export %inline
  (.mulCatR) : (rec : SymRigCategoryR) -> BraidedR
  (.mulCatR) (MkSymRigCategoryR {} {hom,mul,one}) = MkBraidedR hom mul one


  ||| Convert this into a `BimonoidalR`.
  public export %inline
  (.bimonoidalR) : (rec : SymRigCategoryR) -> BimonoidalR
  (.bimonoidalR) (MkSymRigCategoryR hom add mul zero one) = MkBimonoidalR hom add mul zero one

  ||| The left distributor.
  public export %inline
  (.distribl) : (rec : SymRigCategoryR) -> {a,b,c : _} ->
                rec.hom (rec.mul a (rec.add b c)) (rec.add (rec.mul a b) (rec.mul a c))
  (.distribl) rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.distribl

  ||| The inverse of `(.distribl)`, the left distributor.
  public export %inline
  (.distribl') : (rec : SymRigCategoryR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a b) (rec.mul a c)) (rec.mul a (rec.add b c))
  (.distribl') rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.distribl'

  ||| The right distributor.
  public export %inline
  (.distribr) : (rec : SymRigCategoryR) -> {a,b,c : _} ->
                rec.hom (rec.mul (rec.add a b) c) (rec.add (rec.mul a c) (rec.mul b c))
  (.distribr) rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.distribr

  ||| The inverse of `(.distribr)`, the right distributor.
  public export %inline
  (.distribr') : (rec : SymRigCategoryR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a c) (rec.mul b c)) (rec.mul (rec.add a b) c)
  (.distribr') rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.distribr'

  ||| The left absorbor.
  public export %inline
  (.absorbl) : (rec : SymRigCategoryR) -> {a : _} -> rec.hom (rec.mul a rec.zero) rec.zero
  (.absorbl) rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.absorbl

  ||| The inverse of `(.absorbl)`, the left absorbor.
  public export %inline
  (.absorbl') : (rec : SymRigCategoryR) -> {a : _} -> rec.hom rec.zero (rec.mul a rec.zero)
  (.absorbl') rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.absorbl'

  ||| The right absorbor.
  public export %inline
  (.absorbr) : (rec : SymRigCategoryR) -> {a : _} -> rec.hom (rec.mul rec.zero a) rec.zero
  (.absorbr) rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.absorbr

  ||| The inverse of `(.absorbr)`, the right absorbor.
  public export %inline
  (.absorbr') : (rec : SymRigCategoryR) -> {a : _} -> rec.hom rec.zero (rec.mul rec.zero a)
  (.absorbr') rec@(MkSymRigCategoryR {}) = rec.bimonoidalR.absorbr'

  ||| Convert this into a `RigCategoryR`.
  public export %inline
  (.rigCategoryR) : (rec : SymRigCategoryR) -> RigCategoryR
  (.rigCategoryR) (MkSymRigCategoryR hom add mul z i) = MkRigCategoryR hom add mul z i

  ||| Convert this into a `SymRigCategoryR`.
  public export %inline
  (.symRigCategoryR) : (rec : SymRigCategoryR) -> SymRigCategoryR
  (.symRigCategoryR) = id


public export
record DistributiveR where
  constructor MkDistributiveR
  hom : Hom obj
  add, mul : obj -> obj -> obj
  zero, one : obj
  {auto impl : Distributive hom add mul zero one}

public export
PreDistributiveR : Type
PreDistributiveR = DistributiveR

namespace DistributiveR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : DistributiveR) -> CategoryR
  (.categoryR) (MkDistributiveR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : DistributiveR) -> {a : _} -> rec.hom a a
  (.id) rec@(MkDistributiveR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : DistributiveR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkDistributiveR {}) = rec.categoryR.comp


  ||| The additive tensor product as a `BifunctorR`.
  public export %inline
  (.addR) : (rec : DistributiveR) -> EndoBifunctorR rec.categoryR
  (.addR) (MkDistributiveR {} {add}) = MkBifunctorR add

  ||| The multiplicative tensor product as a `BifunctorR`.
  public export %inline
  (.mulR) : (rec : DistributiveR) -> EndoBifunctorR rec.categoryR
  (.mulR) (MkDistributiveR {} {mul}) = MkBifunctorR mul

  ||| Convert this into a `CocartesianR` with the additive tensor product.
  public export %inline
  (.addCatR) : (rec : DistributiveR) -> CocartesianR
  (.addCatR) (MkDistributiveR {} {hom,add,zero}) = MkCocartesianR hom add zero

  ||| Convert this into a `CartesianR` with the multiplicative tensor product.
  public export %inline
  (.mulCatR) : (rec : DistributiveR) -> CartesianR
  (.mulCatR) (MkDistributiveR {} {hom,mul,one}) = MkCartesianR hom mul one


  ||| Convert this into a `BimonoidalR`.
  public export %inline
  (.bimonoidalR) : (rec : DistributiveR) -> BimonoidalR
  (.bimonoidalR) (MkDistributiveR hom add mul zero one) = MkBimonoidalR hom add mul zero one

  ||| The left distributor.
  public export %inline
  (.distribl) : (rec : DistributiveR) -> {a,b,c : _} ->
                rec.hom (rec.mul a (rec.add b c)) (rec.add (rec.mul a b) (rec.mul a c))
  (.distribl) rec@(MkDistributiveR {}) = rec.bimonoidalR.distribl

  ||| The inverse of `(.distribl)`, the left distributor.
  public export %inline
  (.distribl') : (rec : DistributiveR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a b) (rec.mul a c)) (rec.mul a (rec.add b c))
  (.distribl') rec@(MkDistributiveR {}) = rec.bimonoidalR.distribl'

  ||| The right distributor.
  public export %inline
  (.distribr) : (rec : DistributiveR) -> {a,b,c : _} ->
                rec.hom (rec.mul (rec.add a b) c) (rec.add (rec.mul a c) (rec.mul b c))
  (.distribr) rec@(MkDistributiveR {}) = rec.bimonoidalR.distribr

  ||| The inverse of `(.distribr)`, the right distributor.
  public export %inline
  (.distribr') : (rec : DistributiveR) -> {a,b,c : _} ->
                 rec.hom (rec.add (rec.mul a c) (rec.mul b c)) (rec.mul (rec.add a b) c)
  (.distribr') rec@(MkDistributiveR {}) = rec.bimonoidalR.distribr'

  ||| The left absorbor.
  public export %inline
  (.absorbl) : (rec : DistributiveR) -> {a : _} -> rec.hom (rec.mul a rec.zero) rec.zero
  (.absorbl) rec@(MkDistributiveR {}) = rec.bimonoidalR.absorbl

  ||| The inverse of `(.absorbl)`, the left absorbor.
  public export %inline
  (.absorbl') : (rec : DistributiveR) -> {a : _} -> rec.hom rec.zero (rec.mul a rec.zero)
  (.absorbl') rec@(MkDistributiveR {}) = rec.bimonoidalR.absorbl'

  ||| The right absorbor.
  public export %inline
  (.absorbr) : (rec : DistributiveR) -> {a : _} -> rec.hom (rec.mul rec.zero a) rec.zero
  (.absorbr) rec@(MkDistributiveR {}) = rec.bimonoidalR.absorbr

  ||| The inverse of `(.absorbr)`, the right absorbor.
  public export %inline
  (.absorbr') : (rec : DistributiveR) -> {a : _} -> rec.hom rec.zero (rec.mul rec.zero a)
  (.absorbr') rec@(MkDistributiveR {}) = rec.bimonoidalR.absorbr'

  ||| Convert this into a `RigCategoryR`.
  public export %inline
  (.rigCategoryR) : (rec : DistributiveR) -> RigCategoryR
  (.rigCategoryR) (MkDistributiveR hom add mul z i) = MkRigCategoryR hom add mul z i

  ||| Convert this into a `SymRigCategoryR`.
  public export %inline
  (.symRigCategoryR) : (rec : DistributiveR) -> SymRigCategoryR
  (.symRigCategoryR) (MkDistributiveR hom add mul z i) = MkSymRigCategoryR hom add mul z i


  ||| Convert this into a `DistributiveR`.
  public export %inline
  (.distributiveR) : (rec : DistributiveR) -> DistributiveR
  (.distributiveR) = id

  ||| The left projection of the product.
  public export %inline
  (.projl) : (rec : DistributiveR) -> {a,b : _} ->
             rec.hom (rec.mul a b) a
  (.projl) rec@(MkDistributiveR {}) = rec.mulCatR.projl

  ||| The right projection of the product.
  public export %inline
  (.projr) : (rec : DistributiveR) -> {a,b : _} ->
             rec.hom (rec.mul a b) b
  (.projr) rec@(MkDistributiveR {}) = rec.mulCatR.projr

  ||| The universal property of the product.
  public export %inline
  (.prod) : (rec : DistributiveR) -> {a,b,b' : _} ->
            rec.hom a b -> rec.hom a b' -> rec.hom a (rec.mul b b')
  (.prod) rec@(MkDistributiveR {}) = rec.mulCatR.prod

  ||| The cojoin of the universal comonoid structure.
  public export %inline
  (.split) : (rec : DistributiveR) -> {a : _} ->
             rec.hom a (rec.mul a a)
  (.split) rec@(MkDistributiveR {}) = rec.mulCatR.split

  ||| The counit of the universal comonoid structure.
  public export %inline
  (.elim) : (rec : DistributiveR) -> {a : _} ->
            rec.hom a rec.one
  (.elim) rec@(MkDistributiveR {}) = rec.mulCatR.elim

  ||| The left injection of the coproduct.
  public export %inline
  (.injl) : (rec : DistributiveR) -> {a,b : _} ->
            rec.hom a (rec.add a b)
  (.injl) rec@(MkDistributiveR {}) = rec.addCatR.injl

  ||| The right injection of the coproduct.
  public export %inline
  (.injr) : (rec : DistributiveR) -> {a,b : _} ->
            rec.hom b (rec.add a b)
  (.injr) rec@(MkDistributiveR {}) = rec.addCatR.injr

  ||| The universal property of the coproduct.
  public export %inline
  (.coprod) : (rec : DistributiveR) -> {a,a',b : _} ->
              rec.hom a b -> rec.hom a' b -> rec.hom (rec.add a a') b
  (.coprod) rec@(MkDistributiveR {}) = rec.addCatR.coprod

  ||| The join of the universal monoid structure.
  public export %inline
  (.merge) : (rec : DistributiveR) -> {a : _} ->
             rec.hom (rec.add a a) a
  (.merge) rec@(MkDistributiveR {}) = rec.addCatR.merge

  ||| The unit of the universal monoid structure.
  public export %inline
  (.intro) : (rec : DistributiveR) -> {a : _} ->
             rec.hom rec.zero a
  (.intro) rec@(MkDistributiveR {}) = rec.addCatR.intro
