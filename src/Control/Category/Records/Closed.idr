module Control.Category.Records.Closed

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor
import Control.Category.Records.Monoidal
import Control.Category.Records.Braided
import Control.Category.Records.Cartesian
import Data.Morphisms

%default total
%prefix_record_projections off

||| A monoidal category is *closed* if it can meaningfully represent
||| its morphisms as an object inside of itself. More specifically,
||| the internal hom `ihom a b` is an object that encodes the set of
||| morphisms from `a` to `b`.
|||
||| Formally, a monoidal category is closed if the functor
||| ``(`tensor` a)`` has a right adjoint functor `ihom a`.
|||
||| See `Closed` for required laws.
public export
record ClosedR where
  constructor MkClosedR
  {obj : Type}
  hom : Hom obj
  tensor, ihom : obj -> obj -> obj
  unit : obj
  {auto con : Closed hom tensor ihom unit}

namespace ClosedR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : ClosedR) -> CategoryR
  (.categoryR) (MkClosedR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : ClosedR) -> forall a. rec.hom a a
  (.id) rec@(MkClosedR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : ClosedR) -> forall a,b,c.
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkClosedR {}) = rec.categoryR.comp


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : ClosedR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkClosedR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : ClosedR) -> MonoidalR
  (.monoidalR) (MkClosedR {} {hom,tensor,unit}) = MkMonoidalR hom tensor unit

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : ClosedR) -> forall a,b,c.
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) rec@(MkClosedR {}) = rec.monoidalR.assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : ClosedR) -> forall a,b,c.
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') rec@(MkClosedR {}) = rec.monoidalR.assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : ClosedR) -> forall a.
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) rec@(MkClosedR {}) = rec.monoidalR.unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : ClosedR) -> forall a.
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') rec@(MkClosedR {}) = rec.monoidalR.unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : ClosedR) -> forall a.
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) rec@(MkClosedR {}) = rec.monoidalR.unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : ClosedR) -> forall a.
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') rec@(MkClosedR {}) = rec.monoidalR.unitr'


  ||| Convert this into a `ClosedR`.
  public export %inline
  (.closedR) : (rec : ClosedR) -> ClosedR
  (.closedR) = id

  ||| The currying transformation.
  public export %inline
  (.curry) : (rec : ClosedR) -> forall a,b,c.
             rec.hom (rec.tensor a b) c -> rec.hom a (rec.ihom b c)
  (.curry) rec = curry @{rec.con}

  ||| The uncurrying transformation.
  public export %inline
  (.uncurry) : (rec : ClosedR) -> forall a,b,c.
               rec.hom a (rec.ihom b c) -> rec.hom (rec.tensor a b) c
  (.uncurry) rec = uncurry @{rec.con}

  ||| The evaluation map.
  public export %inline
  (.eval) : (rec : ClosedR) -> forall a,b.
            rec.hom (rec.tensor (rec.ihom a b) a) b
  (.eval) rec = eval @{rec.con}

  ||| The coevaluation map.
  public export %inline
  (.coeval) : (rec : ClosedR) -> forall a,b.
            rec.hom a (rec.ihom b (rec.tensor a b))
  (.coeval) rec = coeval @{rec.con}


||| A monoidal category that is both cartesian and closed.
public export
record CartesianClosedR where
  constructor MkCartesianClosedR
  {obj : Type}
  hom : Hom obj
  tensor, ihom : obj -> obj -> obj
  unit : obj
  {auto con : (Cartesian hom tensor unit, Closed hom tensor ihom unit)}

||| A shorter synonym for a cartesian closed category (`CartesianClosedR`).
public export
CCC : Type
CCC = CartesianClosedR

namespace CartesianClosedR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : CartesianClosedR) -> CategoryR
  (.categoryR) (MkCartesianClosedR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : CartesianClosedR) -> forall a. rec.hom a a
  (.id) rec@(MkCartesianClosedR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : CartesianClosedR) -> forall a,b,c.
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkCartesianClosedR {}) = rec.categoryR.comp


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : CartesianClosedR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkCartesianClosedR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : CartesianClosedR) -> MonoidalR
  (.monoidalR) (MkCartesianClosedR {} {hom,tensor,unit}) = MkMonoidalR hom tensor unit

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : CartesianClosedR) -> forall a,b,c.
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) rec@(MkCartesianClosedR {}) = rec.monoidalR.assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : CartesianClosedR) -> forall a,b,c.
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') rec@(MkCartesianClosedR {}) = rec.monoidalR.assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : CartesianClosedR) -> forall a.
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) rec@(MkCartesianClosedR {}) = rec.monoidalR.unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : CartesianClosedR) -> forall a.
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') rec@(MkCartesianClosedR {}) = rec.monoidalR.unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : CartesianClosedR) -> forall a.
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) rec@(MkCartesianClosedR {}) = rec.monoidalR.unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : CartesianClosedR) -> forall a.
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') rec@(MkCartesianClosedR {}) = rec.monoidalR.unitr'


  ||| Convert this into a `BraidedR`.
  public export %inline
  (.braidedR) : (rec : CartesianClosedR) -> BraidedR
  (.braidedR) (MkCartesianClosedR {} {hom,tensor,unit}) =
    MkBraidedR {hom,tensor,unit,con = FromCartesian}

  ||| The braiding of the category.
  public export %inline
  (.braid) : (rec : CartesianClosedR) -> forall a,b.
             rec.hom (rec.tensor a b) (rec.tensor b a)
  (.braid) rec@(MkCartesianClosedR {}) = rec.braidedR.braid

  ||| The inverse of `(.braid)`, the braiding of the category.
  public export %inline
  (.braid') : (rec : CartesianClosedR) -> forall a,b.
              rec.hom (rec.tensor b a) (rec.tensor a b)
  (.braid') rec@(MkCartesianClosedR {}) = rec.braidedR.braid'


  ||| Convert this into a `CartesianR`.
  public export %inline
  (.cartesianR) : (rec : CartesianClosedR) -> CartesianR
  (.cartesianR) (MkCartesianClosedR {} {hom,tensor,unit}) = MkCartesianR {hom,tensor,unit}

  ||| The left projection of the product.
  public export %inline
  (.projl) : (rec : CartesianClosedR) -> forall a,b.
             rec.hom (rec.tensor a b) a
  (.projl) rec@(MkCartesianClosedR {}) = rec.cartesianR.projl

  ||| The right projection of the product.
  public export %inline
  (.projr) : (rec : CartesianClosedR) -> forall a,b.
             rec.hom (rec.tensor a b) b
  (.projr) rec@(MkCartesianClosedR {}) = rec.cartesianR.projr

  ||| The universal property of the product.
  public export %inline
  (.prod) : (rec : CartesianClosedR) -> forall a,b,b'.
            rec.hom a b -> rec.hom a b' -> rec.hom a (rec.tensor b b')
  (.prod) rec@(MkCartesianClosedR {}) = rec.cartesianR.prod

  ||| The cojoin of the universal comonoid structure.
  public export %inline
  (.split) : (rec : CartesianClosedR) -> forall a.
             rec.hom a (rec.tensor a a)
  (.split) rec@(MkCartesianClosedR {}) = rec.cartesianR.split

  ||| The counit of the universal comonoid structure.
  public export %inline
  (.elim) : (rec : CartesianClosedR) -> forall a.
            rec.hom a rec.unit
  (.elim) rec@(MkCartesianClosedR {}) = rec.cartesianR.elim


  ||| Convert this into a `ClosedR`.
  public export %inline
  (.closedR) : (rec : CartesianClosedR) -> ClosedR
  (.closedR) (MkCartesianClosedR {} {hom,tensor,ihom,unit}) =
    MkClosedR {hom,tensor,ihom,unit}

  ||| The currying transformation.
  public export %inline
  (.curry) : (rec : CartesianClosedR) -> forall a,b,c.
             rec.hom (rec.tensor a b) c -> rec.hom a (rec.ihom b c)
  (.curry) rec@(MkCartesianClosedR {}) = rec.closedR.curry

  ||| The uncurrying transformation.
  public export %inline
  (.uncurry) : (rec : CartesianClosedR) -> forall a,b,c.
               rec.hom a (rec.ihom b c) -> rec.hom (rec.tensor a b) c
  (.uncurry) rec@(MkCartesianClosedR {}) = rec.closedR.uncurry

  ||| The evaluation map.
  public export %inline
  (.eval) : (rec : CartesianClosedR) -> forall a,b.
            rec.hom (rec.tensor (rec.ihom a b) a) b
  (.eval) rec@(MkCartesianClosedR {}) = rec.closedR.eval

  ||| The coevaluation map.
  public export %inline
  (.coeval) : (rec : CartesianClosedR) -> forall a,b.
              rec.hom a (rec.ihom b (rec.tensor a b))
  (.coeval) rec@(MkCartesianClosedR {}) = rec.closedR.coeval
