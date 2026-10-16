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
  hom : Hom obj
  tensor, ihom : obj -> obj -> obj
  unit : obj
  {auto impl : Closed hom tensor ihom unit}

namespace ClosedR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : ClosedR) -> CategoryR
  (.categoryR) (MkClosedR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : ClosedR) -> {a : _} -> rec.hom a a
  (.id) (MkClosedR {}) = id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : ClosedR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) (MkClosedR {}) = (.)


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
  (.assoc) : (rec : ClosedR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) (MkClosedR {}) = assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : ClosedR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') (MkClosedR {}) = assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : ClosedR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) (MkClosedR {}) = unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : ClosedR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') (MkClosedR {}) = unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : ClosedR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) (MkClosedR {}) = unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : ClosedR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') (MkClosedR {}) = unitr'


  ||| Convert this into a `ClosedR`.
  public export %inline
  (.closedR) : (rec : ClosedR) -> ClosedR
  (.closedR) = id

  ||| The currying transformation.
  public export %inline
  (.curry) : (rec : ClosedR) -> {a,b,c : _} ->
             rec.hom (rec.tensor a b) c -> rec.hom a (rec.ihom b c)
  (.curry) (MkClosedR {}) = curry

  ||| The uncurrying transformation.
  public export %inline
  (.uncurry) : (rec : ClosedR) -> {a,b,c : _} ->
               rec.hom a (rec.ihom b c) -> rec.hom (rec.tensor a b) c
  (.uncurry) (MkClosedR {}) = uncurry

  ||| The evaluation map.
  public export %inline
  (.eval) : (rec : ClosedR) -> {a,b : _} ->
            rec.hom (rec.tensor (rec.ihom a b) a) b
  (.eval) (MkClosedR {}) = eval

  ||| The coevaluation map.
  public export %inline
  (.coeval) : (rec : ClosedR) -> {a,b : _} ->
            rec.hom a (rec.ihom b (rec.tensor a b))
  (.coeval) (MkClosedR {} {tensor}) = coeval {ten=tensor}


||| A monoidal category that is both cartesian and closed.
public export
record CartesianClosedR where
  constructor MkCartesianClosedR
  hom : Hom obj
  tensor, ihom : obj -> obj -> obj
  unit : obj
  {auto impl : CartesianClosed hom tensor ihom unit}

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
  (.id) : (rec : CartesianClosedR) -> {a : _} -> rec.hom a a
  (.id) (MkCartesianClosedR {}) = id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : CartesianClosedR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) (MkCartesianClosedR {}) = (.)


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
  (.assoc) : (rec : CartesianClosedR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) (MkCartesianClosedR {}) = assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : CartesianClosedR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') (MkCartesianClosedR {}) = assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : CartesianClosedR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) (MkCartesianClosedR {}) = unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : CartesianClosedR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') (MkCartesianClosedR {}) = unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : CartesianClosedR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) (MkCartesianClosedR {}) = unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : CartesianClosedR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') (MkCartesianClosedR {}) = unitr'


  ||| Convert this into a `BraidedR`.
  public export %inline
  (.braidedR) : (rec : CartesianClosedR) -> BraidedR
  (.braidedR) (MkCartesianClosedR {} {hom,tensor,unit}) =
    MkBraidedR {hom,tensor,unit,impl = FromCartesian}

  ||| Convert this into a `SymmetricR`.
  public export %inline
  (.symmetricR) : (rec : CartesianClosedR) -> SymmetricR
  (.symmetricR) (MkCartesianClosedR {} {hom,tensor,unit}) =
    MkSymmetricR {hom,tensor,unit,impl = FromCartesian}

  ||| The braiding of the category.
  public export %inline
  (.braid) : (rec : CartesianClosedR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) (rec.tensor b a)
  (.braid) (MkCartesianClosedR {}) = prod projr projl


  ||| Convert this into a `CartesianR`.
  public export %inline
  (.cartesianR) : (rec : CartesianClosedR) -> CartesianR
  (.cartesianR) (MkCartesianClosedR {} {hom,tensor,unit}) = MkCartesianR {hom,tensor,unit}

  ||| The left projection of the product.
  public export %inline
  (.projl) : (rec : CartesianClosedR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) a
  (.projl) (MkCartesianClosedR {}) = projl

  ||| The right projection of the product.
  public export %inline
  (.projr) : (rec : CartesianClosedR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) b
  (.projr) (MkCartesianClosedR {}) = projr

  ||| The universal property of the product.
  public export %inline
  (.prod) : (rec : CartesianClosedR) -> {a,b,b' : _} ->
            rec.hom a b -> rec.hom a b' -> rec.hom a (rec.tensor b b')
  (.prod) (MkCartesianClosedR {}) = prod

  ||| The cojoin of the universal comonoid structure.
  public export %inline
  (.split) : (rec : CartesianClosedR) -> {a : _} ->
             rec.hom a (rec.tensor a a)
  (.split) (MkCartesianClosedR {}) = split

  ||| The counit of the universal comonoid structure.
  public export %inline
  (.elim) : (rec : CartesianClosedR) -> {a : _} ->
            rec.hom a rec.unit
  (.elim) (MkCartesianClosedR {} {tensor}) = elim {ten=tensor}


  ||| Convert this into a `ClosedR`.
  public export %inline
  (.closedR) : (rec : CartesianClosedR) -> ClosedR
  (.closedR) (MkCartesianClosedR {} {hom,tensor,ihom,unit}) =
    MkClosedR {hom,tensor,ihom,unit}

  ||| The currying transformation.
  public export %inline
  (.curry) : (rec : CartesianClosedR) -> {a,b,c : _} ->
             rec.hom (rec.tensor a b) c -> rec.hom a (rec.ihom b c)
  (.curry) (MkCartesianClosedR {}) = curry

  ||| The uncurrying transformation.
  public export %inline
  (.uncurry) : (rec : CartesianClosedR) -> {a,b,c : _} ->
               rec.hom a (rec.ihom b c) -> rec.hom (rec.tensor a b) c
  (.uncurry) (MkCartesianClosedR {}) = uncurry

  ||| The evaluation map.
  public export %inline
  (.eval) : (rec : CartesianClosedR) -> {a,b : _} ->
            rec.hom (rec.tensor (rec.ihom a b) a) b
  (.eval) (MkCartesianClosedR {}) = eval

  ||| The coevaluation map.
  public export %inline
  (.coeval) : (rec : CartesianClosedR) -> {a,b : _} ->
              rec.hom a (rec.ihom b (rec.tensor a b))
  (.coeval) (MkCartesianClosedR {} {tensor}) = coeval {ten=tensor}
