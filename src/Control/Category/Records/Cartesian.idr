module Control.Category.Records.Cartesian

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor
import Control.Category.Records.Monoidal
import Control.Category.Records.Braided
import Data.Morphisms

%default total
%prefix_record_projections off

||| A monoidal category is *cartesian* if its tensor product coincides
||| with the categorical product. This automatically implies that it
||| is symmetric (see `Braided`).
|||
||| See `Cartesian` for required laws.
public export
record CartesianR where
  constructor MkCartesianR
  hom : Hom obj
  tensor : obj -> obj -> obj
  unit : obj
  {auto impl : Cartesian hom tensor unit}

||| See `PreMonoidal`.
public export
PreCartesianR : Type
PreCartesianR = CartesianR

namespace CartesianR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : CartesianR) -> CategoryR
  (.categoryR) (MkCartesianR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : CartesianR) -> {a : _} -> rec.hom a a
  (.id) (MkCartesianR {}) = id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : CartesianR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) (MkCartesianR {}) = (.)


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : CartesianR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkCartesianR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : CartesianR) -> MonoidalR
  (.monoidalR) (MkCartesianR {} {hom,tensor,unit}) = MkMonoidalR hom tensor unit

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : CartesianR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) (MkCartesianR {}) = assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : CartesianR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') (MkCartesianR {}) = assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : CartesianR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) (MkCartesianR {}) = unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : CartesianR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') (MkCartesianR {}) = unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : CartesianR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) (MkCartesianR {}) = unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : CartesianR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') (MkCartesianR {}) = unitr'


  ||| Convert this into a `BraidedR`.
  public export %inline
  (.braidedR) : (rec : CartesianR) -> BraidedR
  (.braidedR) (MkCartesianR {} {hom,tensor,unit}) =
    MkBraidedR {hom,tensor,unit,impl = FromCartesian}

  ||| Convert this into a `SymmetricR`.
  public export %inline
  (.symmetricR) : (rec : CartesianR) -> SymmetricR
  (.symmetricR) (MkCartesianR {} {hom,tensor,unit}) =
    MkSymmetricR {hom,tensor,unit,impl = FromCartesian}

  ||| The braiding of the category.
  public export %inline
  (.braid) : (rec : CartesianR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) (rec.tensor b a)
  (.braid) (MkCartesianR {}) = prod projr projl


  ||| Convert this into a `CartesianR`.
  public export %inline
  (.cartesianR) : (rec : CartesianR) -> CartesianR
  (.cartesianR) = id

  ||| The left projection of the product.
  public export %inline
  (.projl) : (rec : CartesianR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) a
  (.projl) (MkCartesianR {}) = projl

  ||| The right projection of the product.
  public export %inline
  (.projr) : (rec : CartesianR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) b
  (.projr) (MkCartesianR {}) = projr

  ||| The universal property of the product.
  public export %inline
  (.prod) : (rec : CartesianR) -> {a,b,b' : _} ->
            rec.hom a b -> rec.hom a b' -> rec.hom a (rec.tensor b b')
  (.prod) (MkCartesianR {}) = prod

  ||| The cojoin of the universal comonoid structure.
  public export %inline
  (.split) : (rec : CartesianR) -> {a : _} ->
             rec.hom a (rec.tensor a a)
  (.split) (MkCartesianR {}) = split

  ||| The counit of the universal comonoid structure.
  public export %inline
  (.elim) : (rec : CartesianR) -> {a : _} ->
            rec.hom a rec.unit
  (.elim) (MkCartesianR {} {tensor}) = elim {ten=tensor}
