module Control.Category.Records.Braided

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor
import Control.Category.Records.Monoidal
import Data.Morphisms

%default total
%prefix_record_projections off

||| A monoidal category is *braided* when it is possible to flip the
||| order of the tensor product in a coherent way, determined by the
||| braiding isomorphism.
|||
||| See `Braided` for required laws.
public export
record BraidedR where
  constructor MkBraidedR
  hom : Hom obj
  tensor : obj -> obj -> obj
  unit : obj
  {auto impl : Braided hom tensor unit}

||| See `PreMonoidal`.
public export
PreBraidedR : Type
PreBraidedR = BraidedR

namespace BraidedR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : BraidedR) -> CategoryR
  (.categoryR) (MkBraidedR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : BraidedR) -> {a : _} -> rec.hom a a
  (.id) (MkBraidedR {}) = id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : BraidedR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) (MkBraidedR {}) = (.)


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : BraidedR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkBraidedR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : BraidedR) -> MonoidalR
  (.monoidalR) (MkBraidedR {} {hom,tensor,unit}) = MkMonoidalR hom tensor unit

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : BraidedR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) (MkBraidedR {}) = assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : BraidedR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') (MkBraidedR {}) = assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : BraidedR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) (MkBraidedR {}) = unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : BraidedR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') (MkBraidedR {}) = unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : BraidedR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) (MkBraidedR {}) = unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : BraidedR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') (MkBraidedR {}) = unitr'


  ||| Convert this into a `BraidedR`.
  public export %inline
  (.braidedR) : (rec : BraidedR) -> BraidedR
  (.braidedR) = id

  ||| The braiding of the category.
  public export %inline
  (.braid) : (rec : BraidedR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) (rec.tensor b a)
  (.braid) (MkBraidedR {}) = braid

  ||| The inverse of `(.braid)`, the braiding of the category.
  public export %inline
  (.braid') : (rec : BraidedR) -> {a,b : _} ->
              rec.hom (rec.tensor b a) (rec.tensor a b)
  (.braid') (MkBraidedR {}) = braid'

  ||| Invert the braiding of the monoidal category. If the braiding is
  ||| symmetric, this does nothing.
  public export
  (.flipBraid) : (rec : BraidedR) -> BraidedR
  (.flipBraid) (MkBraidedR hom ten i) =
    MkBraidedR hom ten i {impl = FlipBraid}


||| A monoidal category is *symmetric* when it has a braiding that is
||| equal to its own inverse.
|||
||| See `MonSymmetric` for required laws.
public export
record SymmetricR where
  constructor MkSymmetricR
  hom : Hom obj
  tensor : obj -> obj -> obj
  unit : obj
  {auto impl : MonSymmetric hom tensor unit}

||| See `PreMonoidal`.
public export
PreSymmetricR : Type
PreSymmetricR = SymmetricR

namespace SymmetricR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : SymmetricR) -> CategoryR
  (.categoryR) (MkSymmetricR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : SymmetricR) -> {a : _} -> rec.hom a a
  (.id) (MkSymmetricR {}) = id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : SymmetricR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) (MkSymmetricR {}) = (.)


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : SymmetricR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkSymmetricR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : SymmetricR) -> MonoidalR
  (.monoidalR) (MkSymmetricR {} {hom,tensor,unit}) = MkMonoidalR hom tensor unit

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : SymmetricR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) (MkSymmetricR {}) = assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : SymmetricR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') (MkSymmetricR {}) = assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : SymmetricR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) (MkSymmetricR {}) = unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : SymmetricR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') (MkSymmetricR {}) = unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : SymmetricR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) (MkSymmetricR {}) = unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : SymmetricR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') (MkSymmetricR {}) = unitr'


  ||| Convert this into a `BraidedR`.
  public export %inline
  (.braidedR) : (rec : SymmetricR) -> BraidedR
  (.braidedR) (MkSymmetricR {} {hom,tensor,unit}) = MkBraidedR hom tensor unit

  ||| The braiding of the category.
  public export %inline
  (.braid) : (rec : SymmetricR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) (rec.tensor b a)
  (.braid) (MkSymmetricR {}) = braid
