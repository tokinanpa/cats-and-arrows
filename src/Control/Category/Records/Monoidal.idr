module Control.Category.Records.Monoidal

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor
import Data.Morphisms

%default total
%prefix_record_projections off

||| A *monoidal category* is a category equipped with a binary operator
||| on its objects called the *tensor product* that respects its
||| internal structure. This operation is required to be a monoid,
||| that is to be associative and have an identity object (up to
||| isomorphism).
|||
||| See `Monoidal` for required laws.
public export
record MonoidalR where
  constructor MkMonoidalR
  hom : Hom obj
  tensor : obj -> obj -> obj
  unit : obj
  {auto impl : Monoidal hom tensor unit}

||| See `PreMonoidal`.
public export
PreMonoidalR : Type
PreMonoidalR = MonoidalR

namespace MonoidalR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : MonoidalR) -> CategoryR
  (.categoryR) (MkMonoidalR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : MonoidalR) -> {a : _} -> rec.hom a a
  (.id) rec@(MkMonoidalR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : MonoidalR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkMonoidalR {}) = rec.categoryR.comp


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : MonoidalR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkMonoidalR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : MonoidalR) -> MonoidalR
  (.monoidalR) = id

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : MonoidalR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) rec = assoc @{rec.impl}

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : MonoidalR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') rec = assoc' @{rec.impl}

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : MonoidalR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) rec = unitl @{rec.impl}

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : MonoidalR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') rec = unitl' @{rec.impl}

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : MonoidalR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) rec = unitr @{rec.impl}

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : MonoidalR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') rec = unitr' @{rec.impl}
