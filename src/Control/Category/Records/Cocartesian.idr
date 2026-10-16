module Control.Category.Records.Cocartesian

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor
import Control.Category.Records.Monoidal
import Control.Category.Records.Braided
import Data.Morphisms

%default total
%prefix_record_projections off

||| A monoidal category is *cocartesian* if its tensor product
||| coincides with the categorical coproduct. This automatically
||| implies that it is symmetric (see `Braided`).
|||
||| See `Cocartesian` for required laws.
public export
record CocartesianR where
  constructor MkCocartesianR
  hom : Hom obj
  tensor : obj -> obj -> obj
  unit : obj
  {auto impl : Cocartesian hom tensor unit}

||| See `PreMonoidal`.
public export
PreCocartesianR : Type
PreCocartesianR = CocartesianR

namespace CocartesianR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : CocartesianR) -> CategoryR
  (.categoryR) (MkCocartesianR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : CocartesianR) -> {a : _} -> rec.hom a a
  (.id) (MkCocartesianR {}) = id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : CocartesianR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) (MkCocartesianR {}) = (.)


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : CocartesianR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkCocartesianR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : CocartesianR) -> MonoidalR
  (.monoidalR) (MkCocartesianR {} {hom,tensor,unit}) = MkMonoidalR hom tensor unit

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : CocartesianR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) (MkCocartesianR {}) = assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : CocartesianR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') (MkCocartesianR {}) = assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : CocartesianR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) (MkCocartesianR {}) = unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : CocartesianR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') (MkCocartesianR {}) = unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : CocartesianR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) (MkCocartesianR {}) = unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : CocartesianR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') (MkCocartesianR {}) = unitr'


  ||| Convert this into a `BraidedR`.
  public export %inline
  (.braidedR) : (rec : CocartesianR) -> BraidedR
  (.braidedR) (MkCocartesianR {} {hom,tensor,unit}) =
    MkBraidedR {hom,tensor,unit,impl = FromCocartesian}

  ||| Convert this into a `SymmetricR`.
  public export %inline
  (.symmetricR) : (rec : CocartesianR) -> SymmetricR
  (.symmetricR) (MkCocartesianR {} {hom,tensor,unit}) =
    MkSymmetricR {hom,tensor,unit,impl = FromCocartesian}

  ||| The braiding of the category.
  public export %inline
  (.braid) : (rec : CocartesianR) -> {a,b : _} ->
             rec.hom (rec.tensor a b) (rec.tensor b a)
  (.braid) (MkCocartesianR {}) = coprod injr injl


  ||| Convert this into a `CocartesianR`.
  public export %inline
  (.cocartesianR) : (rec : CocartesianR) -> CocartesianR
  (.cocartesianR) = id

  ||| The left injection of the coproduct.
  public export %inline
  (.injl) : (rec : CocartesianR) -> {a,b : _} ->
            rec.hom a (rec.tensor a b)
  (.injl) (MkCocartesianR {}) = injl

  ||| The right injection of the coproduct.
  public export %inline
  (.injr) : (rec : CocartesianR) -> {a,b : _} ->
            rec.hom b (rec.tensor a b)
  (.injr) (MkCocartesianR {}) = injr

  ||| The universal property of the coproduct.
  public export %inline
  (.coprod) : (rec : CocartesianR) -> {a,a',b : _} ->
            rec.hom a b -> rec.hom a' b -> rec.hom (rec.tensor a a') b
  (.coprod) (MkCocartesianR {}) = coprod

  ||| The join of the universal monoid structure.
  public export %inline
  (.merge) : (rec : CocartesianR) -> {a : _} ->
             rec.hom (rec.tensor a a) a
  (.merge) (MkCocartesianR {}) = merge

  ||| The unit of the universal monoid structure.
  public export %inline
  (.intro) : (rec : CocartesianR) -> {a : _} ->
             rec.hom rec.unit a
  (.intro) (MkCocartesianR {} {tensor}) = intro {ten=tensor}
