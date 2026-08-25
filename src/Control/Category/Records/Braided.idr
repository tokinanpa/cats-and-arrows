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
||| Additionally, a braided monoidal category may be *symmetric*,
||| requiring that `(.braid) = (.braid')`. Since the only difference
||| is in laws, the same record is used for this case.
|||
||| See `Braided` for required laws.
public export
record BraidedR where
  constructor MkBraidedR
  {obj : Type}
  hom : Hom obj
  tensor : obj -> obj -> obj
  unit : obj
  {auto con : Braided hom tensor unit}

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
  (.id) : (rec : BraidedR) -> forall a. rec.hom a a
  (.id) rec@(MkBraidedR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : BraidedR) -> forall a,b,c.
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkBraidedR {}) = rec.categoryR.comp


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
  (.assoc) : (rec : BraidedR) -> forall a,b,c.
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) rec@(MkBraidedR {}) = rec.monoidalR.assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : BraidedR) -> forall a,b,c.
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') rec@(MkBraidedR {}) = rec.monoidalR.assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : BraidedR) -> forall a.
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) rec@(MkBraidedR {}) = rec.monoidalR.unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : BraidedR) -> forall a.
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') rec@(MkBraidedR {}) = rec.monoidalR.unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : BraidedR) -> forall a.
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) rec@(MkBraidedR {}) = rec.monoidalR.unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : BraidedR) -> forall a.
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') rec@(MkBraidedR {}) = rec.monoidalR.unitr'


  ||| Convert this into a `BraidedR`.
  public export %inline
  (.braidedR) : (rec : BraidedR) -> BraidedR
  (.braidedR) = id

  ||| The braiding of the category.
  public export %inline
  (.braid) : (rec : BraidedR) -> forall a,b.
             rec.hom (rec.tensor a b) (rec.tensor b a)
  (.braid) rec = braid @{rec.con}

  ||| The inverse of `(.braid)`, the braiding of the category.
  public export %inline
  (.braid') : (rec : BraidedR) -> forall a,b.
              rec.hom (rec.tensor b a) (rec.tensor a b)
  (.braid') rec = braid' @{rec.con}

  ||| Invert the braiding of the monoidal category. If the braiding is
  ||| symmetric, this does nothing.
  public export
  (.flipBraid) : (rec : BraidedR) -> BraidedR
  (.flipBraid) (MkBraidedR hom ten i) =
    MkBraidedR hom ten i {con = FlipBraid}
