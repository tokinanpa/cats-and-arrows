module Control.Category.Records.Category

import Control.Category
import Control.Category.Records.Semigroupoid

%default total
%prefix_record_projections off

||| A *category* is a generalized function type with a notion of
||| composition and of identity. The elements of this type are
||| typically called *morphisms*.
|||
||| See `Category` for required laws.
public export
record CategoryR where
  constructor MkCategoryR
  {obj : Type}
  hom : Hom obj
  {auto impl : Category hom}

namespace CategoryR
  ||| Convert this into a `SemigroupoidR`.
  public export %inline
  (.semigroupoidR) : (rec : CategoryR) -> SemigroupoidR
  (.semigroupoidR) (MkCategoryR {} {hom}) = MkSemigroupoidR hom {impl = FromCategory}


  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : CategoryR) -> CategoryR
  (.categoryR) = id

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : CategoryR) -> forall a. rec.hom a a
  (.id) rec = id @{rec.impl}

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : CategoryR) -> forall a,b,c.
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec = (.) @{rec.impl}
