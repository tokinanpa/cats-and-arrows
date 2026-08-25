module Control.Category.Records.Semigroupoid

import Control.Category

%default total
%prefix_record_projections off

||| A *semigroupoid* is a category that lacks identity morphisms.
|||
||| Laws:
||| * `(f . g) . h = f . (g . h)`
public export
record SemigroupoidR where
  constructor MkSemigroupoidR
  {obj : Type}
  hom : Hom obj
  {auto impl : Semigroupoid hom}

namespace SemigroupoidR
  ||| Convert this into a `SemigroupoidR`.
  public export %inline
  (.semigroupoidR) : (rec : SemigroupoidR) -> SemigroupoidR
  (.semigroupoidR) = id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : SemigroupoidR) -> forall a,b,c.
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec = (.) @{rec.impl}
