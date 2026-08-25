module Control.Category.NatTrans

import Control.Category.Core

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *natural transformation* is a kind of mapping between functors
||| that's compatible with their behavior.
|||
||| This is the interface-style definition of a natural transformation.
||| For the record-style definition, see `Control.Category.Records.NatTransR`.
|||
||| Laws (for natural transformation `tr`):
||| * `map f . tr = tr . map f`
public export
0 NatTrans : (cat : Hom obj') -> (f,g : obj -> obj') -> Type
NatTrans cat f g = forall a. cat (f a) (g a)

