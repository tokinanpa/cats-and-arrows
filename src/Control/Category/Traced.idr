module Control.Category.Traced

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Data.Morphisms

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *traced monoidal category* is a monoidal category equipped with
||| trace maps, maps which allow one to write loops in string diagrams.
||| The name "traced" comes from a connection to the trace of a matrix
||| in linear algebra, though the concept has far greater applications.
|||
||| This is the interface-style definition of a traced monoidal category.
||| For the record-style definition, see `Control.Category.Records.TracedR`.
|||
||| Laws:
||| * `tracel (mapr f . g) = f . tracel g`
||| * `tracer (mapl f . g) = f . tracer g`
||| * `tracel (f . mapr g) = tracel f . g`
||| * `tracer (f . mapl g) = tracer f . g`
||| * `tracel (unitl' . f . unitl) = f`
||| * `tracer (unitr' . f . unitr) = f`
||| * `tracel (tracel f) . assoc = tracel f`
||| * `tracer (tracer f) . assoc' = tracer f`
||| * `assoc . tracer (bimap f g) = bimap f (tracer g)`
||| * `assoc' . tracel (bimap f g) = bimap (tracel f) g`
||| * `tracel f = tracer f` for all `f : cat a a`
|||
||| Note that these laws are for spherical traces, which are rather
||| restrictive. Some weaker versions of these laws may be appropriate
||| depending on the needs of the implementation.
public export
interface Monoidal cat ten i =>
    Traced (0 cat : Hom obj) (0 ten : obj -> obj -> obj) (0 i : obj) | cat,ten where
  constructor MkTraced
  ||| The left trace.
  tracel : forall a,b,c. cat (a `ten` b) (a `ten` c) -> cat b c
  ||| The right trace.
  tracer : forall a,b,c. cat (a `ten` c) (b `ten` c) -> cat a b

||| See `PreMonoidal`.
public export
PreTraced : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> Type
PreTraced = Traced


||| Take the trace of an endomorphism, returning an endomorphism in
||| the unit object. Depending on what the unit object is, this may
||| or may not actually be useful.
|||
||| The name comes from the fact that in the monoidal category of
||| vector spaces, this takes a square matrix `M` to the 1x1 matrix
||| `[ tr(M) ]`.
public export
trace : Traced cat ten i => cat a a -> cat i i
trace f = tracer $ unitl' {ten} . f . unitl
