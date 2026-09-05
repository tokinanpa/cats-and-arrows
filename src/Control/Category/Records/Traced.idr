module Control.Category.Records.Traced

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor
import Control.Category.Records.Monoidal
import Data.Morphisms

%default total
%prefix_record_projections off

||| A *traced monoidal category* is a monoidal category equipped with
||| trace maps, maps which allow one to write loops in string diagrams.
||| The name "traced" comes from a connection to the trace of a matrix
||| in linear algebra, though the concept has far greater applications.
|||
||| See `Traced` for required laws.
public export
record TracedR where
  constructor MkTracedR
  hom : Hom obj
  tensor : obj -> obj -> obj
  unit : obj
  {auto impl : Traced hom tensor unit}

||| See `PreMonoidal`.
public export
PreTracedR : Type
PreTracedR = TracedR

namespace TracedR
  ||| Convert this into a `CategoryR`.
  public export %inline
  (.categoryR) : (rec : TracedR) -> CategoryR
  (.categoryR) (MkTracedR {} {hom}) = MkCategoryR hom

  ||| The identity morphism of an object `a`.
  public export %inline
  (.id) : (rec : TracedR) -> {a : _} -> rec.hom a a
  (.id) rec@(MkTracedR {}) = rec.categoryR.id

  ||| Binary right-to-left composition of morphisms.
  public export %inline
  (.comp) : (rec : TracedR) -> {a,b,c : _} ->
            rec.hom b c -> rec.hom a b -> rec.hom a c
  (.comp) rec@(MkTracedR {}) = rec.categoryR.comp


  ||| Return the tensor product as a `BifunctorR`.
  public export %inline
  (.tensorR) : (rec : TracedR) -> EndoBifunctorR rec.categoryR
  (.tensorR) (MkTracedR {} {tensor}) = MkBifunctorR tensor


  ||| Convert this into a `MonoidalR`.
  public export %inline
  (.monoidalR) : (rec : TracedR) -> MonoidalR
  (.monoidalR) (MkTracedR {} {hom,tensor,unit}) = MkMonoidalR hom tensor unit

  ||| The left-biased associator. This must be the inverse of `(.assoc')`.
  public export %inline
  (.assoc) : (rec : TracedR) -> {a,b,c : _} ->
             rec.hom (rec.tensor (rec.tensor a b) c) (rec.tensor a (rec.tensor b c))
  (.assoc) rec@(MkTracedR {}) = rec.monoidalR.assoc

  ||| The right-biased associator. This must be the inverse of `(.assoc)`.
  public export %inline
  (.assoc') : (rec : TracedR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a (rec.tensor b c)) (rec.tensor (rec.tensor a b) c)
  (.assoc') rec@(MkTracedR {}) = rec.monoidalR.assoc'

  ||| The left unitor.
  public export %inline
  (.unitl) : (rec : TracedR) -> {a : _} ->
             rec.hom (rec.tensor rec.unit a) a
  (.unitl) rec@(MkTracedR {}) = rec.monoidalR.unitl

  ||| The inverse of `(.unitl)`, the left unitor.
  public export %inline
  (.unitl') : (rec : TracedR) -> {a : _} ->
              rec.hom a (rec.tensor rec.unit a)
  (.unitl') rec@(MkTracedR {}) = rec.monoidalR.unitl'

  ||| The right unitor.
  public export %inline
  (.unitr) : (rec : TracedR) -> {a : _} ->
             rec.hom (rec.tensor a rec.unit) a
  (.unitr) rec@(MkTracedR {}) = rec.monoidalR.unitr

  ||| The inverse of `(.unitr)`, the right unitor.
  public export %inline
  (.unitr') : (rec : TracedR) -> {a : _} ->
              rec.hom a (rec.tensor a rec.unit)
  (.unitr') rec@(MkTracedR {}) = rec.monoidalR.unitr'


  ||| Convert this into a `TracedR`.
  public export %inline
  (.tracedR) : (rec : TracedR) -> TracedR
  (.tracedR) = id

  ||| The left trace.
  public export %inline
  (.tracel) : (rec : TracedR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a b) (rec.tensor a c) -> rec.hom b c
  (.tracel) rec = tracel @{rec.impl}

  ||| The right trace.
  public export %inline
  (.tracer) : (rec : TracedR) -> {a,b,c : _} ->
              rec.hom (rec.tensor a c) (rec.tensor b c) -> rec.hom a b
  (.tracer) rec = tracer @{rec.impl}

  ||| Take the trace of an endomorphism, returning an endomorphism in
  ||| the unit object. Depending on what the unit object is, this may
  ||| or may not actually be useful.
  |||
  ||| The name comes from the fact that in the monoidal category of
  ||| vector spaces, this takes a square matrix `M` to the 1x1 matrix
  ||| `[ tr(M) ]`.
  public export %inline
  (.trace) : (rec : TracedR) -> {a : _} ->
             rec.hom a a -> rec.hom rec.unit rec.unit
  (.trace) rec = trace @{rec.impl}
