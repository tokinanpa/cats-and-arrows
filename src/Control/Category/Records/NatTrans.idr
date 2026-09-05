module Control.Category.Records.NatTrans

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Functor

%default total
%prefix_record_projections off

||| A *natural transformation* is a kind of mapping between functors
||| that's compatible with their behavior.
|||
||| See `NatTrans` for required laws.
public export
record NatTransR (f,g : FunctorR cat cat') where
  constructor MkNatTransR
  fun : NatTrans cat'.hom f.fun g.fun

namespace NatTransR
  ||| The identity natural transformation.
  public export
  id : {cat' : _} -> {f : FunctorR cat cat'} ->
       NatTransR {cat'} f f
  id = MkNatTransR cat'.id

  ||| Binary right-to-left composition of natural transformations.
  public export
  (.) : {cat' : _} -> {f,g,h : FunctorR cat cat'} ->
        NatTransR g h -> NatTransR f g -> NatTransR f h
  MkNatTransR tr . MkNatTransR tr' = MkNatTransR (cat'.comp tr tr')
