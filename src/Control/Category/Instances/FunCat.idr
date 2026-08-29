||| This module defines the functor category between two categories,
||| `FunCat C D`, traditionally written `[C, D]`. Its morphisms are
||| natural transformations between parallel functors.
module Control.Category.Instances.FunCat

import Control.Category
import Control.Category.Instances.One
import Control.Category.Instances.Prod
import Control.Category.Records

%default total

||| The functor category between `cat` and `cat'`.
|||
||| This category doesn't play very nicely with Idris's interface
||| resolution. Consider using the record-style definitions below.
public export
FunCat : (cat, cat' : CategoryR) -> Hom (FunctorR cat cat')
FunCat _ _ = NatTransR

public export
FunProd : {cat' : _} -> (ten : cat'.obj -> cat'.obj -> cat'.obj) -> CatEndoBifunctor cat'.hom ten =>
            (f,g : FunctorR cat cat') -> FunctorR cat cat'
FunProd {cat'=cat'@(MkCategoryR{})} ten f@(MkFunctorR _) g@(MkFunctorR _) =
  MkFunctorR (\x => ten (f.fun x) (g.fun x))
    {impl = MkCatFunctor $ \x => bimap (f.map x) (g.map x)}

public export
FunUnit : {cat' : _} -> (i : cat'.obj) -> FunctorR cat cat'
FunUnit i = MkFunctorR (const i) {impl = Const @{cat'.impl}}


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
{cat' : _} -> Category (FunCat cat cat') where
  id = NatTransR.id
  (.) = NatTransR.(.)

public export %hint
[BifunctorFunProd] {cat' : _} -> {0 ten : cat'.obj -> cat'.obj -> cat'.obj} ->
    CatBifunctor cat'.hom cat'.hom cat'.hom ten =>
    CatBifunctor (FunCat cat cat')
                 (FunCat cat cat')
                 (FunCat cat cat') (FunProd ten) where
  bimap {cat'=cat'@(MkCategoryR{}),
    a=MkFunctorR{},a'=MkFunctorR{},b=MkFunctorR{},b'=MkFunctorR{}}
    (MkNatTransR tr) (MkNatTransR tr') = MkNatTransR $ bimap tr tr'

public export %hint
MonoidalFunCat : {cat' : _} -> {0 ten : cat'.obj -> cat'.obj -> cat'.obj} -> {0 i : cat'.obj} ->
                  Monoidal cat'.hom ten i => Monoidal (FunCat cat cat') (FunProd ten) (FunUnit i)
MonoidalFunCat {cat'=cat'@(MkCategoryR{})} =
  MkMonoidal @{%search} @{BifunctorFunProd} assoc_ assoc'_ unitl_ unitl'_ unitr_ unitr'_
  where
    assoc_ : NatTransR {cat'} (FunProd ten (FunProd ten f g) h) (FunProd ten f (FunProd ten g h))
    assoc_ {f=MkFunctorR{},g=MkFunctorR{},h=MkFunctorR{}} = MkNatTransR assoc

    assoc'_ : NatTransR {cat'} (FunProd ten f (FunProd ten g h)) (FunProd ten (FunProd ten f g) h)
    assoc'_ {f=MkFunctorR{},g=MkFunctorR{},h=MkFunctorR{}} = MkNatTransR assoc'

    unitl_ : NatTransR {cat'} (FunProd ten (FunUnit i) f) f
    unitl_ {f=MkFunctorR{}} = MkNatTransR unitl

    unitl'_ : NatTransR {cat'} f (FunProd ten (FunUnit i) f)
    unitl'_ {f=MkFunctorR{}} = MkNatTransR unitl'

    unitr_ : NatTransR {cat'} (FunProd ten f (FunUnit i)) f
    unitr_ {f=MkFunctorR{}} = MkNatTransR unitr

    unitr'_ : NatTransR {cat'} f (FunProd ten f (FunUnit i))
    unitr'_ {f=MkFunctorR{}} = MkNatTransR unitr'

public export %hint
BraidedFunCat : {cat' : _} -> {0 ten : cat'.obj -> cat'.obj -> cat'.obj} -> {0 i : cat'.obj} ->
                  Braided cat'.hom ten i => Braided (FunCat cat cat') (FunProd ten) (FunUnit i)
BraidedFunCat {cat'=cat'@(MkCategoryR{})} = MkBraided @{MonoidalFunCat} braid_ braid'_
  where
    braid_ : NatTransR {cat'} (FunProd ten f g) (FunProd ten g f)
    braid_ {f=MkFunctorR{},g=MkFunctorR{}} = MkNatTransR braid

    braid'_ : NatTransR {cat'} (FunProd ten g f) (FunProd ten f g)
    braid'_ {f=MkFunctorR{},g=MkFunctorR{}} = MkNatTransR braid'

public export %hint
CartesianFunCat : {cat' : _} -> {0 ten : cat'.obj -> cat'.obj -> cat'.obj} -> {0 i : cat'.obj} ->
                  Cartesian cat'.hom ten i => Cartesian (FunCat cat cat') (FunProd ten) (FunUnit i)
CartesianFunCat {cat'=cat'@(MkCategoryR{})} = MkCartesian @{MonoidalFunCat} projl_ projr_ prod_ split_ elim_
  where
    projl_ : NatTransR {cat'} (FunProd ten f g) f
    projl_ {f=MkFunctorR{},g=MkFunctorR{}} = MkNatTransR projl

    projr_ : NatTransR {cat'} (FunProd ten f g) g
    projr_ {f=MkFunctorR{},g=MkFunctorR{}} = MkNatTransR projr

    prod_ : NatTransR {cat'} f g -> NatTransR f g' -> NatTransR f (FunProd ten g g')
    prod_ {f=MkFunctorR{},g=MkFunctorR{},g'=MkFunctorR{}} (MkNatTransR tr) (MkNatTransR tr') =
      MkNatTransR $ prod tr tr'

    split_ : NatTransR {cat'} f (FunProd ten f f)
    split_ {f=MkFunctorR{}} = MkNatTransR split

    elim_ : NatTransR {cat'} f (FunUnit i)
    elim_ {f=MkFunctorR{}} = MkNatTransR $ elim {ten}

public export %hint
CocartesianFunCat : {cat' : _} -> {0 ten : cat'.obj -> cat'.obj -> cat'.obj} -> {0 i : cat'.obj} ->
                    Cocartesian cat'.hom ten i => Cocartesian (FunCat cat cat') (FunProd ten) (FunUnit i)
CocartesianFunCat {cat'=cat'@(MkCategoryR{})} = MkCocartesian @{MonoidalFunCat} injl_ injr_ coprod_ merge_ intro_
  where
    injl_ : NatTransR {cat'} f (FunProd ten f g)
    injl_ {f=MkFunctorR{},g=MkFunctorR{}} = MkNatTransR injl

    injr_ : NatTransR {cat'} g (FunProd ten f g)
    injr_ {f=MkFunctorR{},g=MkFunctorR{}} = MkNatTransR injr

    coprod_ : NatTransR {cat'} f g -> NatTransR f' g -> NatTransR (FunProd ten f f') g
    coprod_ {f=MkFunctorR{},f'=MkFunctorR{},g=MkFunctorR{}} (MkNatTransR tr) (MkNatTransR tr') =
      MkNatTransR $ coprod tr tr'

    merge_ : NatTransR {cat'} (FunProd ten f f) f
    merge_ {f=MkFunctorR{}} = MkNatTransR merge

    intro_ : NatTransR {cat'} (FunUnit i) f
    intro_ {f=MkFunctorR{}} = MkNatTransR $ intro {ten}

public export %hint
TracedFunCat : {cat' : _} -> {0 ten : cat'.obj -> cat'.obj -> cat'.obj} -> {0 i : cat'.obj} ->
               Traced cat'.hom ten i => Traced (FunCat cat cat') (FunProd ten) (FunUnit i)
TracedFunCat {cat'=cat'@(MkCategoryR{})} = MkTraced @{MonoidalFunCat} tracel_ tracer_
  where
    tracel_ : NatTransR {cat'} (FunProd ten f g) (FunProd ten f h) -> NatTransR g h
    tracel_ {f=MkFunctorR{},g=MkFunctorR{},h=MkFunctorR{}} (MkNatTransR tr) = MkNatTransR $ tracel tr

    tracer_ : NatTransR {cat'} (FunProd ten f h) (FunProd ten g h) -> NatTransR f g
    tracer_ {f=MkFunctorR{},g=MkFunctorR{},h=MkFunctorR{}} (MkNatTransR tr) = MkNatTransR $ tracer tr


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace CategoryR
  public export
  FunCat : (cat,cat' : CategoryR) -> CategoryR
  FunCat cat cat' = MkCategoryR (FunCat cat cat')

namespace MonoidalR
  public export
  FunCat : (cat : CategoryR) -> (cat' : MonoidalR) -> MonoidalR
  FunCat cat cat'@(MkMonoidalR {}) =
    MkMonoidalR (FunCat cat cat'.categoryR) (FunProd cat'.tensor) (FunUnit cat'.unit)
      {impl = MonoidalFunCat}

namespace BraidedR
  public export
  FunCat : (cat : CategoryR) -> (cat' : BraidedR) -> BraidedR
  FunCat cat cat'@(MkBraidedR {}) =
    MkBraidedR (FunCat cat cat'.categoryR) (FunProd cat'.tensor) (FunUnit cat'.unit)
      {impl = BraidedFunCat}

namespace CartesianR
  public export
  FunCat : (cat : CategoryR) -> (cat' : CartesianR) -> CartesianR
  FunCat cat cat'@(MkCartesianR {}) =
    MkCartesianR (FunCat cat cat'.categoryR) (FunProd cat'.tensor) (FunUnit cat'.unit)
      {impl = CartesianFunCat}

namespace CocartesianR
  public export
  FunCat : (cat : CategoryR) -> (cat' : CocartesianR) -> CocartesianR
  FunCat cat cat'@(MkCocartesianR {}) =
    MkCocartesianR (FunCat cat cat'.categoryR) (FunProd cat'.tensor) (FunUnit cat'.unit)
      {impl = CocartesianFunCat}

namespace TracedR
  public export
  FunCat : (cat : CategoryR) -> (cat' : TracedR) -> TracedR
  FunCat cat cat'@(MkTracedR {}) =
    MkTracedR (FunCat cat cat'.categoryR) (FunProd cat'.tensor) (FunUnit cat'.unit)
      {impl = TracedFunCat}
