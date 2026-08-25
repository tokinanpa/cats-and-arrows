||| This module defines the category of categories, `Cat`, whose
||| morphisms are functors.
module Control.Category.Instances.Cat

import Control.Category
import Control.Category.Instances.One
import Control.Category.Instances.Prod
import Control.Category.Instances.FunCat
import Control.Category.Records

%default total

||| The category of categories.
public export
Cat : Hom CategoryR
Cat = FunctorR


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Category Cat where
  id = MkFunctorR id {impl = Id}
  MkFunctorR f {impl=fc} . MkFunctorR g {impl=gc} =
    MkFunctorR (f . g) @{Compose @{fc} @{gc}}

public export %hint
SemigroupoidCat : Semigroupoid Cat
SemigroupoidCat = FromCategory

public export
CatBifunctor Cat Cat Cat Prod where
  bimap = FunctorProd

public export
Monoidal Cat Prod One where
  assoc {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : ((a,b),c) -> (a,(b,c))
        fn p = (fst (fst p), (snd (fst p), snd p))
        mp : Prod (Prod a b) c x y -> Prod a (Prod b c) (fn x) (fn y)
        mp (MkProd (MkProd f g) h) = MkProd f (MkProd g h)
    in MkFunctorR fn {impl = MkCatFunctor mp}
  assoc' {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : (a,(b,c)) -> ((a,b),c)
        fn p = ((fst p, fst (snd p)), snd (snd p))
        mp : Prod a (Prod b c) x y -> Prod (Prod a b) c (fn x) (fn y)
        mp (MkProd f (MkProd g h)) = MkProd (MkProd f g) h
    in MkFunctorR fn {impl = MkCatFunctor mp}
  unitl {a=MkCategoryR{}} = MkFunctorR snd {impl = MkCatFunctor snd}
  unitl' {a=MkCategoryR{}} = MkFunctorR ((),) {impl = MkCatFunctor (MkProd MkOne)}
  unitr {a=MkCategoryR{}} = MkFunctorR fst {impl = MkCatFunctor fst}
  unitr' {a=MkCategoryR{}} = MkFunctorR (,()) {impl = MkCatFunctor (`MkProd` MkOne)}

public export
Braided Cat Prod One where
  braid {a=MkCategoryR{},b=MkCategoryR{}} =
    let mp : Prod a b x y -> Prod b a (swap x) (swap y)
        mp {x=(_,_),y=(_,_)} (MkProd f g) = MkProd g f
    in MkFunctorR swap {impl = MkCatFunctor mp}

public export
Cartesian Cat Prod One where
  projl {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR fst {impl = MkCatFunctor fst}
  projr {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR snd {impl = MkCatFunctor snd}
  prod {a=MkCategoryR{},b=MkCategoryR{},b'=MkCategoryR{}}
    (MkFunctorR {fun=f}) (MkFunctorR {fun=g}) =
      MkFunctorR (\x => (f x, g x))
        {impl = MkCatFunctor $ \m => MkProd (map m) (map m)}

-- We unfortunately can't properly prove that Cat is closed
-- due to runtime multiplicity issues. Here's an erased proof.

public export
curry : {a,b : _} -> Cat (Prod a b) c -> Cat a (FunCat b c)
curry {a=a@(MkCategoryR{}),b=b@(MkCategoryR{}),c=MkCategoryR{}}
  f@(MkFunctorR {fun}) =
    MkFunctorR (\x => MkFunctorR (curry fun x)
                      {impl = MkCatFunctor $ \m => f.map (MkProd a.id m)})
      {impl = MkCatFunctor $ \m => MkNatTransR (f.map (MkProd m b.id))}

public export
0 uncurry : Cat a (FunCat b c) -> Cat (Prod a b) c
uncurry {a=a@(MkCategoryR {}),b=b@(MkCategoryR {}),c=c@(MkCategoryR {})}
  f@(MkFunctorR {fun}) =
    let fn : (a.obj, b.obj) -> c.obj
        fn p = (fun $ fst p).fun $ snd p
        mp : Prod a.hom b.hom x y -> c.hom (fn x) (fn y)
        mp {x=(_,_),y=(ya,_)} (MkProd m m') = c.comp ((fun ya).map m') (f.map m).fun
    in MkFunctorR fn {impl = MkCatFunctor mp}

public export
0 CatClosed : Closed Cat Prod FunCat One
CatClosed = MkClosed curry uncurry


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Cat : SemigroupoidR
  Cat = MkSemigroupoidR Cat

namespace CategoryR
  public export
  Cat : CategoryR
  Cat = MkCategoryR Cat

namespace MonoidalR
  public export
  Cat : MonoidalR
  Cat = MkMonoidalR Cat Prod One

namespace BraidedR
  public export
  Cat : BraidedR
  Cat = MkBraidedR Cat Prod One

namespace CartesianR
  public export
  Cat : CartesianR
  Cat = MkCartesianR Cat Prod One

namespace ClosedR
  public export
  0 Cat : ClosedR
  Cat = MkClosedR Cat Prod FunCat One {impl = CatClosed}

namespace CartesianClosedR
  public export
  0 Cat : CartesianClosedR
  Cat = MkCartesianClosedR Cat Prod FunCat One {impl = (%search, CatClosed)}
