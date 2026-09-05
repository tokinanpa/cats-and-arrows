||| This module defines the category of categories, `Cat`, whose
||| morphisms are functors.
module Control.Category.Instances.Cat

import Control.Category
import Control.Category.Instances.One
import Control.Category.Instances.Prod
import Control.Category.Instances.FunCat
import Control.Category.Records
import Data.Wrap0

%default total

||| The category of categories.
public export
Cat : Hom CategoryR
Cat = FunctorR

||| The erased category of categories.
|||
||| This category is identical to `Cat`, except its category objects
||| are not required to exist at runtime. This makes it more efficient
||| at the cost of restricting its capabilities.
public export
record Cat0 (a,b : Wrap0 CategoryR) where
  constructor MkCat0
  runCat0 : Cat a.runW0 b.runW0

public export
Cat0_ : Hom CategoryR
Cat0_ a b = Cat0 (W0 a) (W0 b)


public export
Cat0Prod : Wrap0 CategoryR -> Wrap0 CategoryR -> Wrap0 CategoryR
Cat0Prod = liftW2 Prod


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

-- Cat

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

public export
Closed Cat Prod FunCat One where
  curry {a=a@(MkCategoryR{}),b=b@(MkCategoryR{}),c=MkCategoryR{}}
    f@(MkFunctorR {fun}) =
        MkFunctorR (\x => MkFunctorR (curry fun x)
                        {impl = MkCatFunctor $ \m => f.map (MkProd a.id m)})
        {impl = MkCatFunctor $ \m => MkNatTransR (f.map (MkProd m b.id))}
  uncurry {a=a@(MkCategoryR {}),b=b@(MkCategoryR {}),c=c@(MkCategoryR {})}
    f@(MkFunctorR {fun}) =
      let fn : (a.obj, b.obj) -> c.obj
          fn p = (fun $ fst p).fun $ snd p
          mp : {x,y : _} -> Prod a.hom b.hom x y -> c.hom (fn x) (fn y)
          mp {x=(_,_),y=(ya,_)} (MkProd m m') = c.comp ((fun ya).map m') (f.map m).fun
      in MkFunctorR fn {impl = MkCatFunctor mp}

-- Cat0

public export
Category Cat0 where
  id = MkCat0 $ MkFunctorR id {impl = Id}
  MkCat0 (MkFunctorR f {impl=fc}) . MkCat0(MkFunctorR g {impl=gc}) =
    MkCat0 (MkFunctorR (f . g) @{Compose @{fc} @{gc}})

public export %hint
SemigroupoidCat0 : Semigroupoid Cat0
SemigroupoidCat0 = FromCategory

public export
CatBifunctor Cat0 Cat0 Cat0 Cat0Prod where
  bimap (MkCat0 f) (MkCat0 g) = MkCat0 $ FunctorProd f g

public export
Monoidal Cat0 Cat0Prod (W0 One) where
  assoc {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ assoc_ {a,b,c}
    where
      assoc_ : forall a,b,c. Cat (Prod (Prod a b) c) (Prod a (Prod b c))
      assoc_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. ((a,b),c) -> (a,(b,c))
            fn p = (fst (fst p), (snd (fst p), snd p))
            mp : forall a,b,c. Prod (Prod a b) c x y -> Prod a (Prod b c) (fn x) (fn y)
            mp (MkProd (MkProd f g) h) = MkProd f (MkProd g h)
        in MkFunctorR fn {impl = MkCatFunctor mp}
  assoc' {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ assoc'_ {a,b,c}
    where
      assoc'_ : forall a,b,c. Cat (Prod a (Prod b c)) (Prod (Prod a b) c)
      assoc'_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. (a,(b,c)) -> ((a,b),c)
            fn p = ((fst p, fst (snd p)), snd (snd p))
            mp : forall a,b,c. Prod a (Prod b c) x y -> Prod (Prod a b) c (fn x) (fn y)
            mp (MkProd f (MkProd g h)) = MkProd (MkProd f g) h
        in MkFunctorR fn {impl = MkCatFunctor mp}
  unitl {a=W0 a} = MkCat0 $ unitl_ {a}
    where
      unitl_ : forall a. Cat (Prod One a) a
      unitl_ {a=MkCategoryR{}} = MkFunctorR snd {impl = MkCatFunctor snd}
  unitl' {a=W0 a} = MkCat0 $ unitl'_ {a}
    where
      unitl'_ : forall a. Cat a (Prod One a)
      unitl'_ {a=MkCategoryR{}} = MkFunctorR ((),) {impl = MkCatFunctor (MkProd MkOne)}
  unitr {a=W0 a} = MkCat0 $ unitr_ {a}
    where
      unitr_ : forall a. Cat (Prod a One) a
      unitr_ {a=MkCategoryR{}} = MkFunctorR fst {impl = MkCatFunctor fst}
  unitr' {a=W0 a} = MkCat0 $ unitr'_ {a}
    where
      unitr'_ : forall a. Cat a (Prod a One)
      unitr'_ {a=MkCategoryR{}} = MkFunctorR (,()) {impl = MkCatFunctor (`MkProd` MkOne)}

public export
Braided Cat0 Cat0Prod (W0 One) where
  braid {a=W0 a,b=W0 b} = MkCat0 $ braid_ {a,b}
    where
      braid_ : forall a,b. Cat (Prod a b) (Prod b a)
      braid_ {a=MkCategoryR{},b=MkCategoryR{}} =
        let mp : forall a,b. Prod a b x y -> Prod b a (swap x) (swap y)
            mp {x=(_,_),y=(_,_)} (MkProd f g) = MkProd g f
        in MkFunctorR swap {impl = MkCatFunctor mp}

public export
Cartesian Cat0 Cat0Prod (W0 One) where
  projl {a=W0 a,b=W0 b} = MkCat0 $ projl_ {a,b}
    where
      projl_ : forall a,b. Cat (Prod a b) a
      projl_ {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR fst {impl = MkCatFunctor fst}
  projr {a=W0 a,b=W0 b} = MkCat0 $ projr_ {a,b}
    where
      projr_ : forall a,b. Cat (Prod a b) b
      projr_ {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR snd {impl = MkCatFunctor snd}
  prod {a=W0 a,b=W0 b,b'=W0 b'} (MkCat0 f) (MkCat0 g) = MkCat0 $ prod_ {a,b,b'} f g
    where
      prod_ : forall a,b,b'. Cat a b -> Cat a b' -> Cat a (Prod b b')
      prod_ {a=MkCategoryR{},b=MkCategoryR{},b'=MkCategoryR{}}
        (MkFunctorR {fun=f}) (MkFunctorR {fun=g}) =
        MkFunctorR (\x => (f x, g x))
            {impl = MkCatFunctor $ \m => MkProd (map m) (map m)}



------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Cat : SemigroupoidR
  Cat = MkSemigroupoidR Cat

  public export
  Cat0 : SemigroupoidR
  Cat0 = MkSemigroupoidR Cat0

namespace CategoryR
  public export
  Cat : CategoryR
  Cat = MkCategoryR Cat

  public export
  Cat0 : CategoryR
  Cat0 = MkCategoryR Cat0

namespace MonoidalR
  public export
  Cat : MonoidalR
  Cat = MkMonoidalR Cat Prod One

  public export
  Cat0 : MonoidalR
  Cat0 = MkMonoidalR Cat0 Cat0Prod (W0 One)

namespace BraidedR
  public export
  Cat : BraidedR
  Cat = MkBraidedR Cat Prod One

  public export
  Cat0 : BraidedR
  Cat0 = MkBraidedR Cat0 Cat0Prod (W0 One)

namespace CartesianR
  public export
  Cat : CartesianR
  Cat = MkCartesianR Cat Prod One

  public export
  Cat0 : CartesianR
  Cat0 = MkCartesianR Cat0 Cat0Prod (W0 One)

namespace ClosedR
  public export
  Cat : ClosedR
  Cat = MkClosedR Cat Prod FunCat One

namespace CartesianClosedR
  public export
  Cat : CartesianClosedR
  Cat = MkCartesianClosedR Cat Prod FunCat One
