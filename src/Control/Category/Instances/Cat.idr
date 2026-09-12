||| This module defines the category of categories, `Cat`, whose
||| morphisms are functors.
module Control.Category.Instances.Cat

import Control.Category
import Control.Category.Instances.Zero
import Control.Category.Instances.One
import Control.Category.Instances.Sum
import Control.Category.Instances.Prod
import Control.Category.Instances.FunCat
import Control.Category.Records
import Data.Either
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

public export
Cat0Sum : Wrap0 CategoryR -> Wrap0 CategoryR -> Wrap0 CategoryR
Cat0Sum = liftW2 Sum


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
CatBifunctor Cat Cat Cat Sum where
  bimap = FunctorSum

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
Monoidal Cat Sum Zero where
  assoc {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : Either (Either a b) c -> Either a (Either b c)
        fn (Left (Left x)) = Left x
        fn (Left (Right x)) = Right (Left x)
        fn (Right x) = Right (Right x)
        mp : Sum (Sum a b) c x y -> Sum a (Sum b c) (fn x) (fn y)
        mp (Left (Left f)) = Left f
        mp (Left (Right f)) = Right (Left f)
        mp (Right f) = Right (Right f)
    in MkFunctorR fn {impl = MkCatFunctor mp}
  assoc' {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : Either a (Either b c) -> Either (Either a b) c
        fn (Left x) = Left (Left x)
        fn (Right (Left x)) = Left (Right x)
        fn (Right (Right x)) = Right x
        mp : Sum a (Sum b c) x y -> Sum (Sum a b) c (fn x) (fn y)
        mp (Left f) = Left (Left f)
        mp (Right (Left f)) = Left (Right f)
        mp (Right (Right f)) = Right f
    in MkFunctorR fn {impl = MkCatFunctor mp}
  unitl {a=MkCategoryR{}} =
    let fn : Either Void a -> a
        fn = either absurd id
        mp : Sum Zero a x y -> a (fn x) (fn y)
        mp (Left _) impossible
        mp (Right f) = f
    in MkFunctorR fn {impl = MkCatFunctor mp}
  unitl' {a=MkCategoryR{}} = MkFunctorR Right {impl = MkCatFunctor Right}
  unitr {a=MkCategoryR{}} =
    let fn : Either a Void -> a
        fn = either id absurd
        mp : Sum a Zero x y -> a (fn x) (fn y)
        mp (Left f) = f
        mp (Right _) impossible
    in MkFunctorR fn {impl = MkCatFunctor mp}
  unitr' {a=MkCategoryR{}} = MkFunctorR Left {impl = MkCatFunctor Left}

public export
Braided Cat Prod One where
  braid {a=MkCategoryR{},b=MkCategoryR{}} =
    let mp : Prod a b x y -> Prod b a (swap x) (swap y)
        mp {x=(_,_),y=(_,_)} (MkProd f g) = MkProd g f
    in MkFunctorR swap {impl = MkCatFunctor mp}

public export
Braided Cat Sum Zero where
  braid {a=MkCategoryR{},b=MkCategoryR{}} =
    let mp : Sum a b x y -> Sum b a (mirror x) (mirror y)
        mp (Left f) = Right f
        mp (Right f) = Left f
    in MkFunctorR mirror {impl = MkCatFunctor mp}

public export
Cartesian Cat Prod One where
  projl {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR fst {impl = MkCatFunctor fst}
  projr {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR snd {impl = MkCatFunctor snd}
  prod {a=MkCategoryR{},b=MkCategoryR{},b'=MkCategoryR{}}
    (MkFunctorR {fun=f}) (MkFunctorR {fun=g}) =
      MkFunctorR (\x => (f x, g x))
        {impl = MkCatFunctor $ \m => MkProd (map m) (map m)}
  split {a=MkCategoryR{}} =
    MkFunctorR dup {impl = MkCatFunctor $ \f => MkProd f f}
  elim {a=MkCategoryR{}} =
    MkFunctorR (const ()) {impl = MkCatFunctor $ const MkOne}

public export
Cocartesian Cat Sum Zero where
  injl {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR Left {impl = MkCatFunctor Left}
  injr {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR Right {impl = MkCatFunctor Right}
  coprod {a=MkCategoryR{},a'=MkCategoryR{},b=MkCategoryR{}}
    (MkFunctorR {fun=f}) (MkFunctorR {fun=g}) =
      MkFunctorR (either f g)
        {impl = MkCatFunctor $ \case
          Left f => map f
          Right f => map f}
  merge {a=MkCategoryR{}} =
    MkFunctorR fromEither {impl = MkCatFunctor $ \case
      Left f => f
      Right f => f}
  intro {a=MkCategoryR{}} = MkFunctorR absurd {impl = MkCatFunctor absurd}

public export
Bimonoidal Cat Sum Prod Zero One where
  distribl {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : (a, Either b c) -> Either (a,b) (a,c)
        fn (x,y) = bimap (x,) (x,) y
        mp : {x,y : _} -> Prod a (Sum b c) x y -> Sum (Prod a b) (Prod a c) (fn x) (fn y)
        mp {x=(_,Left _),y=(_,Left _)} (MkProd f (Left g)) = Left (MkProd f g)
        mp {x=(_,Prelude.Left _),y=(_,Prelude.Right _)} (MkProd _ _) impossible
        mp {x=(_,Right _),y=(_,Right _)} (MkProd f (Right g)) = Right (MkProd f g)
        mp {x=(_,Prelude.Right _),y=(_,Prelude.Left _)} (MkProd _ _) impossible
    in MkFunctorR fn {impl = MkCatFunctor mp}
  distribl' {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : Either (a,b) (a,c) -> (a, Either b c)
        fn = either (mapSnd Left) (mapSnd Right)
        mp : Sum (Prod a b) (Prod a c) x y -> Prod a (Sum b c) (fn x) (fn y)
        mp {x=Left (_,_),y=Left (_,_)} (Left (MkProd f g)) = MkProd f (Left g)
        mp {x=Right (_,_),y=Right (_,_)} (Right (MkProd f g)) = MkProd f (Right g)
    in MkFunctorR fn {impl = MkCatFunctor mp}
  distribr {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : (Either a b, c) -> Either (a,c) (b,c)
        fn (x,y) = bimap (,y) (,y) x
        mp : {x,y : _} -> Prod (Sum a b) c x y -> Sum (Prod a c) (Prod b c) (fn x) (fn y)
        mp {x=(Left _,_),y=(Left _,_)} (MkProd (Left f) g) = Left (MkProd f g)
        mp {x=(Prelude.Left _,_),y=(Prelude.Right _,_)} (MkProd _ _) impossible
        mp {x=(Right _,_),y=(Right _,_)} (MkProd (Right f) g) = Right (MkProd f g)
        mp {x=(Prelude.Right _,_),y=(Prelude.Left _,_)} (MkProd _ _) impossible
    in MkFunctorR fn {impl = MkCatFunctor mp}
  distribr' {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
    let fn : Either (a,c) (b,c) -> (Either a b, c)
        fn = either (mapFst Left) (mapFst Right)
        mp : Sum (Prod a c) (Prod b c) x y -> Prod (Sum a b) c (fn x) (fn y)
        mp {x=Left (_,_),y=Left (_,_)} (Left (MkProd f g)) = MkProd (Left f) g
        mp {x=Right (_,_),y=Right (_,_)} (Right (MkProd f g)) = MkProd (Right f) g
    in MkFunctorR fn {impl = MkCatFunctor mp}
  absorbl {a=MkCategoryR{}} = MkFunctorR snd {impl = MkCatFunctor snd}
  absorbl' {a=MkCategoryR{}} = MkFunctorR absurd {impl = MkCatFunctor absurd}
  absorbr {a=MkCategoryR{}} = MkFunctorR fst {impl = MkCatFunctor fst}
  absorbr' {a=MkCategoryR{}} = MkFunctorR absurd {impl = MkCatFunctor absurd}

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
CatBifunctor Cat0 Cat0 Cat0 Cat0Sum where
  bimap (MkCat0 f) (MkCat0 g) = MkCat0 $ FunctorSum f g

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
Monoidal Cat0 Cat0Sum (W0 Zero) where
  assoc {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ assoc_ {a,b,c}
    where
      assoc_ : forall a,b,c. Cat (Sum (Sum a b) c) (Sum a (Sum b c))
      assoc_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. Either (Either a b) c -> Either a (Either b c)
            fn (Left (Left x)) = Left x
            fn (Left (Right x)) = Right (Left x)
            fn (Right x) = Right (Right x)
            mp : forall a,b,c. Sum (Sum a b) c x y -> Sum a (Sum b c) (fn x) (fn y)
            mp (Left (Left f)) = Left f
            mp (Left (Right f)) = Right (Left f)
            mp (Right f) = Right (Right f)
        in MkFunctorR fn {impl = MkCatFunctor mp}
  assoc' {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ assoc'_ {a,b,c}
    where
      assoc'_ : forall a,b,c. Cat (Sum a (Sum b c)) (Sum (Sum a b) c)
      assoc'_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. Either a (Either b c) -> Either (Either a b) c
            fn (Left x) = Left (Left x)
            fn (Right (Left x)) = Left (Right x)
            fn (Right (Right x)) = Right x
            mp : forall a,b,c. Sum a (Sum b c) x y -> Sum (Sum a b) c (fn x) (fn y)
            mp (Left f) = Left (Left f)
            mp (Right (Left f)) = Left (Right f)
            mp (Right (Right f)) = Right f
        in MkFunctorR fn {impl = MkCatFunctor mp}
  unitl {a=W0 a} = MkCat0 $ unitl_ {a}
    where
      unitl_ : forall a. Cat (Sum Zero a) a
      unitl_ {a=MkCategoryR{}} =
        let fn : forall a. Either Void a -> a
            fn = either absurd id
            mp : forall a. Sum Zero a x y -> a (fn x) (fn y)
            mp (Left _) impossible
            mp (Right f) = f
        in MkFunctorR fn {impl = MkCatFunctor mp}
  unitl' {a=W0 a} = MkCat0 $ unitl'_ {a}
    where
      unitl'_ : forall a. Cat a (Sum Zero a)
      unitl'_ {a=MkCategoryR{}} = MkFunctorR Right {impl = MkCatFunctor Right}
  unitr {a=W0 a} = MkCat0 $ unitr_ {a}
    where
      unitr_ : forall a. Cat (Sum a Zero) a
      unitr_ {a=MkCategoryR{}} =
        let fn : forall a. Either a Void -> a
            fn = either id absurd
            mp : forall a. Sum a Zero x y -> a (fn x) (fn y)
            mp (Left f) = f
            mp (Right _) impossible
        in MkFunctorR fn {impl = MkCatFunctor mp}
  unitr' {a=W0 a} = MkCat0 $ unitr'_ {a}
    where
      unitr'_ : forall a. Cat a (Sum a Zero)
      unitr'_ {a=MkCategoryR{}} = MkFunctorR Left {impl = MkCatFunctor Left}

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
Braided Cat0 Cat0Sum (W0 Zero) where
  braid {a=W0 a,b=W0 b} = MkCat0 $ braid_ {a,b}
    where
      braid_ : forall a,b. Cat (Sum a b) (Sum b a)
      braid_ {a=MkCategoryR{},b=MkCategoryR{}} =
        let mp : forall a,b. Sum a b x y -> Sum b a (mirror x) (mirror y)
            mp (Left f) = Right f
            mp (Right f) = Left f
        in MkFunctorR mirror {impl = MkCatFunctor mp}

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

public export
Cocartesian Cat0 Cat0Sum (W0 Zero) where
  injl {a=W0 a,b=W0 b} = MkCat0 $ injl_ {a,b}
    where
      injl_ : forall a,b. Cat a (Sum a b)
      injl_ {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR Left {impl = MkCatFunctor Left}
  injr {a=W0 a,b=W0 b} = MkCat0 $ injr_ {a,b}
    where
      injr_ : forall a,b. Cat b (Sum a b)
      injr_ {a=MkCategoryR{},b=MkCategoryR{}} = MkFunctorR Right {impl = MkCatFunctor Right}
  coprod {a=W0 a,a'=W0 a',b=W0 b} (MkCat0 f) (MkCat0 g) = MkCat0 $ coprod_ f g
    where
      coprod_ : forall a,a',b. Cat a b -> Cat a' b -> Cat (Sum a a') b
      coprod_ {a=MkCategoryR{},a'=MkCategoryR{},b=MkCategoryR{}}
        (MkFunctorR {fun=f}) (MkFunctorR {fun=g}) =
          MkFunctorR (either f g)
            {impl = MkCatFunctor $ \case
              Left f => map f
              Right f => map f}

public export
Bimonoidal Cat0 Cat0Sum Cat0Prod (W0 Zero) (W0 One) where
  distribl {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ distribl_ {a,b,c}
    where
      distribl_ : forall a,b,c. Cat (Prod a (Sum b c)) (Sum (Prod a b) (Prod a c))
      distribl_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. (a, Either b c) -> Either (a,b) (a,c)
            fn (x,y) = bimap (x,) (x,) y
            mp : {x,y : _} -> forall a,b,c. Prod a (Sum b c) x y -> Sum (Prod a b) (Prod a c) (fn x) (fn y)
            mp {x=(_,Left _),y=(_,Left _)} (MkProd f (Left g)) = Left (MkProd f g)
            mp {x=(_,Prelude.Left _),y=(_,Prelude.Right _)} (MkProd _ _) impossible
            mp {x=(_,Right _),y=(_,Right _)} (MkProd f (Right g)) = Right (MkProd f g)
            mp {x=(_,Prelude.Right _),y=(_,Prelude.Left _)} (MkProd _ _) impossible
        in MkFunctorR fn {impl = MkCatFunctor mp}
  distribl' {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ distribl'_ {a,b,c}
    where
      distribl'_ : forall a,b,c. Cat (Sum (Prod a b) (Prod a c)) (Prod a (Sum b c))
      distribl'_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. Either (a,b) (a,c) -> (a, Either b c)
            fn = either (mapSnd Left) (mapSnd Right)
            mp : forall a,b,c. Sum (Prod a b) (Prod a c) x y -> Prod a (Sum b c) (fn x) (fn y)
            mp {x=Left (_,_),y=Left (_,_)} (Left (MkProd f g)) = MkProd f (Left g)
            mp {x=Right (_,_),y=Right (_,_)} (Right (MkProd f g)) = MkProd f (Right g)
        in MkFunctorR fn {impl = MkCatFunctor mp}
  distribr {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ distribr_ {a,b,c}
    where
      distribr_ : forall a,b,c. Cat (Prod (Sum a b) c) (Sum (Prod a c) (Prod b c))
      distribr_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. (Either a b, c) -> Either (a,c) (b,c)
            fn (x,y) = bimap (,y) (,y) x
            mp : {x,y : _} -> forall a,b,c. Prod (Sum a b) c x y -> Sum (Prod a c) (Prod b c) (fn x) (fn y)
            mp {x=(Left _,_),y=(Left _,_)} (MkProd (Left f) g) = Left (MkProd f g)
            mp {x=(Prelude.Left _,_),y=(Prelude.Right _,_)} (MkProd _ _) impossible
            mp {x=(Right _,_),y=(Right _,_)} (MkProd (Right f) g) = Right (MkProd f g)
            mp {x=(Prelude.Right _,_),y=(Prelude.Left _,_)} (MkProd _ _) impossible
        in MkFunctorR fn {impl = MkCatFunctor mp}
  distribr' {a=W0 a,b=W0 b,c=W0 c} = MkCat0 $ distribr'_ {a,b,c}
    where
      distribr'_ : forall a,b,c. Cat (Sum (Prod a c) (Prod b c)) (Prod (Sum a b) c)
      distribr'_ {a=MkCategoryR{},b=MkCategoryR{},c=MkCategoryR{}} =
        let fn : forall a,b,c. Either (a,c) (b,c) -> (Either a b, c)
            fn = either (mapFst Left) (mapFst Right)
            mp : forall a,b,c. Sum (Prod a c) (Prod b c) x y -> Prod (Sum a b) c (fn x) (fn y)
            mp {x=Left (_,_),y=Left (_,_)} (Left (MkProd f g)) = MkProd (Left f) g
            mp {x=Right (_,_),y=Right (_,_)} (Right (MkProd f g)) = MkProd (Right f) g
        in MkFunctorR fn {impl = MkCatFunctor mp}
  absorbl {a=W0 a} = MkCat0 $ absorbl_ {a}
    where
      absorbl_ : forall a. Cat (Prod a Zero) Zero
      absorbl_ {a=MkCategoryR{}} = MkFunctorR snd {impl = MkCatFunctor snd}
  absorbl' {a=W0 a} = MkCat0 $ absorbl'_ {a}
    where
      absorbl'_ : forall a. Cat Zero (Prod a Zero)
      absorbl'_ {a=MkCategoryR{}} = MkFunctorR absurd {impl = MkCatFunctor absurd}
  absorbr {a=W0 a} = MkCat0 $ absorbr_ {a}
    where
      absorbr_ : forall a. Cat (Prod Zero a) Zero
      absorbr_ {a=MkCategoryR{}} = MkFunctorR fst {impl = MkCatFunctor fst}
  absorbr' {a=W0 a} = MkCat0 $ absorbr'_ {a}
    where
      absorbr'_ : forall a. Cat Zero (Prod Zero a)
      absorbr'_ {a=MkCategoryR{}} = MkFunctorR absurd {impl = MkCatFunctor absurd}


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
  CatProd : MonoidalR
  CatProd = MkMonoidalR Cat Prod One

  public export
  CatSum : MonoidalR
  CatSum = MkMonoidalR Cat Sum Zero

  public export
  Cat0Prod : MonoidalR
  Cat0Prod = MkMonoidalR Cat0 Cat0Prod (W0 One)

  public export
  Cat0Sum : MonoidalR
  Cat0Sum = MkMonoidalR Cat0 Cat0Sum (W0 Zero)

namespace BraidedR
  public export
  CatProd : BraidedR
  CatProd = MkBraidedR Cat Prod One

  public export
  CatSum : BraidedR
  CatSum = MkBraidedR Cat Sum Zero

  public export
  Cat0Prod : BraidedR
  Cat0Prod = MkBraidedR Cat0 Cat0Prod (W0 One)

  public export
  Cat0Sum : BraidedR
  Cat0Sum = MkBraidedR Cat0 Cat0Sum (W0 Zero)

namespace CartesianR
  public export
  Cat : CartesianR
  Cat = MkCartesianR Cat Prod One

  public export
  Cat0 : CartesianR
  Cat0 = MkCartesianR Cat0 Cat0Prod (W0 One)

namespace CocartesianR
  public export
  Cat : CocartesianR
  Cat = MkCocartesianR Cat Sum Zero

  public export
  Cat0 : CocartesianR
  Cat0 = MkCocartesianR Cat0 Cat0Sum (W0 Zero)

namespace BimonoidalR
  public export
  Cat : BimonoidalR
  Cat = MkBimonoidalR Cat Sum Prod Zero One

  public export
  Cat0 : BimonoidalR
  Cat0 = MkBimonoidalR Cat0 Cat0Sum Cat0Prod (W0 Zero) (W0 One)

namespace RigCategoryR
  public export
  Cat : RigCategoryR
  Cat = MkRigCategoryR Cat Sum Prod Zero One

  public export
  Cat0 : RigCategoryR
  Cat0 = MkRigCategoryR Cat0 Cat0Sum Cat0Prod (W0 Zero) (W0 One)

namespace SymRigCategoryR
  public export
  Cat : SymRigCategoryR
  Cat = MkSymRigCategoryR Cat Sum Prod Zero One

  public export
  Cat0 : SymRigCategoryR
  Cat0 = MkSymRigCategoryR Cat0 Cat0Sum Cat0Prod (W0 Zero) (W0 One)

namespace DistributiveR
  public export
  Cat : DistributiveR
  Cat = MkDistributiveR Cat Sum Prod Zero One

  public export
  Cat0 : DistributiveR
  Cat0 = MkDistributiveR Cat0 Cat0Sum Cat0Prod (W0 Zero) (W0 One)

namespace ClosedR
  public export
  Cat : ClosedR
  Cat = MkClosedR Cat Prod FunCat One

namespace CartesianClosedR
  public export
  Cat : CartesianClosedR
  Cat = MkCartesianClosedR Cat Prod FunCat One
