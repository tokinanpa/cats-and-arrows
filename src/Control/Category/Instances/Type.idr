||| This module defines the category of types and functions, named
||| `Typ`. Using this is more efficient than something like `Morphism`,
||| as it erases the types at runtime.
module Control.Category.Instances.Type

import Control.Category
import Control.Category.Records
import Data.Either
import Data.Tensor
import Data.Wrap0

%default total

public export
data Typ : (a,b : Type0) -> Type where
  MkTyp : (a.runW0 -> b.runW0) -> Typ a b

public export %inline %tcinline
runTyp : Typ a b -> a.runW0 -> b.runW0
runTyp (MkTyp f) = f

public export %inline %tcinline
(.runTyp) : Typ a b -> a.runW0 -> b.runW0
(.runTyp) = runTyp

public export %inline
Typ_ : (0 a,b : Type) -> Type
Typ_ a b = Typ (W0 a) (W0 b)


public export
Pair : Type0 -> Type0 -> Type0
Pair = liftW2 Pair

public export
Either : Type0 -> Type0 -> Type0
Either = liftW2 Either

public export
TypHom : Type0 -> Type0 -> Type0
TypHom a b = W0 (Typ a b)


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Category Typ where
  id = MkTyp id
  MkTyp f . MkTyp g = MkTyp (f . g)

public export %hint
SemigroupoidTyp : Semigroupoid Typ
SemigroupoidTyp = FromCategory

public export
Promonad0 Typ where
  funitW = MkTyp

namespace CatFunctor
  public export
  [FromFunctor] Functor f => CatFunctor Typ Typ (liftW f) where
    map {a=W0 _,b=W0 _} (MkTyp f) = MkTyp (map f)

namespace CatBifunctor
  public export
  [FromBifunctor] Bifunctor f => CatBifunctor Typ Typ Typ (liftW2 f) where
    bimap {a=W0 _,a'=W0 _,b=W0 _,b'=W0 _} (MkTyp f) (MkTyp g) = MkTyp (bimap f g)

public export
CatBifunctor Typ Typ Typ Pair where
  bimap {a=W0 _,a'=W0 _,b=W0 _,b'=W0 _} (MkTyp f) (MkTyp g) = MkTyp (bimap f g)

public export
CatBifunctor Typ Typ Typ Either where
  bimap {a=W0 _,a'=W0 _,b=W0 _,b'=W0 _} (MkTyp f) (MkTyp g) = MkTyp (bimap f g)

namespace Monoidal
  public export
  FromTensor : {ten,i : _} -> Tensor ten i => Monoidal Typ (liftW2 ten) (W0 i)
  FromTensor = MkMonoidal @{%search} @{FromBifunctor}
    (MkTyp assocr)
    (MkTyp assocl)
    (MkTyp unitl.leftToRight)
    (MkTyp unitl.rightToLeft)
    (MkTyp unitr.leftToRight)
    (MkTyp unitr.rightToLeft)

public export
Monoidal Typ Pair (W0 ()) where
  assoc = MkTyp (\((x,y),z) => (x,(y,z)))
  assoc' = MkTyp (\(x,(y,z)) => ((x,y),z))
  unitl = MkTyp snd
  unitl' = MkTyp ((),)
  unitr = MkTyp fst
  unitr' = MkTyp (,())

public export
Monoidal Typ Either (W0 Void) where
  assoc = MkTyp $ either (either Left (Right . Left)) (Right . Right)
  assoc' = MkTyp $ either (Left . Left) (either (Left . Right) Right)
  unitl = MkTyp $ either absurd id
  unitl' = MkTyp Right
  unitr = MkTyp $ either id absurd
  unitr' = MkTyp Left

namespace Braided
  public export
  FromTensor : {ten,i : _} -> (Tensor ten i, Symmetric ten) => Braided Typ (liftW2 ten) (W0 i)
  FromTensor = MkBraided @{FromTensor} (MkTyp swap') (MkTyp swap')

public export
Braided Typ Pair (W0 ()) where
  braid = MkTyp swap

public export
Braided Typ Either (W0 Void) where
  braid = MkTyp mirror

public export
Cartesian Typ Pair (W0 ()) where
  projl = MkTyp fst
  projr = MkTyp snd
  prod (MkTyp f) (MkTyp g) = MkTyp $ \x => (f x, g x)
  split = MkTyp dup
  elim = MkTyp $ const ()

public export
Cocartesian Typ Either (W0 Void) where
  injl = MkTyp Left
  injr = MkTyp Right
  coprod (MkTyp f) (MkTyp g) = MkTyp $ either f g
  merge = MkTyp fromEither
  intro = MkTyp absurd

public export
Closed Typ Pair TypHom (W0 ()) where
  curry (MkTyp f) = MkTyp $ \x => MkTyp (curry f x)
  uncurry (MkTyp f) = MkTyp $ uncurry $ \x => (f x).runTyp

public export
Bimonoidal Typ Either Pair (W0 Void) (W0 ()) where
  distribl = MkTyp $ \(x,y) => bimap (x,) (x,) y
  distribl' = MkTyp $ either (mapSnd Left) (mapSnd Right)
  distribr = MkTyp $ \(x,y) => bimap (,y) (,y) x
  distribr' = MkTyp $ either (mapFst Left) (mapFst Right)
  absorbl = MkTyp snd
  absorbl' = MkTyp absurd
  absorbr = MkTyp fst
  absorbr' = MkTyp absurd


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Typ : SemigroupoidR
  Typ = MkSemigroupoidR Typ

namespace CategoryR
  public export
  Typ : CategoryR
  Typ = MkCategoryR Typ

namespace CatBifunctor
  public export
  Pair : BifunctorR Typ Typ Typ
  Pair = MkBifunctorR Pair

  public export
  Either : BifunctorR Typ Typ Typ
  Either = MkBifunctorR Either

namespace MonoidalR
  public export
  TypPair : MonoidalR
  TypPair = MkMonoidalR Typ Pair (W0 ())

  public export
  TypEither : MonoidalR
  TypEither = MkMonoidalR Typ Either (W0 Void)

namespace BraidedR
  public export
  TypPair : BraidedR
  TypPair = MkBraidedR Typ Pair (W0 ())

  public export
  TypEither : BraidedR
  TypEither = MkBraidedR Typ Either (W0 Void)

namespace CartesianR
  public export
  Typ : CartesianR
  Typ = MkCartesianR Typ Pair (W0 ())

namespace CocartesianR
  public export
  Typ : CocartesianR
  Typ = MkCocartesianR Typ Either (W0 Void)

namespace ClosedR
  public export
  Typ : ClosedR
  Typ = MkClosedR Typ Pair TypHom (W0 ())

namespace BimonoidalR
  public export
  Typ : BimonoidalR
  Typ = MkBimonoidalR Typ Either Pair (W0 Void) (W0 ())

namespace RigCategoryR
  public export
  Typ : RigCategoryR
  Typ = MkRigCategoryR Typ Either Pair (W0 Void) (W0 ())

namespace SymRigCategoryR
  public export
  Typ : SymRigCategoryR
  Typ = MkSymRigCategoryR Typ Either Pair (W0 Void) (W0 ())

namespace DistributiveR
  public export
  Typ : DistributiveR
  Typ = MkDistributiveR Typ Either Pair (W0 Void) (W0 ())
