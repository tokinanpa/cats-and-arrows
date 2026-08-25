||| This module defines a more general Kleisli category construction
||| that can be used to derive a premonoidal category structure from
||| any strong monad on any premonoidal category.
module Control.Category.Instances.Kleisli

import Control.Category
import Control.Category.Semigroupoid
import Control.Category.Traced
import Control.Category.Bimonoidal
import Control.Category.Promonad
import Control.Category.Records

%default total

||| The Kleisli category of a category `cat` with monad `m`. This
||| forms another category with the same objects. In addition, if
||| `cat` is a premonoidal category, then this category inherits its
||| premonoidal structure. (Note that this is NOT the case for
||| monoidal structure.)
public export
record Kleisli (cat : Hom obj) (m : obj -> obj) (a,b : obj) where
  constructor MkKleisli
  runKleisli : cat a (m b)


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Category cat => CatMonad cat m => Category (Kleisli cat m) where
  id = MkKleisli unit
  MkKleisli f . MkKleisli g = MkKleisli (join . map f . g)

public export
[KleisliInj] Category cat => CatMonad cat m => CatFunctor cat (Kleisli cat m) Prelude.id where
  map f = MkKleisli $ unit . f


||| WARNING: This is typically a binoidal functor, not a true bifunctor.
||| It is only a bifunctor if the monad `m` is commutative over `ten`.
public export %hint
KleisliBinoidal : Category cat => StrongMonad cat ten m =>
                  CatEndoBinoidal cat ten => CatEndoBinoidal (Kleisli cat m) ten
KleisliBinoidal = Impl
  where
    [Impl] CatBifunctor (Kleisli cat m) (Kleisli cat m) (Kleisli cat m) ten where
      bimap (MkKleisli f) (MkKleisli g) =
        MkKleisli (strongl . mapr' g) . -- mapr
        MkKleisli (strongr . mapl' f)   -- mapl

public export
Promonad cat => CatMonad cat m => Promonad (Kleisli cat m) where
  funit f = MkKleisli $ unit . funit f

||| WARNING: This is typically a premonoidal category, not truly monoidal.
||| It is only monoidal if the monad `m` is commutative over `ten`.
public export %hint
KleisliPreMonoidal : PreMonoidal cat ten i => StrongMonad cat ten m =>
                     PreMonoidal (Kleisli cat m) ten i
KleisliPreMonoidal =
  MkMonoidal (MkKleisli $ unit . assoc)
             (MkKleisli $ unit . assoc')
             (MkKleisli $ unit . unitl)
             (MkKleisli $ unit . unitl')
             (MkKleisli $ unit . unitr)
             (MkKleisli $ unit . unitr')

public export %hint
KleisliPreBraided : PreBraided cat ten i => StrongMonad cat ten m =>
                    PreBraided (Kleisli cat m) ten i
KleisliPreBraided =
  MkBraided (MkKleisli $ unit . braid)
            (MkKleisli $ unit . braid')

public export %hint
KleisliPreCartesian : PreCartesian cat ten i => StrongMonad cat ten m =>
                      PreCartesian (Kleisli cat m) ten i
KleisliPreCartesian =
  MkCartesian (MkKleisli $ unit . projl)
              (MkKleisli $ unit . projr)
              (\f,g => bimap' f g . (MkKleisli $ unit . split))
              (MkKleisli $ unit . split)
              (MkKleisli $ unit . elim)

public export %hint
KleisliPreCocartesian : PreCocartesian cat ten i => StrongMonad cat ten m =>
                        PreCocartesian (Kleisli cat m) ten i
KleisliPreCocartesian =
  MkCocartesian (MkKleisli $ unit . injl)
                (MkKleisli $ unit . injr)
                (\f,g => (MkKleisli $ unit . merge) . bimap' f g)
                (MkKleisli $ unit . merge)
                (MkKleisli $ unit . intro)

public export %hint
KleisliPreBimonoidal : PreBimonoidal cat add mul z i =>
                       (StrongMonad cat add m, StrongMonad cat mul m) =>
                       PreBimonoidal (Kleisli cat m) add mul z i
KleisliPreBimonoidal @{_} @{(c@(MkStrongMonad @{con} {}),_)} =
  MkBimonoidal (MkKleisli $ unit @{con} . distribl)
               (MkKleisli $ unit @{con} . distribl')
               (MkKleisli $ unit @{con} . distribr)
               (MkKleisli $ unit @{con} . distribr')
               (MkKleisli $ unit @{con} . absorbl)
               (MkKleisli $ unit @{con} . absorbl')
               (MkKleisli $ unit @{con} . absorbr)
               (MkKleisli $ unit @{con} . absorbr')


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace CategoryR
  public export
  Kleisli : (cat : CategoryR) -> (m : MonadR cat) -> CategoryR
  Kleisli (MkCategoryR cat) (MkMonadR m) = MkCategoryR (Kleisli cat m)

namespace FunctorR
  public export
  KleisliInj : {cat,m : _} -> FunctorR cat (Kleisli cat m)
  KleisliInj {cat=MkCategoryR{}} {m=MkMonadR{}} = MkFunctorR Prelude.id {con = KleisliInj}

namespace MonoidalR
  public export
  Kleisli : (cat : PreMonoidalR) -> (m : StrongMonadR cat) -> PreMonoidalR
  Kleisli (MkMonoidalR cat ten i) (MkStrongMonadR m) = MkMonoidalR (Kleisli cat m) ten i

namespace BraidedR
  public export
  Kleisli : (cat : PreBraidedR) -> (m : StrongMonadR cat.monoidalR) -> PreBraidedR
  Kleisli (MkBraidedR cat ten i) (MkStrongMonadR m) = MkBraidedR (Kleisli cat m) ten i

namespace CartesianR
  public export
  Kleisli : (cat : PreCartesianR) -> (m : StrongMonadR cat.monoidalR) -> PreCartesianR
  Kleisli (MkCartesianR cat ten i) (MkStrongMonadR m) = MkCartesianR (Kleisli cat m) ten i

namespace CocartesianR
  public export
  Kleisli : (cat : PreCocartesianR) -> (m : StrongMonadR cat.monoidalR) -> PreCocartesianR
  Kleisli (MkCocartesianR cat ten i) (MkStrongMonadR m) = MkCocartesianR (Kleisli cat m) ten i
