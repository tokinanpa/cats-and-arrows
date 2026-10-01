||| This module defines a co-Kleisli category construction on an
||| arbitrary comonad in an arbitrary premonoidal category.
module Control.Category.Instances.Cokleisli

import Control.Category
import Control.Category.Records
import Data.Wrap0

%default total

||| The co-Kleisli category of a category `cat` with comonad `w`. This
||| forms another category with the same objects. In addition, if
||| `cat` is a premonoidal category and `w` has tensorial costrength,
||| then this category inherits its premonoidal structure.
||| (Note that this is NOT the case for monoidal structure.)
public export
record Cokleisli (cat : Hom obj) (w : obj -> obj) (a,b : obj) where
  constructor MkCokleisli
  runCokleisli : cat (w a) b


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
{w : _} -> Category cat => CatComonad cat w => Category (Cokleisli cat w) where
  id = MkCokleisli counit
  MkCokleisli f . MkCokleisli g = MkCokleisli (f . map g . cojoin)

public export
[CokleisliInj] {w : _} -> Category cat => CatComonad cat w => CatFunctor cat (Cokleisli cat w) Prelude.id where
  map f = MkCokleisli $ f . counit

public export
{w : _} -> Promonad0 cat => CatComonad cat w => Promonad0 (Cokleisli cat w) where
  funitW f = MkCokleisli (funitW f . counit)

||| WARNING: This is typically a binoidal functor, not a true bifunctor.
||| It is only a bifunctor if the comonad `m` is commutative over `ten`.
public export %hint
CokleisliBinoidal : {ten,w : _} -> Category cat => StrongComonad cat ten w =>
                    EndoBinoidal cat ten => EndoBinoidal (Cokleisli cat w) ten
CokleisliBinoidal = Impl
  where
    [Impl] CatBifunctor (Cokleisli cat w) (Cokleisli cat w) (Cokleisli cat w) ten where
      bimap (MkCokleisli f) (MkCokleisli g) =
        MkCokleisli (mapr' g . costrongl) . -- mapr
        MkCokleisli (mapl' f . costrongr)   -- mapl

||| WARNING: This is typically a premonoidal category, not truly monoidal.
||| It is only monoidal if the comonad `m` is commutative over `ten`.
public export %hint
CokleisliPreMonoidal : {w,ten,i : _} -> PreMonoidal cat ten i => StrongComonad cat ten w =>
                       PreMonoidal (Cokleisli cat w) ten i
CokleisliPreMonoidal =
  MkMonoidal (MkCokleisli $ assoc . counit)
             (MkCokleisli $ assoc' . counit)
             (MkCokleisli $ unitl . counit)
             (MkCokleisli $ unitl' . counit)
             (MkCokleisli $ unitr . counit)
             (MkCokleisli $ unitr' . counit)

public export %hint
CokleisliPreBraided : {w,ten,i : _} -> PreBraided cat ten i => StrongComonad cat ten w =>
                      PreBraided (Cokleisli cat w) ten i
CokleisliPreBraided =
  MkBraided (MkCokleisli $ braid . counit)
            (MkCokleisli $ braid' . counit)

public export %hint
CokleisliPreCartesian : {w,ten,i : _} -> PreCartesian cat ten i => StrongComonad cat ten w =>
                        PreCartesian (Cokleisli cat w) ten i
CokleisliPreCartesian =
  MkCartesian (MkCokleisli $ projl . counit)
              (MkCokleisli $ projr . counit)
              (\f,g => bimap' f g . (MkCokleisli $ split . counit))
              (MkCokleisli $ split . counit)
              (MkCokleisli $ elim {ten} . counit)

public export %hint
CokleisliPreCocartesian : {w,ten,i : _} -> PreCocartesian cat ten i => StrongComonad cat ten w =>
                          PreCocartesian (Cokleisli cat w) ten i
CokleisliPreCocartesian =
  MkCocartesian (MkCokleisli $ injl . counit)
                (MkCokleisli $ injr . counit)
                (\f,g => (MkCokleisli $ merge . counit) . bimap' f g)
                (MkCokleisli $ merge . counit)
                (MkCokleisli $ intro {ten} . counit)

public export %hint
CokleisliPreBimonoidal : {w,add,mul,z,i : _} -> PreBimonoidal cat add mul z i =>
                         (StrongComonad cat add w, StrongComonad cat mul w) =>
                         PreBimonoidal (Cokleisli cat w) add mul z i
CokleisliPreBimonoidal @{_} @{(c@(impl,_),_)} =
  MkBimonoidal (MkCokleisli $ distribl . counit @{impl})
               (MkCokleisli $ distribl' . counit @{impl})
               (MkCokleisli $ distribr . counit @{impl})
               (MkCokleisli $ distribr' . counit @{impl})
               (MkCokleisli $ absorbl {add,mul} . counit @{impl})
               (MkCokleisli $ absorbl' {add,mul} . counit @{impl})
               (MkCokleisli $ absorbr {add,mul} . counit @{impl})
               (MkCokleisli $ absorbr' {add,mul} . counit @{impl})


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace CategoryR
  public export
  Cokleisli : (cat : CategoryR) -> (w : ComonadR cat) -> CategoryR
  Cokleisli (MkCategoryR cat) (MkComonadR w) = MkCategoryR (Cokleisli cat w)

namespace FunctorR
  public export
  CokleisliInj : {cat,w : _} -> FunctorR cat (Cokleisli cat w)
  CokleisliInj {cat=MkCategoryR{}} {w=MkComonadR{}} = MkFunctorR Prelude.id {impl = CokleisliInj}

namespace MonoidalR
  public export
  Cokleisli : (cat : PreMonoidalR) -> (w : StrongComonadR cat) -> PreMonoidalR
  Cokleisli (MkMonoidalR cat ten i) (MkStrongComonadR w) = MkMonoidalR (Cokleisli cat w) ten i

namespace BraidedR
  public export
  Cokleisli : (cat : PreBraidedR) -> (w : StrongComonadR cat.monoidalR) -> PreBraidedR
  Cokleisli (MkBraidedR cat ten i) (MkStrongComonadR w) = MkBraidedR (Cokleisli cat w) ten i

namespace CartesianR
  public export
  Cokleisli : (cat : PreCartesianR) -> (w : StrongComonadR cat.monoidalR) -> PreCartesianR
  Cokleisli (MkCartesianR cat ten i) (MkStrongComonadR w) = MkCartesianR (Cokleisli cat w) ten i

namespace CocartesianR
  public export
  Cokleisli : (cat : PreCocartesianR) -> (w : StrongComonadR cat.monoidalR) -> PreCocartesianR
  Cokleisli (MkCocartesianR cat ten i) (MkStrongComonadR w) = MkCocartesianR (Cokleisli cat w) ten i
