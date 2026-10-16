module Control.Category.Promonad

import Control.Category.Core
import Control.Category.Semigroupoid
import Control.Category.Functor
import Control.Category.Monoidal
import Control.Category.Braided
import Control.Category.Cartesian
import Control.Category.Cocartesian
import Control.Category.Traced
import Control.Category.Bimonoidal
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Either
import Data.Morphisms
import Data.Vect
import Data.Wrap0

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *promonad* (short for profunctor monad, no relation to regular
||| Prelude monads) is a monad in the bicategory of profunctors.
|||
||| Equivalently, a promonad is a category equipped with an
||| identity-on-objects functor from the category `Typ`.
|||
||| Laws - `fromFunc` is functorial (see `CatFunctor`), meaning:
||| * `fromFunc id = id`
||| * `fromFunc f . fromFunc g = fromFunc (f . g)`
public export
interface Category cat => Promonad (0 cat : Hom Type) where
  ||| The unit transformation of the promonad.
  ||| Equivalently, the action of the unit functor on morphisms.
  fromFunc : (a -> b) -> cat a b

||| Like `Promonad`, but allows the category's objects to be wrapped
||| using `Wrap0`. This is typically the more practical option.
|||
||| See `Promonad` for required laws.
public export
interface Category cat => Promonad0 (0 cat : Hom Type0) where
  ||| The unit transformation of the promonad.
  ||| Equivalently, the action of the unit functor on morphisms.
  fromFuncW : (a -> b) -> cat (W0 a) (W0 b)

------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

||| The unit identity-on-objects functor of a promonad.
public export
[PromonadUnit] Promonad cat => CatFunctor Morphism cat Prelude.id where
  map = fromFunc . applyMor

||| The unit identity-on-objects functor of a promonad.
public export
[PromonadUnit0] Promonad0 cat => CatFunctor Morphism cat (\x => W0 x) where
  map = fromFuncW . applyMor

namespace Monoidal
  ||| Convert a promonad into a (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Monoidal Morphism ten i) =>
      Monoidal cat ten i where
    assoc = fromFunc $ applyMor assoc
    assoc' = fromFunc $ applyMor assoc'
    unitl = fromFunc $ applyMor unitl
    unitl' = fromFunc $ applyMor unitl'
    unitr = fromFunc $ applyMor unitr
    unitr' = fromFunc $ applyMor unitr'

namespace Braided
  ||| Convert a promonad into a braided (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Braided Morphism ten i) =>
      Braided cat ten i using Monoidal.FromPromonad where
    braid = fromFunc $ applyMor braid

namespace MonSymmetric
  ||| Convert a promonad into a symmetric (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, MonSymmetric Morphism ten i) =>
      MonSymmetric cat ten i using Braided.FromPromonad where

namespace Cartesian
  ||| Convert a promonad into a cartesian (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Cartesian Morphism ten i) =>
      Cartesian cat ten i using Monoidal.FromPromonad where
    projl = fromFunc $ applyMor projl
    projr = fromFunc $ applyMor projr
    prod f g = Core.(.) {cat} (bimap' f g) (split {cat,ten,i})
    split = fromFunc $ applyMor split
    elim = fromFunc $ applyMor $ elim {ten}

namespace Cocartesian
  ||| Convert a promonad into a cocartesian (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Cocartesian Morphism ten i) =>
      Cocartesian cat ten i using Monoidal.FromPromonad where
    injl = fromFunc $ applyMor injl
    injr = fromFunc $ applyMor injr
    coprod f g = Core.(.) {cat} (merge {cat,ten,i}) (bimap' f g)
    merge = fromFunc $ applyMor merge
    intro = fromFunc $ applyMor $ intro {ten}

namespace Bimonoidal
  ||| Convert a promonad into a (pre)bimonoidal category.
  public export
  [FromPromonad] {add,mul,z,i : _} -> (Promonad cat, CatEndoBifunctor cat add, CatEndoBifunctor cat mul,
                  Bimonoidal Morphism add mul z i) => Bimonoidal cat add mul z i
      using Monoidal.FromPromonad where
    distribl = fromFunc $ applyMor distribl
    distribl' = fromFunc $ applyMor distribl'
    distribr = fromFunc $ applyMor distribr
    distribr' = fromFunc $ applyMor distribr'
    absorbl = fromFunc $ applyMor $ absorbl {add,mul}
    absorbl' = fromFunc $ applyMor $ absorbl' {add,mul}
    absorbr = fromFunc $ applyMor $ absorbr {add,mul}
    absorbr' = fromFunc $ applyMor $ absorbr' {add,mul}


-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

public export
Promonad Morphism where
  fromFunc = Mor

namespace Promonad
  public export
  [Function] Promonad (~~>) using Category.Function where
    fromFunc = id

public export
Monad m => Promonad (Kleislimorphism m) where
  fromFunc f = Kleisli $ pure . f
