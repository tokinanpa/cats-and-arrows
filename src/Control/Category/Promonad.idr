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
||| Laws - `funit` is functorial (see `CatFunctor`), meaning:
||| * `funit id = id`
||| * `funit f . funit g = funit (f . g)`
public export
interface Category cat => Promonad (0 cat : Hom Type) where
  ||| The unit transformation of the promonad.
  ||| Equivalently, the action of the unit functor on morphisms.
  funit : (a -> b) -> cat a b


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

||| The unit identity-on-objects functor of a promonad.
public export
[PromonadUnit] Promonad cat => CatFunctor Morphism cat Prelude.id where
  map = funit . applyMor

namespace Monoidal
  ||| Convert a promonad into a (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Monoidal Morphism ten i) =>
      Monoidal cat ten i where
    assoc = funit $ applyMor assoc
    assoc' = funit $ applyMor assoc'
    unitl = funit $ applyMor unitl
    unitl' = funit $ applyMor unitl'
    unitr = funit $ applyMor unitr
    unitr' = funit $ applyMor unitr'

namespace Braided
  ||| Convert a promonad into a braided (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Braided Morphism ten i) =>
      Braided cat ten i using Monoidal.FromPromonad where
    braid = funit $ applyMor braid

namespace Cartesian
  ||| Convert a promonad into a cartesian (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Cartesian Morphism ten i) =>
      Cartesian cat ten i using Monoidal.FromPromonad where
    projl = funit $ applyMor projl
    projr = funit $ applyMor projr
    prod f g = Core.(.) {cat} (bimap' f g) (split {cat,ten,i})
    split = funit $ applyMor split
    elim = funit $ applyMor $ elim {ten}

namespace Cocartesian
  ||| Convert a promonad into a cocartesian (pre)monoidal category.
  public export
  [FromPromonad] {ten,i : _} -> (Promonad cat, CatEndoBifunctor cat ten, Cocartesian Morphism ten i) =>
      Cocartesian cat ten i using Monoidal.FromPromonad where
    injl = funit $ applyMor injl
    injr = funit $ applyMor injr
    coprod f g = Core.(.) {cat} (merge {cat,ten,i}) (bimap' f g)
    merge = funit $ applyMor merge
    intro = funit $ applyMor $ intro {ten}

namespace Bimonoidal
  ||| Convert a promonad into a (pre)bimonoidal category.
  public export
  [FromPromonad] {add,mul,z,i : _} -> (Promonad cat, CatEndoBifunctor cat add, CatEndoBifunctor cat mul,
                  Bimonoidal Morphism add mul z i) => Bimonoidal cat add mul z i
      using Monoidal.FromPromonad where
    distribl = funit $ applyMor distribl
    distribl' = funit $ applyMor distribl'
    distribr = funit $ applyMor distribr
    distribr' = funit $ applyMor distribr'
    absorbl = funit $ applyMor $ absorbl {add,mul}
    absorbl' = funit $ applyMor $ absorbl' {add,mul}
    absorbr = funit $ applyMor $ absorbr {add,mul}
    absorbr' = funit $ applyMor $ absorbr' {add,mul}


-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

public export
Promonad Morphism where
  funit = Mor

namespace Promonad
  public export
  [Function] Promonad (~~>) using Category.Function where
    funit = id

public export
Monad m => Promonad (Kleislimorphism m) where
  funit f = Kleisli $ pure . f
