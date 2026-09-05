module Control.Category.Cartesian

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Control.Category.Braided
import Data.Morphisms
import Data.Fin
import Data.List

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A monoidal category is *cartesian* if its tensor product coincides
||| with the categorical product. This automatically implies that it
||| is symmetric (see `Braided`).
|||
||| This interface may be implemented in two equivalent ways: by giving
||| a categorical product structure (`projl`, `projr`, `prod`) or a
||| universal comonoid structure (`split`, `elim`). Each set of
||| methods has a default definition in terms of the others.
|||
||| This is the interface-style definition of a cartesian monoidal category.
||| For the record-style definition, see `Control.Category.Records.CartesianR`.
|||
||| Laws for `projl`, `projr`, `prod`:
||| * `projl . prod f g = f`
||| * `projr . prod f g = g`
|||
||| Laws for `split`, `elim`:
||| * `unitl . mapl elim . split = id`
||| * `unitr . mapr elim . split = id`
public export
interface Monoidal cat ten i =>
    Cartesian (0 cat : Hom obj) (ten : obj -> obj -> obj) (i : obj) | cat,ten where
  constructor MkCartesian
  -- NOTE: If these default definitions look weird, it's because
  -- Idris's interface elaboration really doesn't like these methods,
  -- so I'm giving it as much help as possible.

  ||| The left projection of the product.
  projl : {a,b : _} -> cat (a `ten` b) a
  projl = Core.(.) {cat} (unitr {cat,ten,i}) (mapr' {cat,f=ten} $ elim {ten})

  ||| The right projection of the product.
  projr : {a,b : _} -> cat (a `ten` b) b
  projr = Core.(.) {cat} (unitl {cat,ten,i}) (mapl' {cat,f=ten} $ elim {ten})

  ||| The universal property of the product.
  prod : {a,b,b' : _} -> cat a b -> cat a b' -> cat a (b `ten` b')
  prod f g = Core.(.) (bimap' f g) split

  ||| The cojoin of the universal comonoid structure.
  split : {a : _} -> cat a (a `ten` a)
  split = Cartesian.prod {ten} Core.id Core.id

  ||| The counit of the universal comonoid structure.
  elim : {a : _} -> cat a i
  elim = Core.(.) (projl {ten}) (unitl' {ten})

export infixr 7 &&&

||| An operator synonym for `prod`, the universal property of a
||| cartesian monoidal category's product structure.
public export %inline %tcinline
(&&&) : {ten,i : _} -> Cartesian cat ten i => {a,b,b' : _} ->
        cat a b -> cat a b' -> cat a (b `ten` b')
(&&&) = prod

||| See `PreMonoidal`.
public export
PreCartesian : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> Type
PreCartesian = Cartesian


------------------------------------------------------------
-- Characterization
------------------------------------------------------------

||| Project a single value out of a tensor product sequence by index.
public export
proj : Cartesian cat ten i => {xs : _} ->
       (x : Fin (length xs)) -> cat (TenSeq ten i xs) (index' xs x)
proj @{c@(MkCartesian{})} {xs=[_]} FZ = id
proj @{c@(MkCartesian{})} {xs=[_,_]} (FS FZ) = projr
proj @{c@(MkCartesian{})} {xs=_::_::_} FZ = projl
proj @{c@(MkCartesian{})} {xs=_::_::_} (FS x) = proj x . projr

||| A compact representation of a function out of a tensor product
||| sequence of size `n`. Used to rearrange/"swizzle" tensor products.
public export
Swizzle : (n : Nat) -> Type
Swizzle n = List (Fin n)

||| Apply a `Swizzle` to a list, rearranging its elements.
public export
swizzleList : (xs : List a) -> Swizzle (length xs) -> List a
swizzleList xs sw = map (index' xs) sw

||| Apply a `Swizzle` to a tensor product sequence.
public export
swizzle : Cartesian cat ten i => {xs : _} ->
          (sw : Swizzle (length xs)) -> cat (TenSeq ten i xs) (TenSeq ten i $ swizzleList xs sw)
swizzle @{c@(MkCartesian{})} [] = elim {ten}
swizzle @{c@(MkCartesian{})} {xs=_::_} [i] = proj i
swizzle @{c@(MkCartesian{})} {xs=_::_} (i::is@(_::_)) =
  bimap' (proj {ten} i) (swizzle is) . split


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace Braided
  ||| Convert a cartesian monoidal category into a
  ||| symmetric monoidal category.
  public export
  [FromCartesian] {ten,i : _} -> Cartesian cat ten i => Braided cat ten i where
    braid = prod projr projl


-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

public export
Cartesian Morphism Pair () where
  projl = Mor fst
  projr = Mor snd
  prod f g = (,) <$> f <*> g
  split = Mor dup
  elim = Mor $ const ()

namespace Cartesian
  public export
  [Function] Cartesian (~~>) Pair ()
      using Braided.FuncPair where
    projl = fst
    projr = snd
    prod f g x = (f x, g x)
    split = dup
    elim = const ()

||| WARNING: This is a premonoidal category, not truly monoidal.
public export %hint
PreCartesianKleisliPair : Monad m => PreCartesian (Kleislimorphism m) Pair ()
PreCartesianKleisliPair = Impl
  where
    [Impl] Cartesian (Kleislimorphism m) Pair () where
      projl = Kleisli $ pure . fst
      projr = Kleisli $ pure . snd
      prod f g = (,) <$> f <*> g
      split = Kleisli $ pure . dup
      elim = Kleisli $ pure . const ()

