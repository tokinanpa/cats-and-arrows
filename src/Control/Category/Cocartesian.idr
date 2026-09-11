module Control.Category.Cocartesian

import Control.Category.Core
import Control.Category.Functor
import Control.Category.Monoidal
import Control.Category.Braided
import Data.Either
import Data.Fin
import Data.List
import Data.Morphisms

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A monoidal category is *cocartesian* if its tensor product
||| coincides with the categorical coproduct. This automatically
||| implies that it is symmetric (see `Braided`).
|||
||| This interface may be implemented in two equivalent ways: by giving
||| a categorical coproduct structure (`injl`, `injr`, `coprod`) or a
||| universal monoid structure (`merge`, `intro`). Each set of methods
||| has a default definition in terms of the others.
|||
||| This is the interface-style definition of a cocartesian monoidal category.
||| For the record-style definition, see `Control.Category.Records.CocartesianR`.
|||
||| Laws for `injl`, `injr`, `coprod`:
||| * `coprod f g . injl = f`
||| * `coprod f g . injr = g`
|||
||| Laws for `merge`, `intro`:
||| * `merge . mapl intro . unitl' = id`
||| * `merge . mapr intro . unitr' = id`
public export
interface Monoidal cat ten i =>
    Cocartesian (0 cat : Hom obj) (ten : obj -> obj -> obj) (i : obj) | cat,ten where
  constructor MkCocartesian
  -- NOTE: If these default definitions look weird, it's because
  -- Idris's interface elaboration really doesn't like these methods,
  -- so I'm giving it as much help as possible.

  ||| The left injection of the coproduct.
  injl : {a,b : _} -> cat a (a `ten` b)
  injl = Core.(.) {cat} (mapr' {cat,f=ten} $ intro {ten}) (unitr' {cat,ten,i})

  ||| The right injection of the coproduct.
  injr : {a,b : _} -> cat b (a `ten` b)
  injr = Core.(.) {cat} (mapl' {cat,f=ten} $ intro {ten}) (unitl' {cat,ten,i})

  ||| The universal property of the coproduct.
  coprod : {a,a',b : _} -> cat a b -> cat a' b -> cat (a `ten` a') b
  coprod f g = Core.(.) merge (bimap' {f=ten} f g)

  ||| The join of the universal monoid structure.
  merge : {a : _} -> cat (a `ten` a) a
  merge = Cocartesian.coprod {ten} Core.id Core.id

  ||| The unit of the universal monoid structure.
  intro : {a : _} -> cat i a
  intro = Core.(.) (unitl {ten}) injl

export infixr 6 \|/

||| An operator synonym for `coprod`, the universal property of a
||| cocartesian monoidal category's coproduct structure.
public export %inline %tcinline
(\|/) : {ten,i : _} -> Cocartesian cat ten i => {a,a',b : _} ->
        cat a b -> cat a' b -> cat (a `ten` a') b
(\|/) = coprod

||| See `PreMonoidal`.
public export
PreCocartesian : (cat : Hom obj) -> (ten : obj -> obj -> obj) -> (i : obj) -> Type
PreCocartesian = Cocartesian


------------------------------------------------------------
-- Characterization
------------------------------------------------------------

public export
inj : Cocartesian cat ten i => {xs : _} -> (x : Fin (length xs)) -> cat (index' xs x) (TenSeq ten i xs)
inj @{c@(MkCocartesian{})} {xs=[_]} FZ = id
inj @{c@(MkCocartesian{})} {xs=[_,_]} (FS FZ) = injr
inj @{c@(MkCocartesian{})} {xs=_::_::_} FZ = injl
inj @{c@(MkCocartesian{})} {xs=_::_::_} (FS x) = injr . inj x


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace Braided
  ||| Convert a cocartesian monoidal category into a
  ||| symmetric monoidal category.
  public export
  [FromCocartesian] {ten,i : _} -> Cocartesian cat ten i => Braided cat ten i where
    braid = coprod injr injl


-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

public export
Cocartesian Morphism Either Void where
  injl = Mor Left
  injr = Mor Right
  coprod (Mor f) (Mor g) = Mor $ either f g
  merge = Mor fromEither
  intro = Mor absurd

namespace Cocartesian
  public export
  [Function] Cocartesian (~~>) Either Void
      using Braided.FuncEither where
    injl = Left
    injr = Right
    coprod f g = either f g
    merge = fromEither
    intro = absurd

public export
Monad m => Cocartesian (Kleislimorphism m) Either Void where
  injl = Kleisli $ pure . Left
  injr = Kleisli $ pure . Right
  coprod (Kleisli f) (Kleisli g) = Kleisli $ either f g
  merge = Kleisli $ pure . fromEither
  intro = Kleisli $ pure . absurd

