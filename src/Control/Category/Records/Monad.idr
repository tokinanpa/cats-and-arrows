module Control.Category.Records.Monad

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Monoidal
import Control.Category.Records.Functor
import Data.Morphisms

%default total
%prefix_record_projections off

||| A *monad* `m` is a monoid object in the category of endofunctors
||| in `cat`, where the tensor product is given by composition.
|||
||| See `CatMonad` for required laws.
public export
record MonadR (cat : CategoryR) where
  constructor MkMonadR
  fun : cat.obj -> cat.obj
  {auto impl : CatMonad cat.hom fun}

namespace MonadR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : MonadR cat) -> EndofunctorR cat
  (.functorR) (MkMonadR {} {fun}) = MkFunctorR fun

  ||| Apply the monad to a morphism in `cat`.
  public export %inline
  (.map) : (rec : MonadR cat) -> {a,b : _} ->
           cat.hom a b -> cat.hom (rec.fun a) (rec.fun b)
  (.map) rec@(MkMonadR {}) = rec.functorR.map


  ||| Convert this into a `MonadR`.
  public export %inline
  (.monadR) : (rec : MonadR cat) -> MonadR cat
  (.monadR) = id

  ||| The join transformation of the monad.
  public export %inline
  (.join) : (rec : MonadR cat) -> {a : _} ->
            cat.hom (rec.fun (rec.fun a)) (rec.fun a)
  (.join) rec = join @{rec.impl}

  ||| The unit transformation of the monad.
  public export %inline
  (.unit) : (rec : MonadR cat) -> {a : _} ->
            cat.hom a (rec.fun a)
  (.unit) rec = unit @{rec.impl}


||| A monad has *tensorial strength* if it is compatible with a
||| monoidal category's tensor product.
|||
||| See `StrongMonad` for required laws.
public export
record StrongMonadR (cat : MonoidalR) where
  constructor MkStrongMonadR
  fun : cat.obj -> cat.obj
  {auto impl : StrongMonad cat.hom cat.tensor fun}

namespace StrongMonadR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : StrongMonadR cat) -> EndofunctorR cat.categoryR
  (.functorR) {cat=MkMonoidalR{}} (MkStrongMonadR {} {fun}) = MkFunctorR fun

  ||| Apply the monad to a morphism in `cat`.
  public export %inline
  (.map) : (rec : StrongMonadR cat) -> {a,b : _} ->
           cat.hom a b -> cat.hom (rec.fun a) (rec.fun b)
  (.map) {cat=MkMonoidalR{}} rec@(MkStrongMonadR {}) = rec.functorR.map


  ||| Convert this into a `MonadR`.
  public export %inline
  (.monadR) : (rec : StrongMonadR cat) -> MonadR cat.categoryR
  (.monadR) {cat=MkMonoidalR{}} (MkStrongMonadR {} {fun}) = MkMonadR fun

  ||| The join transformation of the monad.
  public export %inline
  (.join) : (rec : StrongMonadR cat) -> {a : _} ->
            cat.hom (rec.fun (rec.fun a)) (rec.fun a)
  (.join) {cat=MkMonoidalR{}} rec@(MkStrongMonadR {}) = rec.monadR.join

  ||| The unit transformation of the monad.
  public export %inline
  (.unit) : (rec : StrongMonadR cat) -> {a : _} ->
            cat.hom a (rec.fun a)
  (.unit) {cat=MkMonoidalR{}} rec@(MkStrongMonadR {}) = rec.monadR.unit


  ||| Convert this into a `StrongMonadR`.
  public export %inline
  (.strongMonadR) : (rec : StrongMonadR cat) -> StrongMonadR cat
  (.strongMonadR) = id

  ||| The left tensor strength.
  public export %inline
  (.strongl) : (rec : StrongMonadR cat) -> {a,b : _} ->
               cat.hom (cat.tensor a (rec.fun b)) (rec.fun (cat.tensor a b))
  (.strongl) rec = strongl @{rec.impl}

  ||| The right tensor strength.
  public export %inline
  (.strongr) : (rec : StrongMonadR cat) -> {a,b : _} ->
               cat.hom (cat.tensor (rec.fun a) b) (rec.fun (cat.tensor a b))
  (.strongr) rec = strongr @{rec.impl}
