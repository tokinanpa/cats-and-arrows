module Control.Category.Records.Comonad

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Monoidal
import Control.Category.Records.Functor
import Control.Category.Records.MonFunctor

%default total
%prefix_record_projections off

||| A *comonad* `m` is a comonoid object in the category of
||| endofunctors in `cat`, where the tensor product is given by
||| composition.
|||
||| See `CatComonad` for required laws.
public export
record ComonadR (cat : CategoryR) where
  constructor MkComonadR
  fun : cat.obj -> cat.obj
  {auto impl : CatComonad cat.hom fun}

namespace ComonadR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : ComonadR cat) -> EndofunctorR cat
  (.functorR) (MkComonadR {} {fun}) = MkFunctorR fun

  ||| Apply the monad to a morphism in `cat`.
  public export %inline
  (.map) : (rec : ComonadR cat) -> {a,b : _} ->
           cat.hom a b -> cat.hom (rec.fun a) (rec.fun b)
  (.map) rec@(MkComonadR {}) = rec.functorR.map


  ||| Convert this into a `ComonadR`.
  public export %inline
  (.comonadR) : (rec : ComonadR cat) -> ComonadR cat
  (.comonadR) = id

  ||| The cojoin transformation of the comonad.
  public export %inline
  (.cojoin) : (rec : ComonadR cat) -> {a : _} ->
              cat.hom (rec.fun a) (rec.fun (rec.fun a))
  (.cojoin) rec = cojoin @{rec.impl}

  ||| The counit transformation of the comonad.
  public export %inline
  (.counit) : (rec : ComonadR cat) -> {a : _} ->
              cat.hom (rec.fun a) a
  (.counit) rec = counit @{rec.impl}


||| A strong comonad is a comonad that is also a costrong functor.
|||
||| See `StrongComonad` for required laws.
public export
record StrongComonadR (cat : MonoidalR) where
  constructor MkStrongComonadR
  fun : cat.obj -> cat.obj
  {auto impl : StrongComonad cat.hom cat.tensor fun}

namespace StrongComonadR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : StrongComonadR cat) -> EndofunctorR cat.categoryR
  (.functorR) {cat=MkMonoidalR{}} (MkStrongComonadR {} {fun}) = MkFunctorR fun

  ||| Apply the monad to a morphism in `cat`.
  public export %inline
  (.map) : (rec : StrongComonadR cat) -> {a,b : _} ->
           cat.hom a b -> cat.hom (rec.fun a) (rec.fun b)
  (.map) {cat=MkMonoidalR{}} rec@(MkStrongComonadR {}) = rec.functorR.map


  ||| Convert this into a `ComonadR`.
  public export %inline
  (.comonadR) : (rec : StrongComonadR cat) -> ComonadR cat.categoryR
  (.comonadR) {cat=MkMonoidalR{}} (MkStrongComonadR {} {fun}) = MkComonadR fun

  ||| The cojoin transformation of the comonad.
  public export %inline
  (.cojoin) : (rec : StrongComonadR cat) -> {a : _} ->
              cat.hom (rec.fun a) (rec.fun (rec.fun a))
  (.cojoin) {cat=MkMonoidalR{}} rec@(MkStrongComonadR {}) = rec.comonadR.cojoin

  ||| The counit transformation of the comonad.
  public export %inline
  (.counit) : (rec : StrongComonadR cat) -> {a : _} ->
              cat.hom (rec.fun a) a
  (.counit) {cat=MkMonoidalR{}} rec@(MkStrongComonadR {}) = rec.comonadR.counit


  ||| Convert this into a `CostrongFunctorR`.
  public export %inline
  (.costrongFunctorR) : (rec : StrongComonadR cat) -> CostrongFunctorR cat
  (.costrongFunctorR) (MkStrongComonadR {} {fun}) = MkCostrongFunctorR fun

  ||| The left tensor costrength.
  public export %inline
  (.costrongl) : (rec : StrongComonadR cat) -> {a,b : _} ->
                 cat.hom (rec.fun (cat.tensor a b)) (cat.tensor a (rec.fun b))
  (.costrongl) rec@(MkStrongComonadR {}) = rec.costrongFunctorR.costrongl

  ||| The right tensor costrength.
  public export %inline
  (.costrongr) : (rec : StrongComonadR cat) -> {a,b : _} ->
                 cat.hom (rec.fun (cat.tensor a b)) (cat.tensor (rec.fun a) b)
  (.costrongr) rec@(MkStrongComonadR {}) = rec.costrongFunctorR.costrongr


  ||| Convert this into a `StrongComonadR`.
  public export %inline
  (.strongComonadR) : (rec : StrongComonadR cat) -> StrongComonadR cat
  (.strongComonadR) = id
