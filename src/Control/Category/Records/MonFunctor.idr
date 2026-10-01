module Control.Category.Records.MonFunctor

import Control.Category
import Control.Category.Records.Category
import Control.Category.Records.Monoidal
import Control.Category.Records.Functor

%default total
%prefix_record_projections off

||| A lax monoidal functor from `cat` to `cat'`.
|||
||| See `LaxMonFunctor` for required laws.
public export
record LaxMonFunctorR (cat,cat' : MonoidalR) where
  constructor MkLaxMonFunctorR
  fun : cat.obj -> cat'.obj
  {auto impl : LaxMonFunctor
    cat.hom cat.tensor cat.unit
    cat'.hom cat'.tensor cat'.unit fun}

||| A type synonym for a lax monoidal endofunctor.
public export %inline
LaxMonEndofunctorR : (cat : MonoidalR) -> Type
LaxMonEndofunctorR cat = LaxMonFunctorR cat cat

namespace LaxMonFunctorR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : LaxMonFunctorR cat cat') -> FunctorR cat.categoryR cat'.categoryR
  (.functorR) {cat=MkMonoidalR{},cat'=MkMonoidalR{}} (MkLaxMonFunctorR {} {fun}) = MkFunctorR fun

  ||| Apply the functor to a morphism in `cat`.
  public export %inline
  (.map) : (rec : LaxMonFunctorR cat cat') -> {a,b : _} ->
           cat.hom a b -> cat'.hom (rec.fun a) (rec.fun b)
  (.map) {cat=MkMonoidalR{},cat'=MkMonoidalR{}} rec@(MkLaxMonFunctorR {}) = rec.functorR.map


  ||| Convert this into a `LaxMonFunctorR`.
  public export %inline
  (.laxMonFunctorR) : (rec : LaxMonFunctorR cat cat') -> LaxMonFunctorR cat cat'
  (.laxMonFunctorR) = id

  ||| The lax monoidal functor action on the tensor product.
  public export %inline
  (.mjoin) : (rec : LaxMonFunctorR cat cat') -> {a,b : _} ->
             cat'.hom (cat'.tensor (rec.fun a) (rec.fun b)) (rec.fun (cat.tensor a b))
  (.mjoin) rec = mjoin @{rec.impl}

  ||| The lax monoidal functor action on the unit object.
  public export %inline
  (.munit) : (rec : LaxMonFunctorR cat cat') -> cat'.hom cat'.unit (rec.fun cat.unit)
  (.munit) rec = munit @{rec.impl}


||| A (strong) monoidal functor from `cat` to `cat'`.
|||
||| See `MonFunctor` for required laws.
public export
record MonFunctorR (cat,cat' : MonoidalR) where
  constructor MkMonFunctorR
  fun : cat.obj -> cat'.obj
  {auto impl : MonFunctor
    cat.hom cat.tensor cat.unit
    cat'.hom cat'.tensor cat'.unit fun}

||| A type synonym for a monoidal endofunctor.
public export %inline
MonEndofunctorR : (cat : MonoidalR) -> Type
MonEndofunctorR cat = MonFunctorR cat cat

namespace MonFunctorR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : MonFunctorR cat cat') -> FunctorR cat.categoryR cat'.categoryR
  (.functorR) {cat=MkMonoidalR{},cat'=MkMonoidalR{}} (MkMonFunctorR {} {fun}) = MkFunctorR fun

  ||| Apply the functor to a morphism in `cat`.
  public export %inline
  (.map) : (rec : MonFunctorR cat cat') -> {a,b : _} ->
           cat.hom a b -> cat'.hom (rec.fun a) (rec.fun b)
  (.map) {cat=MkMonoidalR{},cat'=MkMonoidalR{}} rec@(MkMonFunctorR {}) = rec.functorR.map


  ||| Convert this into a `LaxMonFunctorR`.
  public export %inline
  (.laxMonFunctorR) : (rec : MonFunctorR cat cat') -> LaxMonFunctorR cat cat'
  (.laxMonFunctorR) {cat=MkMonoidalR{},cat'=MkMonoidalR{}} (MkMonFunctorR {} {fun}) = MkLaxMonFunctorR fun

  ||| The monoidal functor action on the tensor product.
  public export %inline
  (.mjoin) : (rec : MonFunctorR cat cat') -> {a,b : _} ->
             cat'.hom (cat'.tensor (rec.fun a) (rec.fun b)) (rec.fun (cat.tensor a b))
  (.mjoin) {cat=MkMonoidalR{},cat'=MkMonoidalR{}} rec@(MkMonFunctorR {}) = rec.laxMonFunctorR.mjoin

  ||| The monoidal functor action on the unit object.
  public export %inline
  (.munit) : (rec : MonFunctorR cat cat') -> cat'.hom cat'.unit (rec.fun cat.unit)
  (.munit) {cat=MkMonoidalR{},cat'=MkMonoidalR{}} rec@(MkMonFunctorR {}) = rec.laxMonFunctorR.munit


  ||| Convert this into a `MonFunctorR`.
  public export %inline
  (.monFunctorR) : (rec : MonFunctorR cat cat') -> MonFunctorR cat cat'
  (.monFunctorR) = id

  ||| The inverse monoidal functor action on the tensor product.
  public export %inline
  (.mjoin') : (rec : MonFunctorR cat cat') -> {a,b : _} ->
             cat'.hom (rec.fun (cat.tensor a b)) (cat'.tensor (rec.fun a) (rec.fun b))
  (.mjoin') rec = mjoin' @{rec.impl}

  ||| The inverse monoidal functor action on the unit object.
  public export %inline
  (.munit') : (rec : MonFunctorR cat cat') -> cat'.hom (rec.fun cat.unit) cat'.unit
  (.munit') rec = munit' @{rec.impl}


||| An endofunctor has *tensorial strength* if it is compatible with a
||| monoidal category's tensor product.
|||
||| See `StrongFunctor` for required laws.
public export
record StrongFunctorR (cat : MonoidalR) where
  constructor MkStrongFunctorR
  fun : cat.obj -> cat.obj
  {auto impl : StrongFunctor cat.hom cat.tensor fun}

namespace StrongFunctorR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : StrongFunctorR cat) -> EndofunctorR cat.categoryR
  (.functorR) {cat=MkMonoidalR{}} (MkStrongFunctorR {} {fun}) = MkFunctorR fun

  ||| Apply the functor to a morphism in `cat`.
  public export %inline
  (.map) : (rec : StrongFunctorR cat) -> {a,b : _} ->
           cat.hom a b -> cat.hom (rec.fun a) (rec.fun b)
  (.map) {cat=MkMonoidalR{}} rec@(MkStrongFunctorR {}) = rec.functorR.map

  ||| The left tensor strength.
  public export %inline
  (.strongl) : (rec : StrongFunctorR cat) -> {a,b : _} ->
               cat.hom (cat.tensor a (rec.fun b)) (rec.fun (cat.tensor a b))
  (.strongl) rec = strongl @{rec.impl}

  ||| The right tensor strength.
  public export %inline
  (.strongr) : (rec : StrongFunctorR cat) -> {a,b : _} ->
               cat.hom (cat.tensor (rec.fun a) b) (rec.fun (cat.tensor a b))
  (.strongr) rec = strongr @{rec.impl}


||| An endofunctor has *tensorial costrength* if it is compatible with
||| a monoidal category's tensor product in a way that is dual to a
||| tensorial strength.
|||
||| See `CostrongFunctor` for required laws.
public export
record CostrongFunctorR (cat : MonoidalR) where
  constructor MkCostrongFunctorR
  fun : cat.obj -> cat.obj
  {auto impl : CostrongFunctor cat.hom cat.tensor fun}

namespace CostrongFunctorR
  ||| Convert this into a `FunctorR`.
  public export %inline
  (.functorR) : (rec : CostrongFunctorR cat) -> EndofunctorR cat.categoryR
  (.functorR) {cat=MkMonoidalR{}} (MkCostrongFunctorR {} {fun}) = MkFunctorR fun

  ||| Apply the functor to a morphism in `cat`.
  public export %inline
  (.map) : (rec : CostrongFunctorR cat) -> {a,b : _} ->
           cat.hom a b -> cat.hom (rec.fun a) (rec.fun b)
  (.map) {cat=MkMonoidalR{}} rec@(MkCostrongFunctorR {}) = rec.functorR.map

  ||| The left tensor costrength.
  public export %inline
  (.costrongl) : (rec : CostrongFunctorR cat) -> {a,b : _} ->
               cat.hom (rec.fun (cat.tensor a b)) (cat.tensor a (rec.fun b))
  (.costrongl) rec = costrongl @{rec.impl}

  ||| The right tensor costrength.
  public export %inline
  (.costrongr) : (rec : CostrongFunctorR cat) -> {a,b : _} ->
               cat.hom (rec.fun (cat.tensor a b)) (cat.tensor (rec.fun a) b)
  (.costrongr) rec = costrongr @{rec.impl}
