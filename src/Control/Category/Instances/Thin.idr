||| This module defines thin categories, which are categorifications
||| of certain relations. Explicitly, any reflexive and transitive
||| relation on a particular type also forms a category on that type
||| where there is at most one morphism between any two objects.
|||
||| It can be demonstrated that thin *monoidal* categories correspond
||| to preordered monoids. This makes it possible to use string diagram
||| notation to prove inequalities on monoids.
|||
||| It can be further demonstrated that thin *bimonoidal* categories
||| correspond to preordered semirings. This makes it possible to use
||| bimonoidal sheet diagram notation to prove inequalities on
||| semirings (represented here by the interface `Num`).
module Control.Category.Instances.Thin

import Control.Category
import Control.Category.Records
import public Control.Relation
import public Control.Order

%default total

public export
[Thin] Preorder ty rel => Category rel where
  id = reflexive
  (.) = flip transitive


public export
record RelMonoid ty (rel : Rel ty) where
  constructor MkRelMonoid
  {auto impl : Monoid ty}
  cong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x <+> x') (y <+> y')
  assoc : {x,y,z : ty} -> rel ((x <+> y) <+> z) (x <+> (y <+> z))
  assoc' : {x,y,z : ty} -> rel (x <+> (y <+> z)) ((x <+> y) <+> z)
  unitl : {x : ty} -> rel (Prelude.neutral <+> x) x
  unitl' : {x : ty} -> rel x (Prelude.neutral <+> x)
  unitr : {x : ty} -> rel (x <+> Prelude.neutral) x
  unitr' : {x : ty} -> rel x (x <+> Prelude.neutral)

public export %inline
mkRelMonoid :
  forall ty,rel. Reflexive ty rel =>
  {auto impl : Monoid ty} ->
  (cong : {x,x',y,y': ty} -> rel x y -> rel x' y' -> rel (x <+> x') (y <+> y')) ->
  (0 assoc : {x,y,z : ty} -> (x <+> y) <+> z = x <+> (y <+> z)) ->
  (0 unitl : {x : ty} -> Prelude.neutral <+> x = x) ->
  (0 unitr : {x : ty} -> x <+> Prelude.neutral = x) ->
  RelMonoid ty rel
mkRelMonoid c a l r =
  MkRelMonoid c
    (replace {p = rel _} a reflexive)
    (replace {p = rel _} (sym a) reflexive)
    (replace {p = rel _} l reflexive)
    (replace {p = rel _} (sym l) reflexive)
    (replace {p = rel _} r reflexive)
    (replace {p = rel _} (sym r) reflexive)

public export
record RelCommMonoid ty (rel : Rel ty) where
  constructor MkRelCommMonoid
  {auto impl : Monoid ty}
  cong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x <+> x') (y <+> y')
  assoc : {x,y,z : ty} -> rel ((x <+> y) <+> z) (x <+> (y <+> z))
  unit : {x : ty} -> rel (Prelude.neutral <+> x) x
  unit' : {x : ty} -> rel x (Prelude.neutral <+> x)
  comm : {x,y : ty} -> rel (x <+> y) (y <+> x)

namespace RelCommMonoid
  public export %inline
  relMonoid : Preorder ty rel => (rec : RelCommMonoid ty rel) -> RelMonoid ty rel
  relMonoid (MkRelCommMonoid c a u u' cm) =
    MkRelMonoid c a
    (transitive (c reflexive cm) $ transitive cm $ transitive a $ transitive cm $ c cm reflexive)
     u u' (transitive cm u) (transitive u' cm)

  public export %inline
  (.relMonoid) : Preorder ty rel => (rec : RelCommMonoid ty rel) -> RelMonoid ty rel
  (.relMonoid) = relMonoid

public export %inline
mkRelCommMonoid :
  forall ty,rel. Reflexive ty rel =>
  {auto impl : Monoid ty} ->
  (cong : {x,x',y,y' : _} -> rel x y -> rel x' y' -> rel (x <+> x') (y <+> y')) ->
  (0 assoc : {x,y,z : ty} -> (x <+> y) <+> z = x <+> (y <+> z)) ->
  (0 unit : {x : ty} -> Prelude.neutral <+> x = x) ->
  (0 comm : {x,y : ty} -> x <+> y = y <+> x) ->
  RelCommMonoid ty rel
mkRelCommMonoid c a u cm =
  MkRelCommMonoid c
    (replace {p = rel _} a reflexive)
    (replace {p = rel _} u reflexive)
    (replace {p = rel _} (sym u) reflexive)
    (replace {p = rel _} cm reflexive)


public export
record RelNearRing ty (rel : Rel ty) where
  constructor MkRelNearRing
  {auto impl : Num ty}
  plusCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x + x') (y + y')
  multCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x * x') (y * y')
  plusAssoc : {x,y,z : ty} -> rel ((x + y) + z) (x + (y + z))
  plusAssoc' : {x,y,z : ty} -> rel (x + (y + z)) ((x + y) + z)
  multAssoc : {x,y,z : ty} -> rel ((x * y) * z) (x * (y * z))
  multAssoc' : {x,y,z : ty} -> rel (x * (y * z)) ((x * y) * z)
  plusUnitl : {x : ty} -> rel (0 + x) x
  plusUnitl' : {x : ty} -> rel x (0 + x)
  multUnitl : {x : ty} -> rel (1 * x) x
  multUnitl' : {x : ty} -> rel x (1 * x)
  plusUnitr : {x : ty} -> rel (x + 0) x
  plusUnitr' : {x : ty} -> rel x (x + 0)
  multUnitr : {x : ty} -> rel (x * 1) x
  multUnitr' : {x : ty} -> rel x (x * 1)
  distribl : {x,y,z : ty} -> rel (x * (y + z)) (x * y + x * z)
  distribl' : {x,y,z : ty} -> rel (x * y + x * z) (x * (y + z))
  distribr : {x,y,z : ty} -> rel ((x + y) * z) (x * z + y * z)
  distribr' : {x,y,z : ty} -> rel (x * z + y * z) ((x + y) * z)
  absorbl : {x : ty} -> rel (x * 0) 0
  absorbl' : {x : ty} -> rel 0 (x * 0)
  absorbr : {x : ty} -> rel (0 * x) 0
  absorbr' : {x : ty} -> rel 0 (0 * x)

public export %inline
mkRelNearRing :
  forall ty,rel. Reflexive ty rel =>
  {auto impl : Num ty} ->
  (plusCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x + x') (y + y')) ->
  (multCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x * x') (y * y')) ->
  (0 plusAssoc : {x,y,z : ty} -> (x + y) + z = x + (y + z)) ->
  (0 multAssoc : {x,y,z : ty} -> (x * y) * z = x * (y * z)) ->
  (0 plusUnitl : {x : ty} -> 0 + x = x) ->
  (0 multUnitl : {x : ty} -> 1 * x = x) ->
  (0 plusUnitr : {x : ty} -> x + 0 = x) ->
  (0 multUnitr : {x : ty} -> x * 1 = x) ->
  (0 distribl : {x,y,z : ty} -> x * (y + z) = x * y + x * z) ->
  (0 distribr : {x,y,z : ty} -> (x + y) * z = x * z + y * z) ->
  (0 absorbl : {x : ty} -> x * 0 = 0) ->
  (0 absorbr : {x : ty} -> 0 * x = 0) ->
  RelNearRing ty rel
mkRelNearRing pc mc pa ma pl ml pr mr dl dr al ar =
  MkRelNearRing pc mc
    (replace {p = rel _} pa reflexive)
    (replace {p = rel _} (sym pa) reflexive)
    (replace {p = rel _} ma reflexive)
    (replace {p = rel _} (sym ma) reflexive)
    (replace {p = rel _} pl reflexive)
    (replace {p = rel _} (sym pl) reflexive)
    (replace {p = rel _} ml reflexive)
    (replace {p = rel _} (sym ml) reflexive)
    (replace {p = rel _} pr reflexive)
    (replace {p = rel _} (sym pr) reflexive)
    (replace {p = rel _} mr reflexive)
    (replace {p = rel _} (sym mr) reflexive)
    (replace {p = rel _} dl reflexive)
    (replace {p = rel _} (sym dl) reflexive)
    (replace {p = rel _} dr reflexive)
    (replace {p = rel _} (sym dr) reflexive)
    (replace {p = rel _} al reflexive)
    (replace {p = rel _} (sym al) reflexive)
    (replace {p = rel _} ar reflexive)
    (replace {p = rel _} (sym ar) reflexive)

namespace RelNearRing
  public export %inline
  plusMonoid : (rec : RelNearRing ty rel) -> RelMonoid ty rel
  plusMonoid (MkRelNearRing c _ a a' _ _ l l' _ _ r r' {}) =
    MkRelMonoid @{Additive} c a a' l l' r r'

  public export %inline
  (.plusMonoid) : (rec : RelNearRing ty rel) -> RelMonoid ty rel
  (.plusMonoid) = plusMonoid

  public export %inline
  multMonoid : (rec : RelNearRing ty rel) -> RelMonoid ty rel
  multMonoid (MkRelNearRing _ c _ _ a a' _ _ l l' _ _ r r' {}) =
    MkRelMonoid @{Multiplicative} c a a' l l' r r'

  public export %inline
  (.multMonoid) : (rec : RelNearRing ty rel) -> RelMonoid ty rel
  (.multMonoid) = multMonoid

public export
record RelSemiring ty (rel : Rel ty) where
  constructor MkRelSemiring
  {auto impl : Num ty}
  plusCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x + x') (y + y')
  multCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x * x') (y * y')
  plusAssoc : {x,y,z : ty} -> rel ((x + y) + z) (x + (y + z))
  multAssoc : {x,y,z : ty} -> rel ((x * y) * z) (x * (y * z))
  multAssoc' : {x,y,z : ty} -> rel (x * (y * z)) ((x * y) * z)
  plusUnit : {x : ty} -> rel (0 + x) x
  plusUnit' : {x : ty} -> rel x (0 + x)
  multUnitl : {x : ty} -> rel (1 * x) x
  multUnitl' : {x : ty} -> rel x (1 * x)
  multUnitr : {x : ty} -> rel (x * 1) x
  multUnitr' : {x : ty} -> rel x (x * 1)
  distribl : {x,y,z : ty} -> rel (x * (y + z)) (x * y + x * z)
  distribl' : {x,y,z : ty} -> rel (x * y + x * z) (x * (y + z))
  distribr : {x,y,z : ty} -> rel ((x + y) * z) (x * z + y * z)
  distribr' : {x,y,z : ty} -> rel (x * z + y * z) ((x + y) * z)
  absorbl : {x : ty} -> rel (x * 0) 0
  absorbl' : {x : ty} -> rel 0 (x * 0)
  absorbr : {x : ty} -> rel (0 * x) 0
  absorbr' : {x : ty} -> rel 0 (0 * x)
  plusComm : {x,y : ty} -> rel (x + y) (y + x)

public export %inline
mkRelSemiring :
  forall ty,rel. Reflexive ty rel =>
  {auto impl : Num ty} ->
  (plusCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x + x') (y + y')) ->
  (multCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x * x') (y * y')) ->
  (0 plusAssoc : {x,y,z : ty} -> (x + y) + z = x + (y + z)) ->
  (0 multAssoc : {x,y,z : ty} -> (x * y) * z = x * (y * z)) ->
  (0 plusUnit : {x : ty} -> 0 + x = x) ->
  (0 multUnitl : {x : ty} -> 1 * x = x) ->
  (0 multUnitr : {x : ty} -> x * 1 = x) ->
  (0 distribl : {x,y,z : ty} -> x * (y + z) = x * y + x * z) ->
  (0 distribr : {x,y,z : ty} -> (x + y) * z = x * z + y * z) ->
  (0 absorbl : {x : ty} -> x * 0 = 0) ->
  (0 absorbr : {x : ty} -> 0 * x = 0) ->
  (0 plusComm : {x,y : ty} -> x + y = y + x) ->
  RelSemiring ty rel
mkRelSemiring pc mc pa ma pu ml mr dl dr al ar pcm =
  MkRelSemiring pc mc
    (replace {p = rel _} pa reflexive)
    (replace {p = rel _} ma reflexive)
    (replace {p = rel _} (sym ma) reflexive)
    (replace {p = rel _} pu reflexive)
    (replace {p = rel _} (sym pu) reflexive)
    (replace {p = rel _} ml reflexive)
    (replace {p = rel _} (sym ml) reflexive)
    (replace {p = rel _} mr reflexive)
    (replace {p = rel _} (sym mr) reflexive)
    (replace {p = rel _} dl reflexive)
    (replace {p = rel _} (sym dl) reflexive)
    (replace {p = rel _} dr reflexive)
    (replace {p = rel _} (sym dr) reflexive)
    (replace {p = rel _} al reflexive)
    (replace {p = rel _} (sym al) reflexive)
    (replace {p = rel _} ar reflexive)
    (replace {p = rel _} (sym ar) reflexive)
    (replace {p = rel _} pcm reflexive)

namespace RelSemiring
  public export %inline
  relNearRing : Preorder ty rel => (rec : RelSemiring ty rel) -> RelNearRing ty rel
  relNearRing (MkRelSemiring pc mc pa ma ma' pu pu' ml ml' mr mr' dl dl' dr dr' al al' ar ar' pcm) =
    MkRelNearRing
      pc mc pa
      (transitive (pc reflexive pcm) $ transitive pcm $ transitive pa $ transitive pcm $ pc pcm reflexive)
      ma ma' pu pu' ml ml' (transitive pcm pu) (transitive pu' pcm) mr mr' dl dl' dr dr' al al' ar ar'

  public export %inline
  (.relNearRing) : Preorder ty rel => (rec : RelSemiring ty rel) -> RelNearRing ty rel
  (.relNearRing) = relNearRing

  public export %inline
  plusMonoid : (rec : RelSemiring ty rel) -> RelCommMonoid ty rel
  plusMonoid (MkRelSemiring c _ a _ _ u u' _ _ _ _ _ _ _ _ _ _ _ _ cm) =
    MkRelCommMonoid @{Additive} c a u u' cm

  public export %inline
  (.plusMonoid) : (rec : RelSemiring ty rel) -> RelCommMonoid ty rel
  (.plusMonoid) = plusMonoid

  public export %inline
  multMonoid : (rec : RelSemiring ty rel) -> RelMonoid ty rel
  multMonoid (MkRelSemiring _ c _ a a' _ _ l l' r r' {}) =
    MkRelMonoid @{Multiplicative} c a a' l l' r r'

  public export %inline
  (.multMonoid) : (rec : RelSemiring ty rel) -> RelMonoid ty rel
  (.multMonoid) = multMonoid

public export
record RelCommSemiring ty (rel : Rel ty) where
  constructor MkRelCommSemiring
  {auto impl : Num ty}
  plusCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x + x') (y + y')
  multCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x * x') (y * y')
  plusAssoc : {x,y,z : ty} -> rel ((x + y) + z) (x + (y + z))
  multAssoc : {x,y,z : ty} -> rel ((x * y) * z) (x * (y * z))
  plusUnit : {x : ty} -> rel (0 + x) x
  plusUnit' : {x : ty} -> rel x (0 + x)
  multUnit : {x : ty} -> rel (1 * x) x
  multUnit' : {x : ty} -> rel x (1 * x)
  distrib : {x,y,z : ty} -> rel (x * (y + z)) (x * y + x * z)
  distrib' : {x,y,z : ty} -> rel (x * y + x * z) (x * (y + z))
  absorb : {x : ty} -> rel (x * 0) 0
  absorb' : {x : ty} -> rel 0 (x * 0)
  plusComm : {x,y : ty} -> rel (x + y) (y + x)
  multComm : {x,y : ty} -> rel (x * y) (y * x)

public export %inline
mkRelCommSemiring :
  forall ty,rel. Reflexive ty rel =>
  {auto impl : Num ty} ->
  (plusCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x + x') (y + y')) ->
  (multCong : {x,x',y,y' : ty} -> rel x y -> rel x' y' -> rel (x * x') (y * y')) ->
  (0 plusAssoc : {x,y,z : ty} -> (x + y) + z = x + (y + z)) ->
  (0 multAssoc : {x,y,z : ty} -> (x * y) * z = x * (y * z)) ->
  (0 plusUnit : {x : ty} -> 0 + x = x) ->
  (0 multUnit : {x : ty} -> 1 * x = x) ->
  (0 distrib : {x,y,z : ty} -> x * (y + z) = x * y + x * z) ->
  (0 absorb : {x : ty} -> x * 0 = 0) ->
  (0 plusComm : {x,y : ty} -> x + y = y + x) ->
  (0 multComm : {x,y : ty} -> x * y = y * x) ->
  RelCommSemiring ty rel
mkRelCommSemiring pc mc pa ma pu mu d a pcm mcm =
  MkRelCommSemiring pc mc
    (replace {p = rel _} pa reflexive)
    (replace {p = rel _} ma reflexive)
    (replace {p = rel _} pu reflexive)
    (replace {p = rel _} (sym pu) reflexive)
    (replace {p = rel _} mu reflexive)
    (replace {p = rel _} (sym mu) reflexive)
    (replace {p = rel _} d reflexive)
    (replace {p = rel _} (sym d) reflexive)
    (replace {p = rel _} a reflexive)
    (replace {p = rel _} (sym a) reflexive)
    (replace {p = rel _} pcm reflexive)
    (replace {p = rel _} mcm reflexive)

namespace RelCommSemiring
  public export %inline
  relSemiring : Preorder ty rel => (rec : RelCommSemiring ty rel) -> RelSemiring ty rel
  relSemiring (MkRelCommSemiring pc mc pa ma pu pu' mu mu' d d' a a' pcm mcm) =
    MkRelSemiring
      pc mc pa ma
      (transitive (mc reflexive mcm) $ transitive mcm $ transitive ma $ transitive mcm $ mc mcm reflexive)
      pu pu' mu mu' (transitive mcm mu) (transitive mu' mcm) d d'
      (transitive mcm $ transitive d $ pc mcm mcm)
      (transitive (pc mcm mcm) $ transitive d' mcm)
      a a' (transitive mcm a) (transitive a' mcm) pcm

  public export %inline
  (.relSemiring) : Preorder ty rel => (rec : RelCommSemiring ty rel) -> RelSemiring ty rel
  (.relSemiring) = relSemiring

  public export %inline
  plusMonoid : (rec : RelCommSemiring ty rel) -> RelCommMonoid ty rel
  plusMonoid (MkRelCommSemiring c _ a _ u u' _ _ _ _ _ _ cm _) =
    MkRelCommMonoid @{Additive} c a u u' cm

  public export %inline
  (.plusMonoid) : (rec : RelCommSemiring ty rel) -> RelCommMonoid ty rel
  (.plusMonoid) = plusMonoid

  public export %inline
  multMonoid : (rec : RelCommSemiring ty rel) -> RelCommMonoid ty rel
  multMonoid (MkRelCommSemiring _ c _ a _ _ u u' _ _ _ _ _ cm) =
    MkRelCommMonoid @{Multiplicative} c a u u' cm

  public export %inline
  (.multMonoid) : (rec : RelCommSemiring ty rel) -> RelCommMonoid ty rel
  (.multMonoid) = multMonoid



namespace CategoryR
  public export
  Thin : (rel : Rel ty) -> Preorder ty rel => CategoryR
  Thin rel = MkCategoryR rel {impl = Thin}

namespace MonoidalR
  public export
  Thin : (rel : Rel ty) -> Preorder ty rel => RelMonoid ty rel -> MonoidalR
  Thin rel (MkRelMonoid c a a' l l' r r') =
    MkMonoidalR rel (<+>) neutral
      {impl = MkMonoidal @{Thin} @{MkCatBifunctor c} a a' l l' r r'}

namespace BraidedR
  public export
  Thin : (rel : Rel ty) -> Preorder ty rel => RelCommMonoid ty rel -> BraidedR
  Thin rel cm@(MkRelCommMonoid {}) =
    MkBraidedR rel (<+>) neutral
      {impl = MkBraided @{(Thin rel cm.relMonoid).impl} cm.comm cm.comm}

namespace BimonoidalR
  public export
  Thin : (rel : Rel ty) -> Preorder ty rel => RelNearRing ty rel -> BimonoidalR
  Thin rel nr@(MkRelNearRing _ _ _ _ _ _ _ _ _ _ _ _ _ _ dl dl' dr dr' al al' ar ar') =
    MkBimonoidalR rel (+) (*) 0 1
      {impl = MkBimonoidal
        @{(Thin rel nr.plusMonoid).impl}
        @{(Thin rel nr.multMonoid).impl}
        dl dl' dr dr' al al' ar ar'}

namespace RigCategoryR
  public export
  Thin : (rel : Rel ty) -> Preorder ty rel => RelSemiring ty rel -> RigCategoryR
  Thin rel sr@(MkRelSemiring _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pcm) =
    MkRigCategoryR rel (+) (*) 0 1
      {impl = ((Thin rel sr.relNearRing).impl, (Thin rel sr.plusMonoid).impl)}

namespace SymRigCategoryR
  public export
  Thin : (rel : Rel ty) -> Preorder ty rel => RelCommSemiring ty rel -> SymRigCategoryR
  Thin rel csr@(MkRelCommSemiring _ _ _ _ _ _ _ _ _ _ _ _ _ mcm) =
    MkSymRigCategoryR rel (+) (*) 0 1
      {impl = ((Thin rel csr.relSemiring).impl, (Thin rel csr.multMonoid).impl)}
