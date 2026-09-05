||| This module defines the product of two categories.
module Control.Category.Instances.Prod

import Control.Category
import Control.Category.Records
import Data.Morphisms

%default total

||| The product category of two other categories.
public export
record Prod (cat : a -> b -> Type) (cat' : a' -> b' -> Type)
            (x : (a, a')) (y : (b, b')) where
  constructor MkProd
  fst : cat (fst x) (fst y)
  snd : cat' (snd x) (snd y)


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Semigroupoid cat => Semigroupoid cat' => Semigroupoid (Prod cat cat') where
  MkProd f f' . MkProd g g' = MkProd (f . g) (f' . g')

public export
Category cat => Category cat' => Category (Prod cat cat') where
  id = MkProd id id
  MkProd f f' . MkProd g g' = MkProd (f . g) (f' . g')


-- Functor/Bifunctor equivalence
-- Unfortunately, we can't make any of these resolve automatically
-- due to the use of `curry`/`uncurry`

namespace CatFunctor
  public export
  [FromCatBifunctor] CatBifunctor catA catB cat' f => CatFunctor (Prod catA catB) cat' (uncurry f) where
    map {a=(_,_),b=(_,_)} (MkProd f g) = bimap f g

  public export
  [FromBifunctor] Bifunctor f => CatFunctor (Prod Morphism Morphism) Morphism (uncurry f) where
    map {a=(_,_),b=(_,_)} (MkProd (Mor f) (Mor g)) = Mor (bimap f g)

  public export
  [FromBifunctor'] Bifunctor f => CatFunctor (Prod (~~>) (~~>)) (~~>) (uncurry f) where
    map {a=(_,_),b=(_,_)} (MkProd f g) = Prelude.bimap f g

namespace CatBifunctor
  public export
  [FromCatFunctor] CatFunctor (Prod catA catB) cat' f => CatBifunctor catA catB cat' (curry f) where
    bimap f' g = map {cat=Prod catA catB,f} (MkProd f' g)

public export
[Horizontal] CatFunctor catF catF' f => CatFunctor catG catG' g =>
    CatFunctor (Prod catF catG) (Prod catF' catG') (Prelude.bimap f g) where
  map {a=(_,_),b=(_,_)} (MkProd f g) = MkProd (map f) (map g)


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Prod : (cat,cat' : SemigroupoidR) -> SemigroupoidR
  Prod (MkSemigroupoidR cat) (MkSemigroupoidR cat') = MkSemigroupoidR (Prod cat cat')

namespace CategoryR
  public export
  Prod : (cat,cat' : CategoryR) -> CategoryR
  Prod (MkCategoryR cat) (MkCategoryR cat') = MkCategoryR (Prod cat cat')

public export
FunctorProd : (f : FunctorR catF catF') -> (g : FunctorR catG catG') ->
              FunctorR (Prod catF catG) (Prod catF' catG')
FunctorProd {catF=MkCategoryR {},catF'=MkCategoryR {},catG=MkCategoryR {},catG'=MkCategoryR {}}
  (MkFunctorR f) (MkFunctorR g) = MkFunctorR (bimap f g) {impl = Horizontal}
