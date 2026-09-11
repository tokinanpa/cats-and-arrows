module Control.Category.Instances.Sum

import Control.Category
import Control.Category.Records
import Data.Morphisms

%default total

||| The sum category of two other categories.
public export
data Sum : (cat : a -> b -> Type) -> (cat' : a' -> b' -> Type) ->
            Either a a' -> Either b b' -> Type where
  Left : forall cat,cat'. cat x y -> Sum cat cat' (Left x) (Left y)
  Right : forall cat,cat'. cat' x y -> Sum cat cat' (Right x) (Right y)


------------------------------------------------------------
-- Interface Style
------------------------------------------------------------

public export
Semigroupoid cat => Semigroupoid cat' => Semigroupoid (Sum cat cat') where
  Left f . Left g = Left (f . g)
  Right f . Right g = Right (f . g)

public export
Category cat => Category cat' => Category (Sum cat cat') where
  id {a=Left _} = Left id
  id {a=Right _} = Right id
  Left f . Left g = Left (f . g)
  Right f . Right g = Right (f . g)


public export
[Horizontal] CatFunctor catF catF' f => CatFunctor catG catG' g =>
    CatFunctor (Sum catF catG) (Sum catF' catG') (Prelude.bimap f g) where
  map (Left f) = Left (map f)
  map (Right f) = Right (map f)


------------------------------------------------------------
-- Record Style
------------------------------------------------------------

namespace SemigroupoidR
  public export
  Sum : (cat,cat' : SemigroupoidR) -> SemigroupoidR
  Sum (MkSemigroupoidR cat) (MkSemigroupoidR cat') = MkSemigroupoidR (Sum cat cat')

namespace CategoryR
  public export
  Sum : (cat,cat' : CategoryR) -> CategoryR
  Sum (MkCategoryR cat) (MkCategoryR cat') = MkCategoryR (Sum cat cat')

public export
FunctorSum : (f : FunctorR catF catF') -> (g : FunctorR catG catG') ->
              FunctorR (Sum catF catG) (Sum catF' catG')
FunctorSum {catF=MkCategoryR {},catF'=MkCategoryR {},catG=MkCategoryR {},catG'=MkCategoryR {}}
  (MkFunctorR f) (MkFunctorR g) = MkFunctorR (bimap f g) {impl = Horizontal}
