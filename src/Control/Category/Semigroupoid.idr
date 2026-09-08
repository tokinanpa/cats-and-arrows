module Control.Category.Semigroupoid

import Control.Category.Core
import Data.Morphisms
import Data.Profunctor.Types

%default total

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *semigroupoid* is a category that lacks identity morphisms.
|||
||| This is the interface-style definition of a semigroupoid. For the
||| record-style definition, see `Control.Category.Records.SemigroupoidR`.
|||
||| Laws:
||| * `(f . g) . h = f . (g . h)`
public export
interface Semigroupoid (0 cat : obj -> obj -> Type) | cat where
  constructor MkSemigroupoid
  (.) : {a,b,c : _} -> cat b c -> cat a b -> cat a c


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

namespace Semigroupoid
  ||| Convert a category into a semigroupoid.
  public export
  [FromCategory] Category cat => Semigroupoid cat where
    (.) = Core.(.)


-- These instances should not be used unless necessary, as they have
-- poor runtime quantity behavior. Prefer `Typ` over base's `Morphism`
-- and `Kleisli` over base's `Kleislimorphism`.

public export
Semigroupoid Morphism where
  Mor f . Mor g = Mor (f . g)

namespace Semigroupoid
  public export
  [Function] Semigroupoid (~~>) where
    (.) = Prelude.(.)

public export
Monad m => Semigroupoid (Kleislimorphism m) where
  Kleisli f . Kleisli g = Kleisli (f <=< g)

public export
Monad m => Semigroupoid (Star m) where
  MkStar f . MkStar g = MkStar (f <=< g)

public export
Semigroupoid Tagged where
  Tag x . Tag _ = Tag x

