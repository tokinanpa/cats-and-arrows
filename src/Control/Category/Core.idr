module Control.Category.Core

import Data.Morphisms
import Data.Profunctor.Types

%default total


||| A type synonym for `obj -> obj -> Type` to simplify definitions.
public export
Hom : Type -> Type
Hom obj = obj -> obj -> Type

export infixr 0 ~~>

||| A type synonym for (non-dependent) functions.
public export
(~~>) : Type -> Type -> Type
(~~>) a b = a -> b

------------------------------------------------------------
-- Interface
------------------------------------------------------------

||| A *category* is a generalized function type with a notion of
||| composition and of identity. The elements of this type are
||| typically called *morphisms*.
|||
||| This is the interface-style definition of a category. For the
||| record-style definition, see `Control.Category.Records.CategoryR`.
|||
||| Laws:
||| * `id . f = f`
||| * `f . id = f`
||| * `(f . g) . h = f . (g . h)`
public export
interface Category (0 cat : Hom obj) | cat where
  constructor MkCategory
  ||| The identity morphism of an object `a`.
  id : forall a. cat a a
  ||| Binary right-to-left composition of morphisms.
  (.) : forall a,b,c. cat b c -> cat a b -> cat a c

export infixl 5 <<<
export infixr 5 >>>

||| A synonym for right-to-left category composition that may be easier
||| to read. The arrow shows the direction the morphisms are composed.
public export %inline %tcinline
(<<<) : Category cat => cat b c -> cat a b -> cat a c
(<<<) = (.)

||| A synonym for left-to-right category composition that may be easier
||| to read. The arrow shows the direction the morphisms are composed.
public export %inline %tcinline
(>>>) : Category cat => cat a b -> cat b c -> cat a c
(>>>) = flip (.)


------------------------------------------------------------
-- Existing Instances
------------------------------------------------------------

||| The `Morphism` type from `Data.Morphisms` forms a category.
public export
Category Morphism where
  id = Mor id
  Mor f . Mor g = Mor (f . g)

namespace Category
  ||| Non-dependent functions form a category with the ordinary
  ||| composition and identity functions.
  public export
  [Function] Category (~~>) where
    id = Prelude.id
    (.) = Prelude.(.)

||| Kleislimorphisms (monadic functions) form a category.
public export
Monad m => Category (Kleislimorphism m) where
  id = Kleisli pure
  Kleisli f . Kleisli g = Kleisli (f <=< g)

public export
Monad m => Category (Star m) where
  id = MkStar pure
  MkStar f . MkStar g = MkStar (f <=< g)
