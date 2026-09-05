||| This module provides a compatibility layer between the traditional
||| Haskell arrow hierarchy and the categorical interfaces of this
||| library. These functions may be easier to write code with for users
||| who are already familiar with arrows.
|||
||| Note that this interface isn't exactly identical to regular arrows.
||| In particular, these functions currently require the types to be
||| available at runtime. This will likely be changed in the future.
|||
||| Currently, the `Arrow`, `ArrowChoice` and `ArrowLoop` interfaces
||| are fully defined. `ArrowPlus` may also be defined in the future
||| if I ever get around to adding support for enriched categories.
|||
||| `ArrowApply` will most likely never be added, as it is not very
||| well-behaved categorically and is also essentially useless.
module Control.Arrow

import public Control.Category.Core as Control.Category
import Control.Category
import Control.Category.Promonad
import Control.Category.Traced
import Data.Either
import Data.Morphisms

%default total

export infixr 7 ***
export infixr 7 &&&
export infixr 6 +++
export infixr 6 \|/

------------------------------------------------------------
-- Interface
------------------------------------------------------------

public export
Arrow : (arr : Hom Type) -> Type
Arrow arr = (Promonad arr, EndoBinoidal arr Pair)

public export
ArrowChoice : (arr : Hom Type) -> Type
ArrowChoice arr = (Arrow arr, EndoBinoidal arr Either)

public export
ArrowLoop : (arr : Hom Type) -> Type
ArrowLoop arr = (Promonad arr, Traced arr Pair ())


------------------------------------------------------------
-- Functions
------------------------------------------------------------

public export
arrow : Arrow arr => (a -> b) -> arr a b
arrow = funit

public export
first : Arrow arr => {a,b,c : _} -> arr a b -> arr (a, c) (b, c)
first = mapl'

public export
second : Arrow arr => {a,b,c : _} -> arr a b -> arr (c, a) (c, b)
second = mapr'

public export
(***) : Arrow arr => {a,a',b,b' : _} -> arr a b -> arr a' b' -> arr (a, a') (b, b')
f *** g = mapl' f >>> mapr' g

public export
(&&&) : Arrow arr => {a,b,b' : _} -> arr a b -> arr a b' -> arr a (b, b')
f &&& g = arrow dup >>> f *** g

public export
liftA2 : Arrow arr => {a,b,c,d : _} -> (a -> b -> c) -> arr d a -> arr d b -> arr d c
liftA2 op f g = (f &&& g) >>> arrow (uncurry op)


public export
left : ArrowChoice arr => {a,b,c : _} -> arr a b -> arr (Either a c) (Either b c)
left = mapl'

public export
right : ArrowChoice arr => {a,b,c : _} -> arr a b -> arr (Either c a) (Either c b)
right = mapr'

public export
(+++) : ArrowChoice arr => {a,a',b,b' : _} -> arr a b -> arr a' b' -> arr (Either a a') (Either b b')
f +++ g = mapl' f >>> mapr' g

public export
(\|/) : ArrowChoice arr => {a,a',b : _} -> arr a b -> arr a' b -> arr (Either a a') b
f \|/ g = f +++ g >>> arrow fromEither


public export
loop : ArrowLoop arr => {a,b,c : _} -> arr (a, c) (b, c) -> arr a b
loop = tracer
