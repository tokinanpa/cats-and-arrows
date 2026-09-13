||| This module provides a compatibility layer between the traditional
||| Haskell arrow hierarchy and the categorical interfaces of this
||| library. These functions may be easier to write code with for users
||| who are already familiar with arrows.
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
import Data.Wrap0

%default total

export infixr 7 ***
export infixr 7 &&&
export infixr 6 +++
export infixr 6 \|/

------------------------------------------------------------
-- Interface
------------------------------------------------------------

public export
0 Arrow : (arr : Hom Type0) -> Type
Arrow arr = (Promonad0 arr, EndoBinoidal arr (liftW2 Pair))

public export
0 ArrowChoice : (arr : Hom Type0) -> Type
ArrowChoice arr = (Arrow arr, EndoBinoidal arr (liftW2 Either))

public export
0 ArrowLoop : (arr : Hom Type0) -> Type
ArrowLoop arr = (Promonad0 arr, Traced arr (liftW2 Pair) (W0 ()))


------------------------------------------------------------
-- Functions
------------------------------------------------------------

public export %inline
arrow : Arrow arr => (a -> b) -> arr (W0 a) (W0 b)
arrow = funitW

public export %inline
first : Arrow arr => arr (W0 a) (W0 b) -> arr (W0 (a, c)) (W0 (b, c))
first = mapl' {f=liftW2 Pair,a=W0 _,b=W0 _,c=W0 _}

public export %inline
second : Arrow arr => arr (W0 a) (W0 b) -> arr (W0 (c, a)) (W0 (c, b))
second = mapr' {f=liftW2 Pair,a=W0 _,b=W0 _,c=W0 _}

public export
(***) : Arrow arr => arr (W0 a) (W0 b) -> arr (W0 a') (W0 b') -> arr (W0 (a, a')) (W0 (b, b'))
f *** g = first f >>> second g

public export
(&&&) : Arrow arr => arr (W0 a) (W0 b) -> arr (W0 a) (W0 b') -> arr (W0 a) (W0 (b, b'))
f &&& g = arrow dup >>> f *** g

public export
liftA2 : Arrow arr => (a -> b -> c) -> arr (W0 d) (W0 a) -> arr (W0 d) (W0 b) -> arr (W0 d) (W0 c)
liftA2 op f g = (f &&& g) >>> arrow (uncurry op)


public export %inline
left : ArrowChoice arr => arr (W0 a) (W0 b) -> arr (W0 $ Either a c) (W0 $ Either b c)
left = mapl' {f=liftW2 Either,a=W0 _,b=W0 _,c=W0 _}

public export %inline
right : ArrowChoice arr => arr (W0 a) (W0 b) -> arr (W0 $ Either c a) (W0 $ Either c b)
right = mapr' {f=liftW2 Either,a=W0 _,b=W0 _,c=W0 _}

public export
(+++) : ArrowChoice arr => arr (W0 a) (W0 b) -> arr (W0 a') (W0 b') -> arr (W0 $ Either a a') (W0 $ Either b b')
f +++ g = left f >>> right g

public export
(\|/) : ArrowChoice arr => arr (W0 a) (W0 b) -> arr (W0 a') (W0 b) -> arr (W0 $ Either a a') (W0 b)
f \|/ g = f +++ g >>> arrow fromEither


public export %inline
loop : ArrowLoop arr => arr (W0 (a, c)) (W0 (b, c)) -> arr (W0 a) (W0 b)
loop = tracer {ten=liftW2 Pair,a=W0 _,b=W0 _,c=W0 _}
