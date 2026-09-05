||| This module defines `Wrap0`, a wrapper type containing a value
||| that is present at compile-time, but erased during run-time. This
||| wrapper is used to define categories with erased objects, such as
||| the category of types `Typ`.
module Data.Wrap0

%default total

||| A wrapper for a value that is erased at runtime.
public export
record Wrap0 (a : Type) where
  constructor W0
  0 runW0 : a

||| Lift a function to act on `Wrap0` values. Since the values it
||| operates on are erased, the function does not have to exist at
||| runtime.
public export
liftW : (0 f : a -> b) -> Wrap0 a -> Wrap0 b
liftW f x = W0 (f x.runW0)

||| Lift a binary operation to act on `Wrap0` values. Since the values
||| it operates on are erased, the function does not have to exist at
||| runtime.
public export
liftW2 : (0 f : a -> b -> c) -> Wrap0 a -> Wrap0 b -> Wrap0 c
liftW2 f x y = W0 (f x.runW0 y.runW0)


||| A type that is erased at runtime.
public export
Type0 : Type
Type0 = Wrap0 Type
