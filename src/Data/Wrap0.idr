module Data.Wrap0

%default total


public export
record Wrap0 (a : Type) where
  constructor W0
  0 runW0 : a


public export
liftW : (0 f : a -> b) -> Wrap0 a -> Wrap0 b
liftW f x = W0 (f x.runW0)

public export
liftW2 : (0 f : a -> b -> c) -> Wrap0 a -> Wrap0 b -> Wrap0 c
liftW2 f x y = W0 (f x.runW0 y.runW0)


public export
Type0 : Type
Type0 = Wrap0 Type
