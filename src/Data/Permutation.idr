module Data.Permutation

import Data.DPair
import Data.Nat
import Data.Vect
import Data.List
import Data.List.Quantifiers
import Data.Vect.Quantifiers

%default total

public export
factorial : Integer -> Integer
factorial 0 = 1
factorial 1 = 1
factorial k = product [2..k]


------------------------------------------------------------
-- Definition
------------------------------------------------------------

||| A permutation on `n` elements. This can be used to reorder values
||| in a list or define actions on objects in a symmetric monoidal
||| category.
|||
||| The permutation is stored in Lehmer code form as a list of factorial
||| digits.
public export
data Permutation : (n : Nat) -> Type where
  Nil : Permutation Z
  (::) : Fin (S n) -> Permutation n -> Permutation (S n)


||| Convert a permutation into a `Vect` of factorial digits.
public export
toVect : Permutation n -> Vect n Nat
toVect Nil = Nil
toVect (i :: is) = finToNat i :: toVect is

||| Convert a permutation into a list of factorial digits.
public export
toList : Permutation n -> List Nat
toList = toList . toVect


------------------------------------------------------------
-- Conversions
------------------------------------------------------------

||| Convert a permutation into its *permutation sequence*.
|||
||| The output is a `Vect` of indices where the `i`-th value is the
||| image of `i`. The output is guaranteed to have unique elements.
public export
permSeq : Permutation n -> Vect n (Fin n)
permSeq [] = []
permSeq (i :: is) =
  i :: map (\i' => if finToNat i' >= finToNat i
                   then FS i'
                   else weaken i') (permSeq is)

||| Maybe convert a permutation sequence into a permutation.
|||
||| The input is a `Vect` of indices where the `i`-th value is the
||| image of `i`. The function will return `Nothing` if any of the
||| incides is repeated.
public export
fromPermSeq : Vect n (Fin n) -> Maybe (Permutation n)
fromPermSeq [] = Just [] -- Prevent definition from unwrapping at compile time
fromPermSeq [_] = Just [FZ] -- (& save some time in these trivial cases)
fromPermSeq seq = if unique seq then Just $ inversions seq else Nothing
  where
    unique : forall n. Eq a => Vect n a -> Bool
    unique [] = True
    unique (x :: xs) = all (/= x) xs && unique xs

    inversions : Vect n' (Fin n) -> Permutation n'
    inversions [] = []
    inversions (x :: xs) =
      natToFinLt (count (< x) xs) @{believe_me Oh} :: inversions xs

||| Return the Lehmer code of the permutation as a machine integer.
public export
lehmerCode : Permutation n -> Integer
lehmerCode [] = 0
lehmerCode [_] = 0
lehmerCode p =
  let ns = dropWhile isZero $ toList p
  in go 0 (length ns) ns
  where
    go : Integer -> Nat -> List Nat -> Integer
    go res d [] = res
    go res d (n :: ns) = go (natToInteger n + natToInteger d * res) (pred d) ns

||| Compute the permutation associated with the given Lehmer code.
public export
fromLehmerCode : {n : Nat} -> (x : Integer) ->
                  {auto 0 ok : So (x >= 0 && x < factorial (natToInteger n))} -> Permutation n
fromLehmerCode {n=0} _ = []
fromLehmerCode {n=1} _ = [FZ]
fromLehmerCode x = go Z [] x
  where
    go : {n : Nat} -> (d : Nat) -> Permutation d -> Integer -> Permutation (d + n)
    go {n=0} d ns _ = rewrite plusZeroRightNeutral d in ns
    go {n=1} d ns x = rewrite plusCommutative d 1 in
      fromJust (integerToFin x _) @{believe_me $ ItIsJust {x=()}} :: ns
    go {n=S n} d ns x =
      let q = x `div` natToInteger (S d)
          r = natToFinLt (integerToNat (x `mod` natToInteger (S d))) @{believe_me Oh}
      in rewrite sym $ plusSuccRightSucc d n in go {n} (S d) (r :: ns) q


------------------------------------------------------------
-- Group operations
------------------------------------------------------------

||| The identity permutation on `n` elements.
public export
identity : {n : Nat} -> Permutation n
identity {n=0} = []
identity {n=S _} = FZ :: identity

||| Compute the inverse of the permutation.
public export
inverse : Permutation n -> Permutation n
inverse [] = []
inverse [_] = [FZ]
inverse p =
  let ns = permSeq p
  in rewrite sym $ lengthCorrect ns in invtable Z (finToNat <$> toList ns) (length ns)
  where
    invtable : Nat -> List Nat -> (n' : Nat) -> Permutation n'
    invtable _ _ Z = []
    invtable i ns (S _) =
      let ns' = takeWhile (/= i) ns
      in natToFinLt (count (> i) ns') @{believe_me Oh} :: invtable (S i) ns _

||| Compose two permutations into a new permutation.
|||
||| Note that this uses function composition order, so that the right
||| permutation is applied first.
public export
compose : Permutation n -> Permutation n -> Permutation n
compose [] [] = []
compose [_] [_] = [FZ]
compose p p' =
  let ns = permSeq p
      ns' = permSeq p'
  in fromJust (fromPermSeq $ map (`index` ns) ns') @{believe_me $ ItIsJust {x=()}}

||| Horizontally compose two permutations into a larger permutation.
|||
||| This corresponds to the action of the Cartesian product on
||| isomorphisms.
public export
horiz : Permutation m -> Permutation n -> Permutation (m + n)
horiz [] p' = p'
horiz (i :: is) p' = weakenN n i :: horiz is p'


------------------------------------------------------------
-- Applying Permutations
------------------------------------------------------------

||| Permute the elements of the `Vect` using the permutation.
public export
permuteVect : Permutation n -> Vect n a -> Vect n a
permuteVect [] [] = []
permuteVect [_] [x] = [x]
permuteVect p xs =
  let invt = permSeq $ inverse p
  in map (`index` xs) invt

||| Permute the elements of the list using the permutation.
public export
permuteList : (xs : List a) -> Permutation (length xs) -> List a
permuteList [] [] = []
permuteList [x] [_] = [x]
permuteList xs p =
  let invt = toList $ permSeq $ inverse p
  in map (index' xs) invt

||| Permute the elements of the `HVect` using the permutation.
public export
permuteHVect : {0 ts : Vect n _} -> (p : Permutation n) ->
                All q ts -> All q (permuteVect p ts)
permuteHVect [] [] = []
permuteHVect [_] [x] = [x]
permuteHVect p xs =
  replace {p = Vect.Quantifiers.All.All q} (believe_me $ Refl {x=()}) $
    fromVect $ permuteVect p $ toVect xs
  where
    toVect : forall n. {0 ts : Vect n _} -> All q ts -> Vect n (Exists q)
    toVect [] = []
    toVect (x :: xs) = Evidence _ x :: toVect xs

    fromVect : forall n. (xs : Vect n (Exists q)) -> All q (map Exists.fst xs)
    fromVect [] = []
    fromVect (Evidence _ x :: xs) = x :: fromVect xs

||| Permute the elements of the `HList` using the permutation.
public export
permuteHList : {0 ts : List _} -> (p : Permutation (length ts)) ->
                All q ts -> All q (permuteList ts p)
permuteHList [] [] = []
permuteHList [_] [x] = [x]
permuteHList p xs =
  replace {p = List.Quantifiers.All.All q} (believe_me $ Refl {x=()}) $
    fromList $ permuteList (toList xs) $ replace {p = Permutation} (believe_me $ Refl {x=()}) p
  where
    toList : forall ts. All q ts -> List (Exists q)
    toList [] = []
    toList (x :: xs) = Evidence _ x :: toList xs

    fromList : (xs : List (Exists q)) -> All q (map Exists.fst xs)
    fromList [] = []
    fromList (Evidence _ x :: xs) = x :: fromList xs


------------------------------------------------------------
-- Laws
------------------------------------------------------------

-- As with the definitions of the operations themselves, we mostly
-- cheat these for now with `believe_me`.

export
permSeqInv : (p : Permutation n) -> fromPermSeq (permSeq p) = Just p
permSeqInv p = believe_me $ Refl {x = Just p}

export
fromPermSeqInv : (seq : Vect n (Fin n)) -> IsJust (fromPermSeq seq) ->
                  permSeq (fromJust (fromPermSeq seq)) = seq
fromPermSeqInv seq prf = believe_me $ Refl {x=seq}

export
lehmerCodeBounded : (p : Permutation n) -> So (lehmerCode p >= 0 && lehmerCode p < factorial (natToInteger n))
lehmerCodeBounded _ = believe_me Oh

export
lehmerCodeInv : (p : Permutation n) -> fromLehmerCode (lehmerCode p) @{lehmerCodeBounded p} = p
lehmerCodeInv p = believe_me $ Refl {x=p}

export
lehmerCodeId : lehmerCode (identity {n}) = 0
lehmerCodeId = believe_me $ Refl {x=0}

export
fromLehmerCodeInv : (x : Integer) -> So (x >= 0 && x < factorial (natToInteger n)) => lehmerCode (fromLehmerCode {n} x) = x
fromLehmerCodeInv x = believe_me $ Refl {x}


export
compAssoc : (p,q,r : Permutation n) -> compose (compose p q) r = compose p (compose q r)
compAssoc p q r = believe_me $ Refl {x = compose p (compose q r)}

export
compIdLeft : (p : Permutation n) -> compose (identity {n}) p = p
compIdLeft p = believe_me $ Refl {x=p}

export
compIdRight : (p : Permutation n) -> compose (identity {n}) p = p
compIdRight p = believe_me $ Refl {x=p}

export
compInvLeft : (p : Permutation n) -> compose (inverse p) p = identity {n}
compInvLeft p = believe_me $ Refl {x = identity {n}}

export
compInvRight : (p : Permutation n) -> compose p (inverse p) = identity {n}
compInvRight p = believe_me $ Refl {x = identity {n}}


-- Useful for working with heterogenous equality
congCons : (0 _ : i ~=~ j) -> (0 _ : p ~=~ q) ->
            Permutation.(::) i p ~=~ Permutation.(::) j q
congCons Refl Refl = Refl

fzRefl : (0 _ : m = n) -> Fin.FZ {k=m} ~=~ Fin.FZ {k=n}
fzRefl Refl = Refl

congFS : (0 _ : i ~=~ j) -> Fin.FS i ~=~ Fin.FS j
congFS Refl = Refl


export
horizBothId : {m : _} -> horiz (identity {n=m}) (identity {n}) = identity {n = m + n}
horizBothId {m=0} = Refl
horizBothId {m=S _} = cong (FZ ::) horizBothId

export
horizComp : (p,p' : Permutation m) -> (q,q' : Permutation n) ->
            horiz (compose p p') (compose q q') = compose (horiz p q) (horiz p' q')
horizComp p p' q q' = believe_me $ Refl {x = compose (horiz p q) (horiz p' q')}

export
horizAssoc : (p : Permutation m) -> (q : Permutation n) -> (r : Permutation o) ->
              horiz (horiz p q) r ~=~ horiz p (horiz q r)
horizAssoc [] q r = Refl
horizAssoc (i :: p) q r = congCons (weakenPlus i) (horizAssoc p q r)
  where
    weakenPlus : (x : Fin _) -> weakenN o (weakenN n x) ~=~ weakenN (n + o) x
    weakenPlus FZ = fzRefl (sym $ plusAssociative _ _ _)
    weakenPlus (FS x) = congFS (weakenPlus x)

export
horizUnitl : (p : Permutation n) -> horiz [] p = p
horizUnitl _ = Refl

export
horizUnitr : (p : Permutation n) -> horiz p [] ~=~ p
horizUnitr [] = Refl
horizUnitr (i :: p) = congCons (weakenZ i) (horizUnitr p)
  where
    weakenZ : (x : Fin _) -> weakenN 0 x ~=~ x
    weakenZ FZ = fzRefl (plusZeroRightNeutral _)
    weakenZ (FS x) = congFS (weakenZ x)


export
permuteVectId : (xs : Vect n a) -> permuteVect Permutation.identity xs = xs
permuteVectId xs = believe_me $ Refl {x=xs}

export
permuteVectComp : (p,q : Permutation n) -> (xs : Vect n a) ->
                  permuteVect (compose p q) xs = permuteVect p (permuteVect q xs)
permuteVectComp p q xs = believe_me $ Refl {x = permuteVect (compose p q) xs}

export
permuteVectHoriz : (p : Permutation m) -> (xs : Vect m a) -> (q : Permutation n) -> (ys : Vect n a) ->
                    permuteVect p xs ++ permuteVect q ys = permuteVect (horiz p q) (xs ++ ys)
permuteVectHoriz p xs q ys = believe_me $ Refl {x = permuteVect (horiz p q) (xs ++ ys)}

export
permuteListId : (xs : List a) -> permuteList xs Permutation.identity = xs
permuteListId xs = believe_me $ Refl {x=xs}

export
permuteListLength : (xs : List a) -> (p : Permutation _) -> length (permuteList xs p) = length xs
permuteListLength xs p = believe_me $ Refl {x = length xs}

export
permuteListComp : (xs : List a) -> (p,q : Permutation _) ->
                  permuteList xs (compose p q)
                  = permuteList (permuteList xs q) (rewrite permuteListLength xs q in p)
permuteListComp xs p q = believe_me $ Refl {x = permuteList xs (compose p q)}
