module Syntax.StringDiagram.Util

import Language.Reflection

%default total
%language ElabReflection

export infix 0 -<
export prefix 0 =<

export
parseList : TTImp -> Elab (List String)
parseList `(~(IVar _ $ UN $ Basic var) :: ~t) = map (var ::) $ parseList t
parseList t@`(~(IVar _ $ UN Underscore) :: ~_) = failAt (getFC t) "Underscores are not allowed here"
parseList t@`(~(Implicit _ True) :: ~_) = failAt (getFC t) "Underscores are not allowed here"
parseList t@`(~_ :: ~_) = failAt (getFC t) "Could not read list"
parseList `(Nil) = pure []
parseList (IVar _ $ UN $ Basic var) = pure [var]
parseList t@(IVar _ $ UN Underscore) = failAt (getFC t) "Underscores are not allowed here"
parseList t@(Implicit _ True) = failAt (getFC t) "Underscores are not allowed here"
parseList t = failAt (getFC t) "Not in proper list form"

export
parseListPat : TTImp -> Elab (List (Maybe String))
parseListPat `(~(IBindVar _ $ UN $ Basic var) :: ~t) = map (Just var ::) $ parseListPat t
parseListPat `(~(IBindVar _ $ UN Underscore) :: ~t) = map (Nothing ::) $ parseListPat t
parseListPat `(~(Implicit _ True) :: ~t) = map (Nothing ::) $ parseListPat t
parseListPat `(Nil) = pure []
parseListPat (IBindVar _ $ UN $ Basic var) = pure [Just var]
parseListPat (IBindVar _ $ UN Underscore) = pure [Nothing]
parseListPat (Implicit _ True) = pure [Nothing]
parseListPat t = failAt (getFC t) "Not in proper list form"

export
parseListLam : TTImp -> Elab (List (Maybe String), TTImp)
parseListLam
  t@(ILam _ MW ExplicitArg (Just var) _
    (ICase _ [] (IVar _ var') _ [PatClause _ ls exp])) =
      if var == var'
      then (,exp) <$> parseListPat ls
      else failAt (getFC t) "Invalid string pattern"
parseListLam (ILam _ MW ExplicitArg (Just $ UN $ Basic var) _ exp) = pure ([Just var], exp)
parseListLam (ILam _ MW ExplicitArg (Just $ UN Underscore) _ exp) = pure ([Nothing], exp)
parseListLam (ILam _ MW ExplicitArg Nothing _ exp) = pure ([Nothing], exp)
parseListLam t@(ILam {}) = failAt (getFC t) "Invalid string pattern"
parseListLam t = failAt (getFC t) "Expected string pattern"


public export
record CatString where
  constructor MkCatString
  name : String
  disamb : Nat

export
Eq CatString where
  MkCatString n d == MkCatString n' d' = n == n' && d == d'

public export
record SDiagramStep where
  constructor MkSDStep
  inputs : List CatString
  mor : TTImp
  outputs : List (Maybe CatString)

public export
record SDiagram where
  constructor MkSDiagram
  inputs : List (Maybe CatString)
  steps : List SDiagramStep
  outputs : List CatString


export
parseDiagram : TTImp -> Elab SDiagram
parseDiagram t = do
  (inp, rest) <- mapFst (map $ map $ flip MkCatString Z) <$> parseListLam t
  let Nothing = findDup (catMaybes inp)
    | Just n => failAt (getFC t) "Duplicate string name '\{n.name}'"
  (steps, out) <- parseDiagram' (catMaybes inp) rest
  pure $ MkSDiagram inp steps out
  where
    findDup : Eq a => List a -> Maybe a
    findDup [] = Nothing
    findDup (s :: ss) =
      if elem s ss
      then Just s
      else findDup ss

    resolveString : FC -> List CatString -> String -> Elab CatString
    resolveString fc names n = case find ((==n) . name) names of
      Just (MkCatString _ d) => pure $ MkCatString n d
      Nothing => failAt fc "Unknown string name \{n}"

    resolveStringPat : List CatString -> String -> CatString
    resolveStringPat names n = case find ((==n) . name) names of
      Just (MkCatString _ d) => MkCatString n (S d)
      Nothing => MkCatString n Z

    parseDiagram' : List CatString -> TTImp -> Elab (List SDiagramStep, List CatString)
    parseDiagram' names t@`((~(mor) -< ~(inp)) >>= ~(pat)) = do
      inp' <- parseList inp >>= traverse (resolveString (getFC inp) names)
      (o, rest) <- parseListLam pat
      let o' = map (resolveStringPat names) <$> o
      let onames = catMaybes o'
      let Nothing = findDup onames
        | Just n => failAt (getFC pat) "Duplicate string name '\{n.name}'"
      let names' = filter (\n => not $ any (\n' => n.name == n'.name) onames) names
      (steps, out) <- parseDiagram' (onames ++ names') (assert_smaller t rest)
      pure $ (MkSDStep inp' mor o' :: steps, out)
    parseDiagram' names t@`((~(mor) -< ~(inp)) >> ~(rest)) = do
      inp' <- parseList inp >>= traverse (resolveString (getFC inp) names)
      (steps, out) <- parseDiagram' names (assert_smaller t rest)
      pure $ (MkSDStep inp' mor [] :: steps, out)
    parseDiagram' names `(=< ~(out)) = do
      out' <- parseList out >>= traverse (resolveString (getFC out) names)
      pure ([], out')
    parseDiagram' _ t = failAt (getFC t) "Could not parse expression as string diagram"
