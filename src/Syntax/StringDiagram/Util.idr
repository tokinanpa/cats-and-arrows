module Syntax.StringDiagram.Util

import Language.Reflection

%default total
%language ElabReflection

export infix 0 -<
export prefix 0 =<

parseList : TTImp -> Elab (List String)
parseList = go [<]
  where
    go : SnocList String -> TTImp -> Elab (List String)
    go res `(~(IVar _ $ UN $ Basic var) :: ~t) = go (res :< var) t
    go res t@`(~(IVar _ $ UN Underscore) :: ~_) = failAt (getFC t) "Underscores are not allowed here"
    go res t@`(~(Implicit _ True) :: ~_) = failAt (getFC t) "Underscores are not allowed here"
    go res t@`(~_ :: ~_) = failAt (getFC t) "Could not read list"
    go res `(Nil) = pure (res <>> [])
    go res t = failAt (getFC t) "Not in proper list form"

parseSingle : TTImp -> Elab (List String)
parseSingle (IVar _ $ UN $ Basic var) = pure [var]
parseSingle t@(IVar _ $ UN Underscore) = failAt (getFC t) "Underscores are not allowed here"
parseSingle t@(Implicit _ True) = failAt (getFC t) "Underscores are not allowed here"
parseSingle t = failAt (getFC t) "Not in proper list form"

export
parseListOrSing : TTImp -> Elab (List String)
parseListOrSing t = parseList t <|> parseSingle t

parseListPat : TTImp -> Elab (List (Maybe String))
parseListPat = go [<]
  where
    go : SnocList (Maybe String) -> TTImp -> Elab (List (Maybe String))
    go res `(~(IBindVar _ $ UN $ Basic var) :: ~t) = go (res :< Just var) t
    go res `(~(IBindVar _ $ UN Underscore) :: ~t) = go (res :< Nothing) t
    go res `(~(Implicit _ True) :: ~t) = go (res :< Nothing) t
    go res t@`(~_ :: ~_) = failAt (getFC t) "Could not read list"
    go res `(Nil) = pure (res <>> [])
    go res t = failAt (getFC t) "Not in proper list form"

parseSinglePat : TTImp -> Elab (List (Maybe String))
parseSinglePat (IBindVar _ $ UN $ Basic var) = pure [Just var]
parseSinglePat t@(IBindVar _ $ UN Underscore) = pure [Nothing]
parseSinglePat t@(Implicit _ True) = pure [Nothing]
parseSinglePat t = failAt (getFC t) "Not in proper list form"

export
parseListOrSingPat : TTImp -> Elab (List (Maybe String))
parseListOrSingPat t = parseListPat t <|> parseSinglePat t

export
parseLam : TTImp -> Elab (List (Maybe String), TTImp)
parseLam
  t@(ILam _ MW ExplicitArg (Just _) _
    (ICase _ [] (IVar _ _) _ [PatClause _ ls exp])) = (,exp) <$> parseListOrSingPat ls
parseLam (ILam _ MW ExplicitArg (Just $ UN $ Basic var) _ exp) = pure ([Just var], exp)
parseLam (ILam _ MW ExplicitArg (Just $ UN Underscore) _ exp) = pure ([Nothing], exp)
parseLam (ILam _ MW ExplicitArg Nothing _ exp) = pure ([Nothing], exp)
parseLam t@(ILam {}) = failAt (getFC t) "Invalid string pattern"
parseLam t = failAt (getFC t) "Expected string pattern"


public export
record CatString where
  constructor MkCatString
  name : String
  disamb : Nat

export
Eq CatString where
  MkCatString n d == MkCatString n' d' = n == n' && d == d'

export
Show CatString where
  showPrec p (MkCatString n d) =
    showCon p "MkCatString" $ showArg n ++ showArg d

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
  (inp, rest) <- mapFst (map $ map $ flip MkCatString Z) <$> parseLam t
  let Nothing = findDup (catMaybes inp)
    | Just n => failAt (getFC t) "Duplicate string name '\{n.name}'"
  (steps, out) <- parseDiagram' [<] (catMaybes inp) rest
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

    parseDiagram' : SnocList SDiagramStep -> List CatString -> TTImp -> Elab (List SDiagramStep, List CatString)
    parseDiagram' steps names t@`((~(mor) -< ~(inp)) >>= ~(pat)) = do
      (inp',o',names',rest) <- do
        inp' <- parseListOrSing inp >>= traverse (resolveString (getFC inp) names)
        (o, rest) <- parseLam pat
        let o' = map (resolveStringPat names) <$> o
        let onames = catMaybes o'
        let Nothing = findDup onames
          | Just n => failAt (getFC pat) "Duplicate string name '\{n.name}'"
        let names' = filter (\n => not $ any (\n' => n.name == n'.name) onames) names
        pure (inp',o',onames ++ names',rest)
      parseDiagram' (steps :< MkSDStep inp' mor o') names' (assert_smaller t rest)
    parseDiagram' steps names t@`((~(mor) -< ~(inp)) >> ~(rest)) = do
      inp' <- parseListOrSing inp >>= traverse (resolveString (getFC inp) names)
      parseDiagram' (steps :< MkSDStep inp' mor []) names (assert_smaller t rest)
    parseDiagram' steps names t@`(~(mor) >>= ~(pat)) = do
      (o',names',rest) <- do
        (o, rest) <- parseLam pat
        let o' = map (resolveStringPat names) <$> o
        let onames = catMaybes o'
        let Nothing = findDup onames
          | Just n => failAt (getFC pat) "Duplicate string name '\{n.name}'"
        let names' = filter (\n => not $ any (\n' => n.name == n'.name) onames) names
        pure (o',onames ++ names',rest)
      parseDiagram' (steps :< MkSDStep [] mor o') names' (assert_smaller t rest)
    parseDiagram' steps names t@`(~(mor) >> ~(rest)) =
      parseDiagram' (steps :< MkSDStep [] mor []) names (assert_smaller t rest)
    parseDiagram' steps names `(=< ~(out)) = do
      out' <- parseListOrSing out >>= traverse (resolveString (getFC out) names)
      pure (steps <>> [], out')
    parseDiagram' _ _ t = failAt (getFC t) "Could not parse expression as string diagram"
