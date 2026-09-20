module Syntax.StringDiagram.Arrow

import public Control.Monad.State
import public Control.Applicative.Const
import public Control.Arrow
import public Control.Category.Core
import public Language.Reflection
import public Data.Wrap0

%default total
%language ElabReflection

export infix 0 -<
export prefix 0 =<


record ArrowVar where
  constructor MkAVar
  name : String
  type : TTImp


zipFilter : List a -> List Bool -> List a
zipFilter = catMaybes .: zipWith (\x,b => guard b $> x)


bindVars : TTImp -> List String
bindVars = (nub . runConst .) $ mapATTImp' $ \case
  IBindVar _ (UN $ Basic var) => const $ MkConst [var]
  IAs _ _ _ (UN $ Basic var) _ => \(MkConst vs) => MkConst (var :: vs)
  _ => id

isBoundVar : TTImp -> String -> Bool
isBoundVar t var =
  let _ = Lazy.Monoid.Any
  in runConst {a=Lazy Bool} $ flip mapATTImp' t $ \case
    IBindVar _ (UN $ Basic var') => const $ MkConst $ delay (var == var')
    IAs _ _ _ (UN $ Basic var') _ => \(MkConst b) => MkConst (var == var' || b)
    _ => id

usedInExpr : TTImp -> String -> Bool
usedInExpr t var =
  let _ = Lazy.Monoid.Any
  in runConst {a=Lazy Bool} $ flip mapATTImp' t $ \case
    -- If a hole is found, always include every possible variable
    IHole _ _ => const $ MkConst $ delay True
    IVar _ (UN $ Basic var') => const $ MkConst $ delay (var == var')
    _ => id

usedInDiagram : TTImp -> String -> Bool
usedInDiagram (ILam _ _ _ (Just $ UN $ Basic v) _ rest) var =
  v /= var && usedInDiagram rest var
usedInDiagram (ILam _ _ _ _ _ rest) var = usedInDiagram rest var
usedInDiagram (ILet _ _ _ (UN $ Basic v) _ exp rest) var =
  usedInExpr exp var || (v /= var && usedInDiagram rest var)
usedInDiagram (ILet _ _ _ _ _ exp rest) var =
  usedInExpr exp var || usedInDiagram rest var
usedInDiagram (ICase _ _ exp _ clauses) var =
  usedInExpr exp var || any (\case
    PatClause _ lhs rhs =>
      not (isBoundVar lhs var) &&
        usedInDiagram (assert_smaller clauses rhs) var
    _ => False
    ) clauses
usedInDiagram `((~(mor) -< ~(inp)) >>= ~(rest)) var =
  usedInExpr inp var || usedInDiagram rest var
usedInDiagram `((~(mor) -< ~(inp)) >> ~(rest)) var =
  usedInExpr inp var || usedInDiagram rest var
usedInDiagram `(=< ~(out)) var = usedInExpr out var
usedInDiagram _ _ = False


export
arrowImpl : TTImp -> Elab TTImp
arrowImpl t = do
  ts <- arrowImplLam [<] [] t
  pure $ composeImp $ optimize ts
  where
    optimize : SnocList TTImp -> SnocList TTImp
    optimize [<] = [<]
    optimize [<t] = [<t]
    optimize (ts :< `(Control.Arrow.arrow {a = ~a, b = ~_} ~f) :< `(Control.Arrow.arrow {a = ~b, b = ~c} ~g)) =
      assert_total $ optimize (ts :< `(Control.Arrow.arrow {a = ~a, b = ~c} (Prelude.(.) {a = ~a, b = ~b, c = ~c} ~g ~f)))
    optimize (ts :< t :< t') = optimize (ts :< t) :< t'

    composeImp : SnocList TTImp -> TTImp
    composeImp [<] = `(Control.Category.Core.id)
    composeImp [<t] = t
    composeImp (ts :< t) =
      `(Control.Category.Core.(.)
        ~t ~(composeImp ts))

    pairTy : List ArrowVar -> TTImp
    pairTy [] = `(Builtin.Unit)
    pairTy [MkAVar _ ty] = ty
    pairTy (MkAVar _ ty :: vars) = `(Builtin.Pair ~ty ~(pairTy vars))

    pair : List String -> TTImp
    pair [] = `(Builtin.MkUnit)
    pair [n] = IVar EmptyFC $ UN $ Basic n
    pair (n :: ns) = `(Builtin.MkPair ~(IVar EmptyFC $ UN $ Basic n) ~(pair ns))

    stringBind : List (ArrowVar, Bool) -> TTImp
    stringBind [] = `(Builtin.MkUnit)
    stringBind [(v,b)] = if b then IBindVar EmptyFC (UN $ Basic v.name) else Implicit EmptyFC True
    stringBind ((v,b) :: strings) = `(Builtin.MkPair ~(if b then IBindVar EmptyFC (UN $ Basic v.name) else Implicit EmptyFC True) ~(stringBind strings))

    stringLam : List (ArrowVar, Bool) -> TTImp -> TTImp
    stringLam [] t = `(\_ => ~t)
    stringLam [(_,False)] t = `(\_ => ~t)
    stringLam [(v,True)] t = ILam EmptyFC MW ExplicitArg (Just $ UN $ Basic v.name) (Implicit EmptyFC False) t
    stringLam ns t = `(\ ~(stringBind ns) => ~t)

    mkEither : (i,n : Nat) -> TTImp -> TTImp
    mkEither Z (S (S _)) t = `(Prelude.Left ~t)
    mkEither (S n) (S n') t = `(Prelude.Right ~(mkEither n n' t))
    mkEither _ _ t = t

    arrowImplLam : SnocList TTImp -> List ArrowVar -> TTImp -> Elab (SnocList TTImp)
    arrowImpl' : SnocList TTImp -> List ArrowVar -> TTImp -> Elab (SnocList TTImp)

    arrowImplLam ts [] (ILam _ MW ExplicitArg Nothing _ rest) =
      arrowImpl' (ts :< `(Control.Arrow.arrow {a=_,b=_} (\_ => Builtin.MkUnit))) [] rest
    arrowImplLam ts [] (ILam _ MW ExplicitArg (Just $ UN $ Basic var) ty rest) =
      arrowImpl' ts [MkAVar var ty] rest
    arrowImplLam ts strings (ILam _ MW ExplicitArg Nothing _ rest) =
      arrowImpl' (ts :< `(Control.Arrow.arrow {a=_,b=_} Builtin.snd)) strings rest
    arrowImplLam ts strings (ILam _ MW ExplicitArg (Just $ UN $ Basic var) ty rest) =
      if any (\v => v.name == var) strings
      then do
        let used = map (\v => v.name /= var) strings
        let strings' = MkAVar var ty :: zipFilter strings used
        arrowImpl'
          (ts :< `(Control.Arrow.arrow {a = ~(pairTy $ MkAVar var ty :: strings), b = ~(pairTy strings')}
                    (\(Builtin.MkPair ~(IBindVar EmptyFC $ UN $ Basic var) ~(stringBind $ zip strings used)) =>
                      ~(pair $ map name strings'))))
          strings' rest
      else arrowImpl' ts (MkAVar var ty :: strings) rest
    arrowImplLam ts strings (ILam _ MW ExplicitArg (Just $ MN var _) ty rest) = do
      arrowImpl' ts (MkAVar var ty :: strings) rest
    arrowImplLam ts strings (ILam fc {}) = failAt fc "Invalid lambda"
    arrowImplLam ts strings t = failAt (getFC t) "Expected lambda expression or binding pattern"

    arrowImpl' ts [MkAVar _ ty] (ICase _ _ (IVar _ var@(MN {})) _ [PatClause _ lhs rhs]) = do
      let names = bindVars lhs
      let vars = map (`MkAVar` `(_)) names
      arrowImpl'
        (ts :< `(Control.Arrow.arrow {a=_,b = ~(pairTy vars)} (\ ~lhs : ~ty => ~(pair names))))
        vars rhs
    arrowImpl' ts (v :: strings) (ICase _ _ (IVar _ var@(MN {})) _ [PatClause _ lhs rhs]) = do
      let names = bindVars lhs
      let vars = map (`MkAVar` `(_)) names
      rest <- genSym "vars"
      arrowImpl'
        (ts :< `(Control.Arrow.arrow {a = ~(pairTy $ v :: strings), b = ~(pairTy $ vars ++ strings)}
          (\(Builtin.MkPair ~lhs ~(IBindVar EmptyFC rest)) =>
            Builtin.MkPair ~(pair names) ~(IVar EmptyFC rest))))
        (vars ++ strings) rhs
    arrowImpl' ts strings (ICase _ _ exp ty clauses) = do
      let tot = length clauses
      (clauses', conts) <- map unzip $ evalStateT Z $ for clauses $ \case
        PatClause _ lhs rhs => do
          let names = bindVars lhs
          let vars = map (`MkAVar` `(_)) names
          let usedExp = map (usedInExpr exp . name) strings
          let usedLater = map (\v => not (elem v.name names) && usedInDiagram rhs v.name) strings
          let strings' = vars ++ zipFilter strings usedLater
          t <- lift $ assert_total $ arrowImpl' [<] strings' rhs
          i <- get
          modify S
          pure (PatClause EmptyFC lhs $ mkEither i tot $ pair $ map name strings', Just $ composeImp $ optimize t)
        ImpossibleClause _ lhs => pure (ImpossibleClause EmptyFC lhs, Nothing)
        WithClause fc {} => failAt fc "Unrecognized case pattern"
      let conts' = catMaybes conts
      case conts' of
        [] =>
          pure (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase EmptyFC [] exp ty clauses'))))
        _ :: _ =>
          pure (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase EmptyFC [] exp ty clauses')))
                    :< foldr1 (\t,t' => `(Control.Arrow.(\|/) ~t ~t')) conts')
    arrowImpl' ts strings `(~(ICase _ _ exp ty clauses) >> ~(rest)) = do
      let tot = length clauses
      (clauses', conts) <- map unzip $ evalStateT Z $ for clauses $ \case
        PatClause _ lhs rhs => do
          let names = bindVars lhs
          let vars = map (`MkAVar` `(_)) names
          let usedExp = map (usedInExpr exp . name) strings
          let usedLater = map (\v => not (elem v.name names) && usedInDiagram rhs v.name) strings
          let strings' = vars ++ zipFilter strings usedLater
          t <- lift $ assert_total $ arrowImpl' [<] strings' rhs
          i <- get
          modify S
          pure (PatClause EmptyFC lhs $ mkEither i tot $ pair $ map name strings', Just $ composeImp $ optimize t)
        ImpossibleClause _ lhs => pure (ImpossibleClause EmptyFC lhs, Nothing)
        WithClause fc {} => failAt fc "Unrecognized case pattern"
      let conts' = catMaybes conts
      case conts' of
        [] =>
          arrowImpl' (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase EmptyFC [] exp ty clauses'))))
            strings rest
        _ :: _ =>
          arrowImpl' (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = _}
                        ~(stringLam (map (,True) strings)
                        `(Builtin.MkPair ~(ICase EmptyFC [] exp ty clauses') ~(pair $ map name strings))))
                      :< `(Control.Arrow.first ~(foldr1 (\t,t' => `(Control.Arrow.(\|/) ~t ~t')) conts'))
                      :< `(Control.Arrow.arrow {a=_,b=_} Builtin.snd))
            strings rest
    arrowImpl' ts strings `(~(ICase _ _ exp ty clauses) >>= ~(rest)) = do
      let tot = length clauses
      (clauses', conts) <- map unzip $ evalStateT Z $ for clauses $ \case
        PatClause _ lhs rhs => do
          let names = bindVars lhs
          let vars = map (`MkAVar` `(_)) names
          let usedExp = map (usedInExpr exp . name) strings
          let usedLater = map (\v => not (elem v.name names) && usedInDiagram rhs v.name) strings
          let strings' = vars ++ zipFilter strings usedLater
          t <- lift $ assert_total $ arrowImpl' [<] strings' rhs
          i <- get
          modify S
          pure (PatClause EmptyFC lhs $ mkEither i tot $ pair $ map name strings', Just $ composeImp $ optimize t)
        ImpossibleClause _ lhs => pure (ImpossibleClause EmptyFC lhs, Nothing)
        WithClause fc {} => failAt fc "Unrecognized case pattern"
      let conts' = catMaybes conts
      case conts' of
        [] =>
          arrowImplLam (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase EmptyFC [] exp ty clauses'))))
            strings rest
        _ :: _ =>
          arrowImplLam (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = _}
                        ~(stringLam (map (,True) strings)
                        `(Builtin.MkPair ~(ICase EmptyFC [] exp ty clauses') ~(pair $ map name strings))))
                      :< `(Control.Arrow.first ~(foldr1 (\t,t' => `(Control.Arrow.(\|/) ~t ~t')) conts')))
            strings rest
    arrowImpl' ts strings (ILet _ _ MW (UN $ Basic var) ty exp rest) = do
      (usedExp,usedLater,strings') <- do
        let usedExp = map (usedInExpr exp . name) strings
        let usedLater = map (\v => v.name /= var && usedInDiagram rest v.name) strings
        let strings' = MkAVar var ty :: zipFilter strings usedLater
        pure (usedExp,usedLater,strings')
      arrowImpl'
        (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = ~(pairTy strings')}
          ~(stringLam (zip strings $ zipWith (\x,y => x || y) usedExp usedLater)
            (ILet EmptyFC EmptyFC MW (UN $ Basic var) ty exp (pair $ map name strings')))))
        strings' rest
    arrowImpl' ts strings (ILet fc {}) = failAt fc "Let binding must be unrestricted"
    arrowImpl' ts strings `((~(mor) -< ~(inp)) >>= ~(rest)) =
      case strings of
        [] => arrowImplLam (ts :< `(Control.Arrow.arrow {a=_,b=_} (\_ => ~inp)) :< mor) [] rest
        _ :: _ => do
          (usedInp,usedLater,strings') <- do
            let usedInp = map (usedInExpr inp . name) strings
            let usedLater = map (usedInDiagram rest . name) strings
            let strings' = zipFilter strings usedLater
            pure (usedInp,usedLater,strings')
          case strings' of
            [] =>
              arrowImplLam
                (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings),b=_}
                          ~(stringLam (zip strings usedInp) inp))
                    :< mor)
                strings' rest
            _ :: _ =>
              arrowImplLam
                (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = Builtin.Pair _ ~(pairTy strings')}
                  ~(stringLam (zip strings $ zipWith (\x,y => x || y) usedInp usedLater)
                    `(Builtin.MkPair ~inp ~(pair $ map name strings'))))
                    :< `(Control.Arrow.first ~mor))
                strings' rest
    arrowImpl' ts strings `((~(mor) -< ~(inp)) >> ~(rest)) =
      case strings of
        [] => arrowImpl' (ts :<
                `(Control.Arrow.arrow {a=_,b=_} (\_ => ~inp)) :< mor :< `(Control.Arrow.arrow {a=_,b=_} Builtin.snd)) [] rest
        _ :: _ => do
          (usedInp,usedLater,strings') <- do
            let usedInp = map (usedInExpr inp . name) strings
            let usedLater = map (usedInDiagram rest . name) strings
            let strings' = zipFilter strings usedLater
            pure (usedInp,usedLater,strings')
          case strings' of
            [] =>
              arrowImpl'
                (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = _}
                          ~(stringLam (zip strings usedInp) inp))
                    :< mor :< `(Control.Arrow.arrow {a=_,b=_} (\_ => ())))
                strings' rest
            _ :: _ =>
              arrowImpl'
                (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings), b = Builtin.Pair _ ~(pairTy strings')}
                        ~(stringLam (zip strings $ zipWith (\x,y => x || y) usedInp usedLater)
                          `(Builtin.MkPair ~inp ~(pair $ map name strings'))))
                    :< `(Control.Arrow.first ~mor) :< `(Control.Arrow.arrow {a=_,b=_} Builtin.snd))
                strings' rest
    arrowImpl' ts strings `(=< ~(out)) =
      pure (ts :< `(Control.Arrow.arrow {a = ~(pairTy strings),b=_}
        ~(stringLam (map (,True) strings) out)))

    arrowImpl' ts strings (ILam fc {}) = failAt (getFC t) "Lambda not allowed here"
    arrowImpl' ts strings t = failAt (getFC t) "Could not parse expression"

||| Enter arrow notation.
|||
||| This elaboration script must be specifically invoked with
||| `%runElab`. The category is inferred from the return type.
export
arrowDo : {0 arr : Hom Type0} -> Arrow arr => TTImp -> Elab (arr (W0 a) (W0 b))
arrowDo t = check !(arrowImpl t)
