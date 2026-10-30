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
arrowImpl : (impl : Maybe (TTImp, Bool)) -> TTImp -> Elab TTImp
arrowImpl impl t = do
  cat <- genSym "cat"
  arr <- genSym "arr"
  choice <- genSym "choice"
  let catImpl : TTImp =
      case impl of
        Nothing => `(%search)
        Just _ => IVar EmptyFC cat
  let arrImpl : TTImp =
      case impl of
        Nothing => `(%search)
        Just _ => IVar EmptyFC arr
  let choiceImpl : TTImp =
      case impl of
        Just (_, True) => IVar EmptyFC choice
        _ => `(%search)
  ts <- arrowImplLam catImpl arrImpl choiceImpl [<] [] t
  let out = composeImp catImpl $ optimize ts
  pure $ case impl of
    Nothing => out
    Just (im, False) => ILet EmptyFC EmptyFC MW arr (Implicit EmptyFC True) im
      `(let (Builtin.MkPair (Control.Category.Promonad.MkPromonad0 @{~(IBindVar EmptyFC cat)} {}) _) = ~(IVar EmptyFC arr)
        in ~out)
    Just (im, True) => ILet EmptyFC EmptyFC MW choice (Implicit EmptyFC True) im
      `(let (Builtin.MkPair ~(IBindVar EmptyFC arr) _) = ~(IVar EmptyFC choice)
            (Builtin.MkPair (Control.Category.Promonad.MkPromonad0 @{~(IBindVar EmptyFC cat)} {}) _) = ~(IVar EmptyFC arr)
        in ~out)
  where
    optimize : SnocList TTImp -> SnocList TTImp
    optimize [<] = [<]
    optimize [<t] = [<t]
    optimize (ts :< `(Control.Arrow.arrow @{~ar} {a = ~a, b = ~_} ~f) :< `(Control.Arrow.arrow @{~_} {a = ~b, b = ~c} ~g)) =
      assert_total $ optimize (ts :< `(Control.Arrow.arrow @{~ar} {a = ~a, b = ~c} (Prelude.(.) {a = ~a, b = ~b, c = ~c} ~g ~f)))
    optimize (ts :< t :< t') = optimize (ts :< t) :< t'

    composeImp : (cat : TTImp) -> SnocList TTImp -> TTImp
    composeImp cat [<] = `(Control.Category.Core.id @{~cat})
    composeImp _ [<t] = t
    composeImp cat (ts :< t) =
      `(Control.Category.Core.(.) @{~cat} {a = _, b = _}
        ~t ~(composeImp cat ts))

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

    stringLamMN : Name -> List (ArrowVar, Bool) -> TTImp -> TTImp
    stringLamMN mn [] t = ILam EmptyFC MW ExplicitArg (Just mn) (Implicit EmptyFC False) t
    stringLamMN mn ns t = `(\ (Builtins.MkPair ~(IBindVar EmptyFC mn) ~(stringBind ns)) => ~t)

    mkEither : (i,n : Nat) -> TTImp -> TTImp
    mkEither Z (S (S _)) t = `(Prelude.Left ~t)
    mkEither (S n) (S n') t = `(Prelude.Right ~(mkEither n n' t))
    mkEither _ _ t = t

    arrowImplLam : (ct,ar,ch : TTImp) -> SnocList TTImp -> List ArrowVar -> TTImp -> Elab (SnocList TTImp)
    arrowImpl' : (ct,ar,ch : TTImp) -> SnocList TTImp -> List ArrowVar -> TTImp -> Elab (SnocList TTImp)

    arrowImplLam ct ar ch ts [] (ILam _ MW ExplicitArg Nothing _ rest) =
      arrowImpl' ct ar ch (ts :< `(Control.Arrow.arrow @{~ar} {a=_,b=_} (\_ => Builtin.MkUnit))) [] rest
    arrowImplLam ct ar ch ts [] (ILam _ MW ExplicitArg (Just $ UN $ Basic var) ty rest) =
      arrowImpl' ct ar ch ts [MkAVar var ty] rest
    arrowImplLam ct ar ch ts strings (ILam _ MW ExplicitArg Nothing _ rest) =
      arrowImpl' ct ar ch (ts :< `(Control.Arrow.arrow @{~ar} {a=_,b=_} Builtin.snd)) strings rest
    arrowImplLam ct ar ch ts strings (ILam _ MW ExplicitArg (Just $ UN $ Basic var) ty rest) =
      if any (\v => v.name == var) strings
      then do
        let used = map (\v => v.name /= var) strings
        let strings' = MkAVar var ty :: zipFilter strings used
        arrowImpl' ct ar ch
          (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy $ MkAVar var ty :: strings), b = ~(pairTy strings')}
                    (\(Builtin.MkPair ~(IBindVar EmptyFC $ UN $ Basic var) ~(stringBind $ zip strings used)) =>
                      ~(pair $ map name strings'))))
          strings' rest
      else arrowImpl' ct ar ch ts (MkAVar var ty :: strings) rest
    arrowImplLam ct ar ch ts strings (ILam _ MW ExplicitArg (Just $ MN var _) ty rest) = do
      arrowImpl' ct ar ch ts (MkAVar var ty :: strings) rest
    arrowImplLam _ _ _ _ _ (ILam fc {}) = failAt fc "Invalid lambda"
    arrowImplLam _ _ _ _ _ t = failAt (getFC t) "Expected lambda expression or binding pattern"

    arrowImpl' ct ar ch ts (MkAVar v ty :: strings) (ICase fc _ (IVar _ var@(MN {})) _ clauses) = do
      let tot = length clauses
      (clauses', conts) <- map unzip $ evalStateT Z $ for clauses $ \case
        PatClause fc' lhs rhs => do
          let names = bindVars lhs
          let vars = map (`MkAVar` `(_)) names
          let usedLater = map (\v => not (elem v.name names) && usedInDiagram rhs v.name) strings
          let strings' = vars ++ zipFilter strings usedLater
          t <- lift $ assert_total $ arrowImpl' ct ar ch [<] strings' rhs
          i <- get
          modify S
          pure (PatClause fc' lhs $ mkEither i tot $ pair $ map name strings', Just $ composeImp ct $ optimize t)
        ImpossibleClause fc' lhs => pure (ImpossibleClause fc' lhs, Nothing)
        WithClause fc' {} => failAt fc' "Unrecognized case pattern"
      let conts' = catMaybes conts
      case conts' of
        [] =>
          pure (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy $ MkAVar v ty :: strings), b = _}
                      ~(stringLamMN var (map (,False) strings)
                        (ICase fc [] (IVar EmptyFC var) ty clauses'))))
        _ :: _ =>
          pure (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy $ MkAVar v ty :: strings), b = _}
                      ~(stringLamMN var (map (,False) strings)
                        (ICase fc [] (IVar EmptyFC var) ty clauses')))
                    :< foldr1 (\t,t' => `(Control.Arrow.(\|/) @{~ch} ~t ~t')) conts')
    arrowImpl' ct ar ch ts strings (ICase fc _ exp ty clauses) = do
      let tot = length clauses
      (clauses', conts) <- map unzip $ evalStateT Z $ for clauses $ \case
        PatClause fc' lhs rhs => do
          let names = bindVars lhs
          let vars = map (`MkAVar` `(_)) names
          let usedLater = map (\v => not (elem v.name names) && usedInDiagram rhs v.name) strings
          let strings' = vars ++ zipFilter strings usedLater
          t <- lift $ assert_total $ arrowImpl' ct ar ch [<] strings' rhs
          i <- get
          modify S
          pure (PatClause fc' lhs $ mkEither i tot $ pair $ map name strings', Just $ composeImp ct $ optimize t)
        ImpossibleClause fc' lhs => pure (ImpossibleClause fc' lhs, Nothing)
        WithClause fc' {} => failAt fc' "Unrecognized case pattern"
      let conts' = catMaybes conts
      case conts' of
        [] =>
          pure (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase fc [] exp ty clauses'))))
        _ :: _ =>
          pure (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase fc [] exp ty clauses')))
                    :< foldr1 (\t,t' => `(Control.Arrow.(\|/) @{~ch} ~t ~t')) conts')
    arrowImpl' ct ar ch ts strings `(~(ICase fc _ exp ty clauses) >> ~(rest)) = do
      let tot = length clauses
      (clauses', conts) <- map unzip $ evalStateT Z $ for clauses $ \case
        PatClause fc' lhs rhs => do
          let names = bindVars lhs
          let vars = map (`MkAVar` `(_)) names
          let usedLater = map (\v => not (elem v.name names) && usedInDiagram rhs v.name) strings
          let strings' = vars ++ zipFilter strings usedLater
          t <- lift $ assert_total $ arrowImpl' ct ar ch [<] strings' rhs
          i <- get
          modify S
          pure (PatClause fc' lhs $ mkEither i tot $ pair $ map name strings', Just $ composeImp ct $ optimize t)
        ImpossibleClause fc' lhs => pure (ImpossibleClause fc' lhs, Nothing)
        WithClause fc' {} => failAt fc' "Unrecognized case pattern"
      let conts' = catMaybes conts
      case conts' of
        [] =>
          arrowImpl' ct ar ch (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase fc [] exp ty clauses'))))
            strings rest
        _ :: _ =>
          arrowImpl' ct ar ch (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                        ~(stringLam (map (,True) strings)
                        `(Builtin.MkPair ~(ICase fc [] exp ty clauses') ~(pair $ map name strings))))
                      :< `(Control.Arrow.first @{~ar} ~(foldr1 (\t,t' => `(Control.Arrow.(\|/) @{~ch} ~t ~t')) conts'))
                      :< `(Control.Arrow.arrow @{~ar} {a=_,b=_} Builtin.snd))
            strings rest
    arrowImpl' ct ar ch ts strings `(~(ICase fc _ exp ty clauses) >>= ~(rest)) = do
      let tot = length clauses
      (clauses', conts) <- map unzip $ evalStateT Z $ for clauses $ \case
        PatClause fc' lhs rhs => do
          let names = bindVars lhs
          let vars = map (`MkAVar` `(_)) names
          let usedLater = map (\v => not (elem v.name names) && usedInDiagram rhs v.name) strings
          let strings' = vars ++ zipFilter strings usedLater
          t <- lift $ assert_total $ arrowImpl' ct ar ch [<] strings' rhs
          i <- get
          modify S
          pure (PatClause fc' lhs $ mkEither i tot $ pair $ map name strings', Just $ composeImp ct $ optimize t)
        ImpossibleClause fc' lhs => pure (ImpossibleClause fc' lhs, Nothing)
        WithClause fc' {} => failAt fc' "Unrecognized case pattern"
      let conts' = catMaybes conts
      case conts' of
        [] =>
          arrowImplLam ct ar ch (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                      ~(stringLam (map (,True) strings) (ICase fc [] exp ty clauses'))))
            strings rest
        _ :: _ =>
          arrowImplLam ct ar ch (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                        ~(stringLam (map (,True) strings)
                        `(Builtin.MkPair ~(ICase fc [] exp ty clauses') ~(pair $ map name strings))))
                      :< `(Control.Arrow.first @{~ar} ~(foldr1 (\t,t' => `(Control.Arrow.(\|/) @{~ch} ~t ~t')) conts')))
            strings rest
    arrowImpl' ct ar ch ts strings (ILet fc fc' MW (UN $ Basic var) ty exp rest) = do
      (usedExp,usedLater,strings') <- do
        let usedExp = map (usedInExpr exp . name) strings
        let usedLater = map (\v => v.name /= var && usedInDiagram rest v.name) strings
        let strings' = MkAVar var ty :: zipFilter strings usedLater
        pure (usedExp,usedLater,strings')
      arrowImpl' ct ar ch
        (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = ~(pairTy strings')}
          ~(stringLam (zip strings $ zipWith (\x,y => x || y) usedExp usedLater)
            (ILet fc fc' MW (UN $ Basic var) ty exp (pair $ map name strings')))))
        strings' rest
    arrowImpl' ct ar ch ts strings (ILet fc {}) = failAt fc "Let binding must be unrestricted"
    arrowImpl' ct ar ch ts strings `((~(mor) -< ~(inp)) >>= ~(rest)) =
      case strings of
        [] => arrowImplLam ct ar ch (ts :< `(Control.Arrow.arrow @{~ar} {a=_,b=_} (\_ => ~inp)) :< mor) [] rest
        _ :: _ => do
          (usedInp,usedLater,strings') <- do
            let usedInp = map (usedInExpr inp . name) strings
            let usedLater = map (usedInDiagram rest . name) strings
            let strings' = zipFilter strings usedLater
            pure (usedInp,usedLater,strings')
          case strings' of
            [] =>
              arrowImplLam ct ar ch
                (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings),b=_}
                          ~(stringLam (zip strings usedInp) inp))
                    :< mor)
                strings' rest
            _ :: _ =>
              arrowImplLam ct ar ch
                (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = Builtin.Pair _ ~(pairTy strings')}
                  ~(stringLam (zip strings $ zipWith (\x,y => x || y) usedInp usedLater)
                    `(Builtin.MkPair ~inp ~(pair $ map name strings'))))
                    :< `(Control.Arrow.first @{~ar} ~mor))
                strings' rest
    arrowImpl' ct ar ch ts strings `((~(mor) -< ~(inp)) >> ~(rest)) =
      case strings of
        [] => arrowImpl' ct ar ch (ts
          :< `(Control.Arrow.arrow @{~ar} {a=Builtin.Unit,b=_} (\_ => ~inp))
          :< mor
          :< `(Control.Arrow.arrow @{~ar} {a=_,b=Builtin.Unit} (\_ => Builtin.MkUnit))) [] rest
        _ :: _ => do
          (usedInp,usedLater,strings') <- do
            let usedInp = map (usedInExpr inp . name) strings
            let usedLater = map (usedInDiagram rest . name) strings
            let strings' = zipFilter strings usedLater
            pure (usedInp,usedLater,strings')
          case strings' of
            [] =>
              arrowImpl' ct ar ch
                (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                          ~(stringLam (zip strings usedInp) inp))
                    :< mor :< `(Control.Arrow.arrow @{~ar} {a=_,b=_} (\_ => ())))
                strings' rest
            _ :: _ =>
              arrowImpl' ct ar ch
                (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = Builtin.Pair _ ~(pairTy strings')}
                        ~(stringLam (zip strings $ zipWith (\x,y => x || y) usedInp usedLater)
                          `(Builtin.MkPair ~inp ~(pair $ map name strings'))))
                    :< `(Control.Arrow.first @{~ar} ~mor) :< `(Control.Arrow.arrow @{~ar} {a=_,b=_} Builtin.snd))
                strings' rest
    arrowImpl' ct ar ch ts strings `(~(mor) -< ~(inp)) =
      pure (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings), b = _}
                    ~(stringLam (map (,True) strings) inp))
                :< mor)
    arrowImpl' ct ar ch ts strings `(=< ~(out)) =
      pure (ts :< `(Control.Arrow.arrow @{~ar} {a = ~(pairTy strings),b=_}
        ~(stringLam (map (,True) strings) out)))

    arrowImpl' _ _ _ _ _ (IHole fc _) = failAt fc "Holes are not allowed as top-level commands"
    arrowImpl' _ _ _ _ _ (ILam fc {}) = failAt (getFC t) "Lambda not allowed here"
    arrowImpl' _ _ _ _ _ t = failAt (getFC t) "Could not parse expression"

||| Enter arrow notation.
|||
||| This elaboration script must be specifically invoked with
||| `%runElab`. The category is inferred from the return type.
export
arrowDo : {0 arr : Hom Type0} -> (0 _ : Arrow arr) => TTImp -> Elab (arr (W0 a) (W0 b))
arrowDo @{impl} t = check !(arrowImpl (Just (!(quote impl), False)) t)

||| Enter arrow notation. Unlike `arrowDo`, this script allows you to
||| explicitly provide an `ArrowChoice` implementation instead of
||| searching for one.
|||
||| This elaboration script must be specifically invoked with
||| `%runElab`. The category is inferred from the return type.
export
arrowChoiceDo : {0 arr : Hom Type0} -> (0 _ : ArrowChoice arr) => TTImp -> Elab (arr (W0 a) (W0 b))
arrowChoiceDo @{impl} t = check !(arrowImpl (Just (!(quote impl), True)) t)
