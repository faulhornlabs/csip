module D3_Val
  ( Val ( WLam, WApp, WApp_, WMeta, WVar, WCon_, WCon, WSup, WFun, WPrimOp, WNat, WString)
  , renameVal
  , vVar
  , Tm, PTm (TGen)
  , AppCached (..), mkApp_
  , vSup, vTm, vNat, vString, mkFun, vLam_, mkBuiltin

  , RuleRef, lookupRule, updateRule_
  , updateMeta, lookupMeta, tMeta, MetaRef, metaRef, MetaDep(..), mkMetaRef
  , addDef, getDefs
  , getGlue
  ) where

import C_Syntax
import D1_Combinator
import D2_Tm

-------------------------- value representation

data Val
  = WCon_   SName Closed
  | WPrimOp SName Arity (Mem Val -> List Val -> Mem Val)
  | WMeta_  SName Closed MetaRef
  | VFun    SName Rigid  RuleRef
  | VNat    SName Word
  | VString SName String
  | VApp_   SName Rigid Closed Val Val AppCached
  | VSup    SName Rigid Closed (Combinator Val) (List Val)

data AppCached
  = ConApp     SName Closed RArity
  | PrimOpApp  SName RArity Arity
  | MetaApp    MetaRef MetaDep
  | FunApp     Val

data RuleRef = MkRuleRef (Ref Val)

data MetaRef = MkMetaRef (Ref (Maybe Val))

data MetaDep = MkMetaDep SName MetaRef

type RArity = Word

-------------------------------- instances

instance HasName MetaDep where name (MkMetaDep n _) = n

instance HasId MetaDep where getId = getId . name

-- invariant:  name v == name w  ==>   v == w
instance HasName Val where
  name = \case
    WCon_ n _         -> n
    VFun n _ _        -> n
    WPrimOp n _ _     -> n
    VNat n _          -> n
    VString n _       -> n
    WMeta_ n _ _      -> n
    VSup n _ _ _ _    -> n
    VApp_ n _ _ _ _ _ -> n

-- TODO: remove
renameVal :: SName -> Val -> Val
renameVal s = \case
  WCon_ n a         -> WCon_ (f n) a
  VFun n a b        -> VFun (f n) a b
  WPrimOp n a b     -> WPrimOp (f n) a b
  VNat n a          -> VNat (f n) a
  VString n a       -> VString (f n) a
  WMeta_ n a b      -> WMeta_ (f n) a b
  VSup n a b c d    -> VSup (f n) a b c d
  VApp_ n a b c d e -> VApp_ (f n) a b c d e
 where
  f _ = s

instance HasId Val where getId = getId . name

instance IsClosed Val where
  closed = \case
    WCon_ _ c         -> c
    VSup  _ _ c _ _   -> c
    VApp_ _ _ c _ _ _ -> c
    WMeta_ _ c _      -> c
    VFun{}     -> True
    WPrimOp{}  -> True
    VNat{}     -> True
    VString{}  -> True

instance IsRigid Val where
  rigid = \case
    WMeta_{} -> False
    VSup  _ r _ _ _   -> r
    VApp_ _ r _ _ _ _ -> r
    VFun _ r _        -> r
    WCon_{}   -> True
    WPrimOp{} -> True
    VNat{}    -> True
    VString{} -> True

instance IsRigid AppCached where
  rigid = \case
    MetaApp{}    -> False
    FunApp v     -> rigid v
    PrimOpApp{}  -> True
    ConApp{}     -> True

instance Print MetaDep where print = print . name

instance PPrint Val where
  pprint = \case
    WNat n        -> pprint n
    WString n     -> pprint n
    WVar n        -> "Var"B    <@> pprint n
    WSup _ c vs   -> "Sup"B    <@> pprint c <@> pprint vs
    WCon n        -> "Con"B    <@> pprint n
    WMeta_ n _ _  -> "Meta"B   <@> pprint n
    WApp a b      -> "@"B      <@> pprint a <@> pprint b
    WPrimOp n _ _ -> "PrimOp"B <@> pprint n
    WFun n _      -> "Fun"B    <@> pprint n
    _ -> $undefined

---------------------------------

pattern WCon n = WCon_ n True
pattern WVar n = WCon_ n False

infixl 9 `WApp`

pattern WFun i f    <- VFun i _    f
  where WFun i f    =  VFun i True f
pattern WNat n      <- VNat _ n
pattern WString n   <- VString _ n
pattern WSup n a b  <- VSup n _ _ a b
pattern WApp_ a b c <- VApp_ _ _ _ a b c
pattern WLam f      <- WSup _ (varName -> Just f) _
pattern WApp a b    <- WApp_ a b _

getMetaDep (WMeta_ n _ r) = Just (MkMetaDep n r)
getMetaDep _ = Nothing

pattern WMeta d <- (getMetaDep -> Just d)

pattern TGen :: Tm -> Tm
pattern TGen a = "TGen"B :@. a

vNat :: Word -> Mem Val
vNat i = nameOf "i"B <&> \n -> VNat n i

vString :: String -> Mem Val
vString i = nameOf "s"B <&> \n -> VString n i

mkApp_ aa u l = nameOf "a"B <&> \n -> VApp_ n (rigid aa && rigid u && rigid l) (closed aa && closed u) aa u l

vSup :: Combinator Val -> List Val -> Mem Val
vSup c vs = nameOf "l"B <&> \n -> VSup n (rigid c && all rigid vs) (all closed vs) c vs

vLam_ :: SName -> Tm -> Mem Val
vLam_ n t = do
  T2 c ns <- mkCombinator n t
  vSup c =<< mapM vVar ns

vVar :: SName -> Mem Val
vVar n = lookupGlobalVal n <&> \case
  Just v -> v
  _      -> WVar n

------------

{-# noinline glueR #-}
glueR :: State (IntMap SName Tm)
glueR = topState mainReset $ pure emptyIM

addGlue n t = modify glueR (insertIM n t)
getGlue n = gets glueR (lookupIM n)

vTm :: NameStr -> Tm -> Val -> Mem Val
vTm _n t v = do
  addGlue (name v) t       -- TODO: check rigidity and closedness?
  pure v

--------

metaRef (MkMetaDep _ r) = r

mkMetaRef = MkMetaRef <$> newRef Nothing

tMeta :: Mem Tm
tMeta = do
  n <- nameOf "m"B
  v <- WMeta_ n False{-TODO!-} <$> mkMetaRef
  let t = TVar n
  addDef True n t
  insertGlobalVal n v
  pure t

lookupRule :: RuleRef -> Mem Val
lookupRule (MkRuleRef r) = readRef r

updateRule_ :: RuleRef -> Val -> Mem Tup0
updateRule_ (MkRuleRef r) b = writeRef r b

lookupMeta :: MetaRef -> Mem (Maybe Val)
lookupMeta (MkMetaRef r) = readRef r

updateMeta :: MetaRef -> Val -> Mem Tup0
updateMeta (MkMetaRef r) b = writeRef r $ Just b

---------------------

metaFun i f = (VFun i False{-hack?-} f)

{-# noinline lookupDictFun #-}
lookupDictFun = metaFun "lookupDict"B $ MkRuleRef $ topRef mainReset "Fail"B

{-# noinline superClassesFun #-}
superClassesFun = metaFun "superClasses"B $ MkRuleRef $ topRef mainReset "Fail"B

{-# noinline succViewFun #-}
succViewFun = WFun "SuccView"B $ MkRuleRef $ topRef mainReset "Fail"B

{-# noinline consViewFun #-}
consViewFun = WFun "ConsView"B $ MkRuleRef $ topRef mainReset "Fail"B

{-# noinline wordToNatFun #-}
wordToNatFun = WFun "wordToNat"B $ MkRuleRef $ topRef mainReset "Fail"B

{-# noinline matchRetFun #-}
matchRetFun = WFun "matchRet"B $ MkRuleRef $ topRef_ mainReset $ nameOf "v"B >>= \n -> vLam_ n $ TVar n

{-# noinline tGenFun #-}
tGenFun = WFun "TGen"B $ MkRuleRef $ topRef_ mainReset $ nameOf "v"B >>= \n -> vLam_ n $ "TRet"B :@. TVar n

mkFun_ :: SName -> Maybe Val
mkFun_ = \case
  "SuccView"B     -> Just succViewFun
  "ConsView"B     -> Just consViewFun
  "lookupDict"B   -> Just lookupDictFun
  "superClasses"B -> Just superClassesFun
  "wordToNat"B    -> Just wordToNatFun
  "matchRet"B     -> Just matchRetFun
  "TGen"B         -> Just tGenFun
  _ -> Nothing

mkFun :: SName -> Mem Val
mkFun n = maybe (WFun n . MkRuleRef <$> newRef "Fail"B) pure $ mkFun_ n

mkBuiltin :: SName -> Val
mkBuiltin n = case n of
  "AppendStr"B  -> f 2 \d -> \case WString va :. WString vb :. Nil -> vString $ va <> vb; _ -> d
  "EqStr"B      -> f 2 \d -> \case WString va :. WString vb :. Nil -> pure $ cBool (va == vb); _ -> d
  "TakeStr"B    -> f 2 \d -> \case WNat va :. WString vb :. Nil -> vString $ takeStr va vb; _ -> d
  "DropStr"B    -> f 2 \d -> \case WNat va :. WString vb :. Nil -> vString $ dropStr va vb; _ -> d
  "DecWord"B    -> f 1 \d -> \case WNat va :. Nil -> vNat $ max 0 $ va - 1; _ -> d
  "AddWord"B    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va + vb; _ -> d
  "MulWord"B    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va * vb; _ -> d
  "DivWord"B    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va `div` vb; _ -> d
  "ModWord"B    -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> vNat $ va `mod` vb; _ -> d
  "EqWord"B     -> f 2 \d -> \case WNat va :. WNat vb :. Nil -> pure $ cBool (va == vb); _ -> d
  n | Just v <- mkFun_ n -> v
  n -> WCon n
-- TODO:  n -> error $ "Unknown builtin: " <> print n
 where
  f ar g = WPrimOp n ar g

  cBool True = "True"B
  cBool _    = "False"B

instance IsName Tm where
  fromName = TVal . fromName
  eqName a (TVal b) = eqName a b
  eqName a (TVar b) = eqName a b
  eqName _ _        = False

instance IsName Val where
  fromName = mkBuiltin . fromName
  eqName a b = getId a == getId b

-----------------

{-# noinline defsR #-}
defsR :: State (List (Tup3 Bool SName Tm))
defsR = topState mainReset $ pure Nil

addDef cstr n i = modify defsR (T3 cstr n i :.)
getDefs = gets defsR id
