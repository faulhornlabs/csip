{-# language MultilineStrings, BlockArguments, ViewPatterns, PatternSynonyms, NoMonomorphismRestriction #-}

import Data.Char
import Data.Function
import Data.List
import Data.Maybe

------------------------

modules =
  [ ("src/" <> f, "gen/" <> f) | f <-
    [ "B0_Builtins.hs", "B1_Basic.hs", "B2_String.hs", "B3_Mem.hs", "B5_Map.hs", "B8_OpSeq.hs", "B8_Doc.hs", "B9_IO.hs", "B_Base.hs"
    , "C1_Name.hs", "C2_NameLiterals.hs", "C3_Parse.hs", "C4_Desug.hs", "C5_Scope.hs", "C_Syntax.hs"
    , "D1_Combinator.hs", "D3_Val.hs-boot", "D2_Tm.hs", "D3_Val.hs", "D4_Eval.hs", "D5_Pattern.hs", "D_Calculus.hs"
    , "E1_Unify.hs", "E2_Conv.hs", "E3_Elab.hs", "E4_Stage.hs", "M_Main.hs"
    ]
  ]

------------------------

strings :: String -> ([String], (String -> String) -> (String -> String) -> String)
strings cs = g cs where

  add    s (a, b) = (s: a, b)
  put    s (a, b) = (a, \tr tr' ->     s <> b tr tr')
  putTr  s (a, b) = (a, \tr tr' -> tr  s <> b tr tr')
  putTr' s (a, b) = (a, \tr tr' -> tr' s <> b tr tr')

  g ('"': cs) = f ['"'] cs
  g (' ':'$': (span isAlpha -> (n@(_:_), cs))) = put (' ':[]) $ putTr n (g cs)
  g ('\'': '\\': '"': cs) = put ('\'': '\\': '"': []) (g cs)
  g ('\'': '"': cs) = put ('\'': '"': []) $ g cs
  g (c: cs) = put (c:[]) $ g cs
  g [] = ([], \_ _ -> [])

  f acc ('"': 'B': cs) | s <- read (reverse ('"': acc)) = putTr' s $ add s (g cs)
  f acc ('"': cs) = put (reverse ('"': acc)) (g cs)
  f acc ('\\': 'E': 'S': 'C': cs) = f ('C': 'S': 'E': '\\': acc) cs
  f acc ('\\': c: cs) | c `elem` "ntr\\\"'" = f (c: '\\': acc) cs
  f acc ('\\': cs) = error $ "TODO: " <> cs
  f acc (c: cs) = f (c: acc) cs
  f acc [] = error $ "unterminated string: " <> show (reverse acc)


mainTr mms = map tr' mms where

  parens a = "(" <> a <> ")"

  a <+> b = a <> " " <> b

  linePragma (mn, l) = "\n{-# LINE " <> show l <+> show mn <> " #-}\n"

  builtins = zip (nub (concatMap (fst . strings . snd) mms)) ["N" <> show n | n <- [0..]]

  dict =
    [ ("precTable",          \_ -> parens $ foldr
        (\(s, (l, r)) t -> "consTable" <+> show s <+> show l <+> show r <+> "$" <+> t) "emptyTable" precTable)
    , ("stringliterals",     \_ -> parens $ foldr (\a b -> show a <> " :. " <> b) "Nil" stringliterals)
    , ("builtinsModule",     \_ -> show builtinsModule <> "#")
    , ("preludeModule",      \_ -> show preludeModule  <> "#")
    , ("impossible",         \(mn, l) -> parens $ "impossible " <> show mn <> " " <> show l)
    , ("undefined",          \(mn, l) -> parens $ "undefined "  <> show mn <> " " <> show l)
    , ("tokenliterals",      \_ -> intercalate "\n" $ concatMap tlit builtins)
    , ("specialPrecedences", \_ -> intercalate "\n" $ map prec special)
    ]
   where
    stringliterals = map fst builtins \\ map fst precedenceTable

    special = ["MAXPREC", "MINPREC", "ALPHA", "GRAPHIC"]

    precTable = filter (not . (`elem` special) . fst) precedenceTable

    prec s = "prec" <> s <> " = " <> hsPrec (fromJust (lookup s precedenceTable)) where
      hsPrec (l, r) = "MkPrecedences" <+> show l <+> show r

    tlit (s, name) =
      [ "{-# noinline " <> lname <> " #-}"
      , lname <> " = fromStr " <> show s <> "#"
      , "pattern " <> name <> " <- (eqName " <> lname <> " -> True)"
      , "  where " <> name <> " = fromName " <> lname
      , ""
      ]
     where
      lname = "lit" <> name

  tr fn ('$': s) = fromJust (lookup s dict) fn <> linePragma fn
  tr fn cs = snd (strings cs) (\s -> fromJust (lookup s dict) fn) \s -> fromMaybe (error $ "ff: " <> s) (lookup s builtins)

  tr' (mn, s) = linePragma (mn, 1) <> unlines (zipWith (\n -> tr (mn, n)) [1..] (lines s))


main = do
  ms <- mapM (readFile . fst) modules
  sequence_ $ zipWith writeFile (map snd modules) $ mainTr $ zip (map fst modules) ms


------------------------

precedenceTable :: [(String, (Int, Int))]
precedenceTable = mkTable (lines precedences) where

  mkTable
    = map f
    . groupBy ((==) `on` fst)
    . sort
    . mconcat
    . zipWith (\p f -> f p) [1..]
    . reverse
    . map (mconcat . map g . words)

  f [(s, Left l), (_, Right r)] = (s, (l, r))

  g ('_': s)   = \p -> [(h s, Left  p)]
  g s | last s == '_' = \p -> [(h $ init s, Right p)]
  g _ = undefined

  h "BEGIN"   = "\t"
  h "END"     = "\r"
  h "NEWLINE" = "\n"
  h "SPACE"   = " "
  h s         = s

precedences = """
   ALPHA_ )_ ]_ }_ !>_ whereEnd_ whereBeg_ ofBeg_ ###_ ofEnd_
  _ALPHA _( _[ _{ _<! _if _let _\\ _import _class _instance _data _### _case _constructor
   constructor_ import_
  _whereBegin _ofBegin
   @_
  _@
  MAXPREC_ _MAXPREC
   ._
  _.
   GRAPHIC_
  _GRAPHIC
  _^
   ^_
   *_ /_
  _* _/
   +_ -_
  _+ _-
  _<>
   <>_
  _::
   ::_
   <$>_ <*>_
  _<$> _<*>
   <_ <=_ >_ >=_ ==_ /=_
  _< _<= _> _>= _== _/=
  _&&
   &&_
  _||
   ||_
   >>=_ >>_ <&>_
  _>>= _>> _<&>
  MINPREC_ _MINPREC
   else_
  _<-
   <-_
  _-> _~> _:-> _|-> _: _** _=> _==> _--> _---> \\_
   ->_ ~>_ :->_ |->_ :_ **_ =>_ ==>_ -->_ --->_
   in_
  _|
   |_
  _= _:=
   =_ :=_
  _,
   ,_
  _#
   #_
  _;
   ;_
   case_ _ofBeg
   class_ instance_ data_ _whereBeg
   whereBegin_ _whereEnd ofBegin_ _ofEnd
  _then
   then_
   let_ _in if_ _else
   [_ _] {_ _} (_ _) <!_ _!>
  _BEGIN _SEMI _do _where _of
   END_   SEMI_ do_ where_ of_
   BEGIN_ _END
  _SPACE
   SPACE_
  _{-
   -}_
   {-_ _-}
  _--
   --_
  _NEWLINE
   NEWLINE_
  _"
   "_
"""

----------------------------------------------------------------


builtinsModule = """

data builtin Type : Type where

-- (~>) is constructor application
constructor builtin Ap : (a ~> b) -> a -> b


data builtin Bool : Type where
  builtin True  : Bool
  builtin False : Bool

constructor builtin Word : Type

constructor builtin DecWord    : Word -> Word
constructor builtin AddWord    : Word -> Word -> Word
constructor builtin MulWord    : Word -> Word -> Word
constructor builtin ModWord    : Word -> Word -> Word
constructor builtin DivWord    : Word -> Word -> Word
constructor builtin EqWord     : Word -> Word -> Bool

data WSucView : Type where
  builtin WSucOk    : Word -> WSucView
  builtin WSucFail  : WSucView

builtin SuccView : Word -> WSucView
SuccView 0 = WSucFail
SuccView n = WSucOk (DecWord n)

constructor builtin WSuc : Word -> Word

-- pattern WSuc n <- (SuccView --> WSucOk n)
-- WSuc = \\n -> AddWord 1 n


constructor builtin String : Type

constructor builtin AppendStr : String -> String -> String
constructor builtin EqStr     : String -> String -> Bool
constructor builtin TakeStr   : Word -> String -> String
constructor builtin DropStr   : Word -> String -> String

data ConsViewData : Type where
  builtin ConsOk    : String -> String -> ConsViewData
  builtin ConsFail  : ConsViewData

builtin ConsView : String -> ConsViewData
ConsView "" = ConsFail
ConsView n = ConsOk (TakeStr 1 n) (DropStr 1 n)

constructor builtin ConsStr : String -> String -> String
-- pattern ConsStr a b <- (ConsView --> ConsOk a b)


data builtin Nat : Type where
  Zero : Nat
  Suc  : Nat -> Nat

builtin wordToNat : Word -> Nat
wordToNat 0 = Zero
wordToNat (WSuc i) = Suc (wordToNat i)


-- Object code
constructor builtin Ty : Type
constructor builtin Code : Ty -> Type

constructor builtin Arr : Ty -> Ty -> Ty
constructor builtin Lam : {a b : Ty} -> (a -> b) -> Arr a b
constructor builtin App : Arr a b -> a -> b
constructor builtin Let : {a b : Ty} -> a -> (a -> b) -> b
constructor builtin TopLet : {a b : Ty} -> a -> a -> b -> b

constructor builtin Prod : Ty -> Ty -> Ty
constructor builtin Pair : {a b : Ty} -> a -> b -> Prod a b
constructor builtin Fst : Prod a b -> a
constructor builtin Snd : Prod a b -> b

data builtin OBool : Ty where
  builtin OTrue  : OBool
  builtin OFalse : OBool

data builtin OString : Ty where
  builtin MkOString : String -> OString

constructor builtin OEqStr : OString -> OString -> OBool

data builtin OWord : Ty where
  builtin MkOWord : Word -> OWord

constructor builtin OEqWord : OWord -> OWord -> OBool


-- Type classes

builtin lookupDict : (a : Type) -> a

data builtin SuperClassList : (a : Type) -> Type where
  builtin SuperClassNil  : (a : Type) -> SuperClassList a
  builtin SuperClassCons : (a : Type) -> (b : Type) -> (a -> b) -> SuperClassList a -> SuperClassList a

builtin superClasses : (a : Type) -> SuperClassList a
"""

----------------------------------------------------------------

preludeModule = """

import Builtins


appendStr = AppendStr

class Eq (a : Type) where
  (==) : a -> a -> Bool

instance Eq Word where
  a == b = EqWord a b

instance Eq String where
  a == b = EqStr a b


class Num (a : Type) where
  (+)     : a -> a -> a
  (*)     : a -> a -> a
  fromWord : Word -> a

instance Num Word where
  a + b = AddWord a b
  a * b = MulWord a b
  fromWord n = n

even : Word -> Bool
  = \\n -> ModWord n 2 == 0
odd  : Word -> Bool
  = \\n -> ModWord n 2 == 1

div = DivWord


the : (a : Type) -> a -> a
  = \\_ x -> x


data Unit : Type where
  TT : Unit

data Tuple2 : Type -> Type -> Type where
  T2 : a -> b -> Tuple2 a b

first : (a -> b) -> Tuple2 a c -> Tuple2 b c
first f (T2 x y) = T2 (f x) y

second : (a -> b) -> Tuple2 c a -> Tuple2 c b
second f (T2 x y) = T2 x (f y)


data Tuple3 : Type -> Type -> Type -> Type where
  T3 : a -> b -> c -> Tuple3 a b c

data Maybe : Type ~> Type where
  Nothing : Maybe a
  Just    : a -> Maybe a

data List : Type ~> Type where
  Nil    : List a
  Cons  : a -> List a -> List a
"""
