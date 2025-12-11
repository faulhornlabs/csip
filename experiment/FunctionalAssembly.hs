{-

======================== Context

Project goal

  High-level programming with predictable and good performance

  Target problems:
    complex, performance critical computation problems

  Target users:
    functional programmers with performance sensitive mindset


Approach

  1. Invent a simple language which is
    - a functional language
    - close to assembly

  2. Add zero cost abstractions to this language


This lecture targets (1.)


======================== Contents

- CPU interpreter

- functional assembly language
  - interpreter
  - compiler

-}

---------------------------------------------------------------- Haskell code

{-# language OverloadedStrings #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

import Data.String
import Data.Function
import Control.Monad.State
import Control.Monad.Writer


----------------------------------- tools

type Map a b = a -> b

insert :: Eq a => a -> b -> Map a b -> Map a b
insert x0 y0 f x | x == x0   = y0
                 | otherwise = f x


----------------------------------- abstract CPU interpreter

type RegName = String   -- register name
type Address = Int      -- RAM address

-- memory locations (memory = register file + RAM)
data Loc
  = Reg RegName
  | Mem Address
  deriving (Eq, Ord)

instance Show Loc where
  show (Reg r) = r
  show (Mem a) = "#" ++ show a

type Mem = Map Loc Int

initMem :: Mem
initMem _ = 0

data Arg
  = Immediate Int
  | LocArg Loc
  deriving (Eq, Ord)

instance Show Arg where
  show (Immediate i) = show i
  show (LocArg l) = show l

getArg :: Arg -> Mem -> Int
getArg (Immediate i) m = i
getArg (LocArg l)    m = m l


data BinOp = Add | Sub | Mul | Mov
  deriving (Eq, Ord, Show)

evalBinOp :: BinOp -> Int -> Int -> Int
evalBinOp Add = (+)
evalBinOp Sub = (-)
evalBinOp Mul = (*)
evalBinOp Mov = \a b -> b

data Condition = E | NE | G | GE | L | LE
  deriving (Eq, Ord, Show)

evalCondition :: Condition -> Int -> Int -> Bool
evalCondition E  = (==)
evalCondition NE = (/=)
evalCondition G  = (>)
evalCondition GE = (>=)
evalCondition L  = (<)
evalCondition LE = (<=)

-- Assembly instructions
-- - instructions contain the address of the next instruction
-- - this address is abstracted out as a parameter
data Instruction ip
  = BinOp BinOp   Loc Arg ip
  | Xchg          Loc Loc ip
  | Jcc Condition Loc Arg ip ip
  | Jmp                   ip
  | Halt

-- instruction evaluation
-- - what to do next is abstracted out (cont)
evalInstruction :: (ip -> Mem -> Mem) -> Instruction ip -> Mem -> Mem
evalInstruction cont i m = case i of
  BinOp op l  a  ip     -> cont ip (insert l (evalBinOp op (m l) (getArg a m)) m)
  Xchg     l1 l2 ip     -> cont ip (insert l1 (m l2) (insert l2 (m l1) m))
  Jcc c    l  a  ip ip' -> cont (if evalCondition c (m l) (getArg a m) then ip else ip') m
  Jmp            ip     -> cont ip m
  Halt                  -> m

----------------------------------- tools

instance IsString Loc where
  fromString = Reg

instance IsString Arg where
  fromString s | [(i, "")] <- reads s = Immediate i
  fromString s = LocArg (fromString s)

instance Num String where
  fromInteger = show
  (+)    = undefined
  (-)    = undefined
  (*)    = undefined
  abs    = undefined
  signum = undefined

----------------------------------- CPU interpreter (I.)

type IP = Int   -- instruction pointer

type ProgramI = Map IP (Instruction IP)

evalProgramI :: ProgramI -> Mem -> Mem
evalProgramI prg m = loop 0 m
 where
  loop :: IP -> Mem -> Mem
  loop ip m = evalInstruction loop (prg ip) m

-- example program
fibI :: ProgramI
fibI = p
 where
  p 0 = mov  a 0      1
  p 1 = mov  b 1      2
  p 2 = less n 1   7  3
  p 3 = sub  n 1      4
  p 4 = add  a b      5
  p 5 = xchg a b      6
  p 6 = Jmp 2
  p 7 = Halt

  n = "r0"
  a = "r1"
  b = "r2"

  -- smart constructors
  less a b = Jcc   L   (fromString a) (fromString b)
  mov  a b = BinOp Mov (fromString a) (fromString b)
  add  a b = BinOp Add (fromString a) (fromString b)
  sub  a b = BinOp Sub (fromString a) (fromString b)
  xchg a b = Xchg      (fromString a) (fromString b)

testFibI :: Int -> Int
testFibI i = evalProgramI fibI (insert "r0" i initMem) "r1"

{-
Pros
- ProgramI is easy to compile to assembly

Cons
- construction of ProgramI needs explicit instruction numbering
-}


----------------------------------- CPU interpreter (II.)

data ProgramII
  = Prg (Instruction ProgramII)
  | Fix (ProgramII -> ProgramII)
  | Label String

evalProgramII :: ProgramII -> Mem -> Mem
evalProgramII p m = case p of
  Prg i -> evalInstruction evalProgramII i m
  Fix f -> evalProgramII (fix f) m

-- example program
fibII :: ProgramII
fibII = start
 where
  start =
    mov  a 0  $
    mov  b 1  $
    loop

  loop = Fix $ \loop ->
    less n 1  halt  $
    sub  n 1  $
    add  a b  $
    xchg a b  $
    loop

  halt =
    Prg Halt

  n = "r0"
  a = "r1"
  b = "r2"

  -- smart constructors
  less a b c d = Prg $ Jcc   L   (fromString a) (fromString b) c d
  mov  a b c   = Prg $ BinOp Mov (fromString a) (fromString b) c
  add  a b c   = Prg $ BinOp Add (fromString a) (fromString b) c
  sub  a b c   = Prg $ BinOp Sub (fromString a) (fromString b) c
  xchg a b c   = Prg $ Xchg      (fromString a) (fromString b) c

testFibII :: Int -> Int
testFibII i = evalProgramII fibII (insert "r0" i initMem) "r1"


compileProgramII :: ProgramII -> String
compileProgramII p = unlines $ snd $ runWriter $ evalStateT (go p) 0
 where
  go :: ProgramII -> StateT Int (Writer [String]) ()
  go p = case p of
    Prg i -> case i of
      Xchg a b c -> do
        emit $ "  Xchg" ++ " " ++ show a ++ " " ++ show b
        go c
      BinOp op a b c -> do
        emit $ "  " ++ show op ++ " " ++ show a ++ " " ++ show b
        go c
      Jcc cond a b c1 c2 -> do
        l <- newLabel
        emit $ "  J" ++ show cond ++ " " ++ show a ++ " " ++ show b ++ " " ++ l
        go c2
        emit $ l ++ ":"
        go c1
      Jmp c -> undefined
      Halt -> emit "  Halt"
    Fix f -> do
      l <- newLabel
      emit $ l ++ ":"
      go (f $ Label l)
    Label l -> emit $ "  jmp " ++ l

  emit s = tell [s]
  newLabel = state $ \s -> ("l" ++ show s, s+1)

testFibII' = putStrLn $ compileProgramII fibII

{-
Pros
- no need for explicit instruction numbering

Cons
- construction of ProgramII needs explicit register numbering
-}






{-
----------------------------------- What is next

The following representation (ProgramIV) abstracts out register numbering.

To be able to compile ProgramIV to assembly we introduce the lover level
ProgramIII representation which still abstracts out register numbering but
it is easier to compile it to assembly.

-}


----------------------------------- abstracting out register numbering

-- HOAS representation of programs
data ProgramIV
  = BinOpIV  BinOp     Int Int (Int -> ProgramIV)
  | MovIV                  Int (Int -> ProgramIV)
  | JccIV    Condition Int Int ProgramIV ProgramIV
  | HaltWithIV Int


evalProgramIV :: ProgramIV -> Int
evalProgramIV p = case p of
  BinOpIV op a b c  -> evalProgramIV (c (evalBinOp op a b))
  MovIV        i c  -> evalProgramIV (c i)
  JccIV c a b c1 c2 -> evalProgramIV (if evalCondition c a b then c1 else c2)
  HaltWithIV i      -> i

-- example program
-- a continuation is used to handle the result
fibIV :: Int -> (Int -> ProgramIV) -> ProgramIV
fibIV n end = start n
 where
  start n =
    mov 0 $ \a ->
    mov 1 $ \b ->
    loop n a b
  loop n a b =
    less n 1  (end a)  $
    sub  n 1  $ \n' ->
    add  a b  $ \ab ->
    loop n' b ab

  less = JccIV L
  mov  = MovIV
  add  = BinOpIV Add
  sub  = BinOpIV Sub

testFibIV :: Int -> Int
testFibIV i = evalProgramIV (fibIV i HaltWithIV)

{-
Pros
- register naming is abstracted out

Cons
- it is not easy to compile ProgramIV to assembly
-}






{-
ProgramIII is described in functionalAssembly.idr
-}

