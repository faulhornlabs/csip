-- usage
--
--  $ rlwrap idris2 functionalAssembly.idr
--  > :exec main
--  > :quit
--  $ gcc -Os -fverbose-asm -masm=intel -nostdlib -S -o fib.s fib.c
--  $ gcc -c -o fib.o fib.s
--  $ ld -s -n -o fib fib.o
--  $ time ./fib

--------------------------------------

import Control.Monad.State
import System.File.ReadWrite

private infixl 9 *.
private infixr 0 ==>
private infixr 0 =->

--------------------------------------

(==>) : Type -> Type -> Type
a ==> b = (1 _ : a) -> b

(=->) : Type -> Type -> Type
a =-> b = a -> b

--------------------------------------

data BinOp = Add | Sub | And | Or | Shl | Shr | Mov

data Cond = Lt | Gt | Le | Ge | E | Ne

data Reg = MkReg Nat       -- register name

data Op : Type where
  BBinOpC   : BinOp -> Reg -> Int        -> Op
  BBinOpR   : BinOp -> Reg -> Reg        -> Op
  BWrite8CC :          Int -> Int -> Reg -> Op
  BWrite8RR :          Reg -> Reg -> Reg -> Op
  BPutStr   :          Reg -> Reg        -> Op
  BAlloc    :          Int -> Reg        -> Op

data Label = MkLabel String

-- untyped DeBruijn Code
data DBCode : Type where
  BLam      :                                   DBCode ==> DBCode
  BApps     : List Reg ->                       DBCode ==> DBCode
  BLet      : DBCode             -> (DBCode -> DBCode) ==> DBCode
  BLetRec   : (DBCode -> DBCode) -> (DBCode -> DBCode) ==> DBCode
  BCondC    : Cond -> Reg -> Int ->  (Bool ==> DBCode) ==> DBCode
  BOp       : Op ->                             DBCode ==> DBCode
  BMovA     : DBCode -> Reg ->                  DBCode ==> DBCode
  BJmp      : Reg ->                                       DBCode
  BEmb      : Label ->                                     DBCode


Eq Reg where
  MkReg a == MkReg b = a == b


-------------------------------------- C code generation

CGen = State (Nat, List String)

newLabel : CGen Label
newLabel = state $ \(i, ss) => ((i + 1, ss), MkLabel $ "l" ++ show i)

emit : String -> CGen ()
emit s = modify $ \(i, ss) => (i, s :: ss)

emitInst s = emit ("    " ++ s ++ ";")

showLabel : Label -> String
showLabel (MkLabel s) = s

emitLabel s = emit ("  " ++ showLabel s ++ ":")

showReg : Reg -> String
showReg (MkReg r) = "r" ++ show r

genXchgs : Nat -> List Reg -> List (Reg, Reg)
genXchgs _ Nil = Nil
genXchgs j (i@(MkReg ii) :: is) = case ii == j of
  True  => genXchgs (j+1) is
  False => (i, MkReg j) :: genXchgs (j+1) (map (\r => if MkReg j == r then i else r) is)

emitXchg : (Reg, Reg) -> CGen ()
emitXchg (i, j) = emitInst ("XCHG(" ++ showReg i ++ ", " ++ showReg j ++ ")")

showPerm : List Reg -> CGen ()
showPerm rs = sequence_ $ map emitXchg $ genXchgs 0 rs

showBinOp : BinOp -> String -> String -> String
showBinOp Mov a b = a ++ "  = "  ++ b
showBinOp Add a b = a ++ " += "  ++ b
showBinOp Sub a b = a ++ " -= "  ++ b
showBinOp And a b = a ++ " &= "  ++ b
showBinOp Or  a b = a ++ " |= "  ++ b
showBinOp Shl a b = a ++ " <<= " ++ b
showBinOp Shr a b = a ++ " >>= " ++ b

showCond : Cond -> String -> String -> String
showCond Lt a b = a ++ " < "  ++ b
showCond Gt a b = a ++ " > "  ++ b
showCond Le a b = a ++ " <= " ++ b
showCond Ge a b = a ++ " >= " ++ b
showCond E  a b = a ++ " == " ++ b
showCond Ne a b = a ++ " != " ++ b

showOp : Op -> String
showOp (BBinOpC op r i)   = showBinOp op (showReg r)  (show    i)
showOp (BBinOpR op r1 r2) = showBinOp op (showReg r1) (showReg r2)
showOp (BWrite8CC i j m)  = "((char*)" ++ showReg m ++ ")[" ++ show    i ++ "] = " ++ show    j
showOp (BWrite8RR i j m)  = "((char*)" ++ showReg m ++ ")[" ++ showReg i ++ "] = " ++ showReg j
showOp (BPutStr i m)      = "PUTSTR(" ++ showReg i ++ ", " ++ showReg m ++ ")"
showOp (BAlloc i m)       = "ALLOC("  ++ show    i ++ ", " ++ showReg m ++ ")"


pr : DBCode -> CGen ()
pr (BApps a b) = showPerm a >> pr b
pr (BLet f g) = do
  l <- newLabel
  pr (g (BEmb l))
  emitLabel l
  pr f
pr (BLetRec f g) = do
  l <- newLabel
  pr (g (BEmb l))
  emitLabel l
  pr (f (BEmb l))
pr (BCondC co r i f) = do
  l <- newLabel
  emitInst $ "if (" ++ showCond co (showReg r) (show i) ++ ") goto " ++ showLabel l
  pr (f False)
  emitLabel l
  pr (f True)
pr (BOp op c)    = emitInst (showOp op) >> pr c
pr (BMovA p m c) = do
  l2 <- newLabel
  emitInst $ showReg m ++ " = (long)&&" ++ showLabel l2
  pr c
  emitLabel l2
  pr p
pr (BLam c) = pr c
pr (BEmb s) = emitInst ("goto " ++ showLabel s)
pr (BJmp r) = emitInst ("goto *(void*)" ++ showReg r)

regs : Nat -> List Reg
regs 0     = Nil
regs (S n) = MkReg n :: regs n

gen : Nat -> DBCode -> String
gen nr p =
  concat $ map (++ "\n") $
     "#define XCHG(a, b) tmp = a; a = b; b = tmp" ::
     "#define ALLOC(a, b) stack -= a; b = (long)stack" ::
     "#define EXIT \\" ::
     "  { \\" ::
     "  register int  x0 asm (\"rax\") = 60; \\" ::
     "  register long x1 asm (\"rdi\") = 0;  \\" ::
     "  __asm volatile (\"syscall\" : \"=a\" (tmp) : \"r\" (x0), \"r\" (x1) : \"rcx\", \"r11\", \"memory\"); \\" ::
     "  }" ::
     "#define PUTSTR(r0, r1) \\" ::
     "  { \\" ::
     "  register int  x0 asm (\"rax\") = 1; \\" ::
     "  register long x1 asm (\"rdi\") = 1; \\" ::
     "  register long x2 asm (\"rsi\") = r1; \\" ::
     "  register long x3 asm (\"rdx\") = r0; \\" ::
     "  __asm volatile (\"syscall\" : \"=a\" (tmp) : \"r\" (x0), \"r\" (x1), \"r\" (x2), \"r\" (x3) : \"rcx\", \"r11\", \"memory\"); \\" ::
     "  }" ::
     "" ::
     "__attribute__((naked))" ::
     "void _start() {" ::
     "    char stackMem[1 << 10]; char * stack = stackMem + (1 << 10);" ::
     "    long tmp;" ::
     "///////////////////////////////////////// generated" ::
     map (\r => "    long " ++ showReg r ++ ";") (reverse $ regs nr) ++
     reverse (snd $ fst $ runState (0, Nil) $ pr p) ++
     "///////////////////////////////////////// end of generated" ::
     "  exit:" ::
     "    EXIT;" ::
     "}" ::
     Nil


--------------------------------------

data Polarity : Type where
  Value       : Polarity
  Computation : Polarity

-- Object types
data Ty : Polarity -> Type where
  I       :                    Ty Value        -- integer in register
  Buffer  :                    Ty Value        -- pointer to memory block in register
  FunPtr  : Ty Computation ->  Ty Value        -- function pointer in register
  Fun     : List (Ty Value) -> Ty Computation

Vs = List (Ty Value)


-- assembly programs
data Code : (0 _ : Ty p) -> Type

CodeFun : (0 _ : Vs) -> Type
CodeFun t = Code (Fun t)

data Args : (0 _ : Vs) -> Type where
  ArgNil   : Args Nil
  ArgCons  : Code a ==> Args as ==> Args (a :: as)

data Code where
  Lam      : (Code a ==> CodeFun n) ==> CodeFun (a :: n)
  Let      : CodeFun k -> (CodeFun k -> CodeFun n) ==> CodeFun n
  LetRec   : (CodeFun k -> CodeFun k) -> (CodeFun k -> CodeFun n) ==> CodeFun n
  CondC    : Cond -> Code I ==> Int =-> (Bool ==> Code I ==> Code (Fun n)) ==> Code (Fun n)
  BinOpC   : BinOp -> Code I ==> Int =-> (Code I ==> CodeFun n) ==> CodeFun n
  BinOpR   : BinOp -> Code I ==> Code I ==> (Code I ==> Code I ==> CodeFun n) ==> CodeFun n
  Write8CC : Int -> Int -> Code Buffer ==> (Code Buffer ==> CodeFun n) ==> CodeFun n
  Write8RR : Code I ==> Code I ==> Code Buffer ==> (Code I ==> Code I ==> Code Buffer ==> CodeFun n) ==> CodeFun n
  PutStr   : Code I ==> Code Buffer ==> (Code I ==> Code Buffer ==> CodeFun n) ==> CodeFun n
  Alloc    : Int -> Code I ==> (Code Buffer ==> CodeFun n) ==> CodeFun n
  MovA     : (Code (FunPtr (Fun ts)) ==> CodeFun ts) -> Code I ==> (CodeFun ts ==> CodeFun n) ==> CodeFun n

  Idx'     : Reg -> Args m ==> CodeFun n
  Idx      : Reg -> Code {p = Value} t
  AppsEmb  : DBCode ==> Args m ==> CodeFun k


(*.) : CodeFun (a :: n) ==> Code a ==> CodeFun n
Lam f              *. b = f b
AppsEmb p as       *. b = AppsEmb p (ArgCons b as)
Idx' p bs          *. b = Idx' p (ArgCons b bs)
LetRec f g         *. b = LetRec f $ \p => g p *. b
Let p g            *. b = Let p $ \p => g p *. b
CondC co i r f     *. b = CondC co i r $ \c, p => f c p *. b
BinOpC op i r c    *. b = BinOpC op i r $ \r => c r *. b
BinOpR op r1 r2 c  *. b = BinOpR op r1 r2 $ \r1, r2 => c r1 r2 *. b
Write8CC i j m c   *. b = Write8CC i j m $ \m => c m *. b
Write8RR i j m c   *. b = Write8RR i j m $ \i, j, m => c i j m *. b
PutStr j m c       *. b = PutStr j m $ \j, m => c j m *. b
Alloc i m c        *. b = Alloc i m $ \m => c m *. b
MovA p r c         *. b = MovA p r $ \r => c r *. b

getRegs : Args n ==> (List Reg -> DBCode) ==> DBCode
getRegs ArgNil cont = cont Nil
getRegs (ArgCons (Idx i) p) cont = getRegs p $ \pe => cont (i :: pe)

emb : DBCode -> CodeFun n
emb d = AppsEmb d ArgNil

db : Nat -> CodeFun rs ==> DBCode
db j (Lam f)      = BLam (db (j+1) (f (Idx (MkReg j))))
db j (Let    f g) = BLet (db 0 f) (\p => db j (g (emb p)))
db j (LetRec f g) = BLetRec (\p => db 0 (f (emb p))) (\p => db j (g (emb p)))
db j (CondC co  (Idx ir) i cont) = BCondC co ir i $ \b => db j (cont b $ Idx ir)
db j (BinOpC op (Idx ir) i cont) = BOp (BBinOpC op ir i) (db j (cont $ Idx ir))
db j (BinOpR op (Idx ir1) (Idx ir2) cont) = BOp (BBinOpR op ir1 ir2) (db j (cont (Idx ir1) (Idx ir2)))
db j (Write8CC i i' (Idx im) cont) = BOp (BWrite8CC i i' im) (db j (cont $ Idx im))
db j (Write8RR (Idx ii) (Idx ii') (Idx im) cont) = BOp (BWrite8RR ii ii' im) (db j (cont (Idx ii) (Idx ii') (Idx im)))
db j (PutStr (Idx ii) (Idx im) cont) = BOp (BPutStr ii im) (db j (cont (Idx ii) (Idx im)))
db j (Alloc i (Idx im) cont)  = BOp (BAlloc i im) (db j (cont $ Idx im))
db j (MovA f (Idx im) cont)   = BMovA (db 1 $ f $ Idx $ MkReg 0) im (db j (cont $ Idx' im ArgNil))
db j (AppsEmb p as) = getRegs as $ \rs => BApps (reverse rs) p
db j (Idx' r as)    = getRegs as $ \rs => BApps (r :: reverse rs) (BJmp $ MkReg 0)

gen' : {ts : _} -> String -> (CodeFun ts' -> CodeFun ts) -> IO ()
gen' oname p = 
  writeFile oname (gen (length ts) (db 0 (p $ AppsEmb (BEmb $ MkLabel "exit") ArgNil))) >>= \_ => pure ()

-----------------------------------------------------------------------

add : Code I ==> Code I ==> (Code I ==> Code I ==> CodeFun n) ==> CodeFun n
add = BinOpR Add

subC : Code I ==> Int =-> (Code I ==> CodeFun n) ==> CodeFun n
subC = BinOpC Sub

movC : Code I ==> Int =-> (Code I ==> CodeFun n) ==> CodeFun n
movC = BinOpC Mov

fibP : CodeFun [Buffer, I, I, I] -> CodeFun [I, I, I, I]
fibP halt = let
  cont = Lam $ \m => Lam $ \a => Lam $ \n => Lam $ \b =>
       Write8CC 0 48 m $ \m =>
       Write8CC 1 120 m $ \m =>
       Write8CC 18 10 m $ \m =>
       LetRec (\go =>
            Lam $ \m => Lam $ \n => Lam $ \a => Lam $ \b =>
            CondC Ge n 2 $ \case
              True  => \n =>
                BinOpR Mov b a $ \b, a =>
                BinOpC And b 15 $ \b =>
                BinOpC Add b 48 $ \b =>
                Let (Lam $ \m => Lam $ \n => Lam $ \a => Lam $ \b =>
                    Write8RR n b m $ \n, b, m =>
                    BinOpC Shr a 4 $ \a =>
                    subC n 1 $ \n => 
                    go *. m *. n *. a *. b
                  ) $ \join =>
                CondC Gt b 57 $ \case
                  True => \b =>
                    BinOpC Add b 7 $ \b =>
                    join *. m *. n *. a *. b
                  False => \b =>
                    join *. m *. n *. a *. b
              False => \n =>
                movC n 19 $ \n =>
                PutStr n m $ \n, m =>
                halt *. m *. a *. n *. b
           ) $ \go =>
       movC n 17 $ \n => go *. m *. n *. a *. b
 in
  Lam $ \m =>
  Alloc 24 m $ \m =>
  LetRec
  (\go => Lam $ \m => Lam $ \n => Lam $ \a => Lam $ \b =>
    CondC Lt n 1 $ \case
     True  => \n => cont *. m *. a *. n *. b
     False => \n =>
       subC n 1 $ \n' =>
       add a b $ \a', b =>
       go *. m *. n' *. b *. a'
  )
  $ \go => Lam $ \n => Lam $ \a =>
     movC n 1000000000 $ \n =>
     movC a 0 $ \a =>
     Lam $ \b =>
     movC b 1 $ \b =>
     go *. m *. n *. a *. b


jmpP : CodeFun [FunPtr (Fun [I, I]), I, I] -> CodeFun [I, I, I]
jmpP halt =
  Lam $ \a => Lam $ \b => Lam $ \c =>
  Let (Lam $ \a => Lam $ \b => Lam $ \c =>
    halt *. a *. b *. c
    ) $ \go =>
  MovA (\a => go *. a) c $ \c =>
  c *. b *. a

main : IO ()
main = do
  gen' "fib.c" fibP
  gen' "jmp.c" jmpP
