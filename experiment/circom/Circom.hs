{-# language LambdaCase, BlockArguments, PatternSynonyms, ViewPatterns #-}
module Circom
  ( Name, Circom (..), CircomInput (..), Constraint (..), Linear (..), F, mkF, publishCircom, runCircom, verifyCircom
  ) where

import Data.List
import Data.Char
import Data.Ratio
import Control.Arrow
import Data.Functor

import System.Environment (getArgs)
import System.Process (readProcess, proc, readCreateProcess, CreateProcess(..), readProcessWithExitCode)
import System.Exit (ExitCode(..))
import System.Directory (doesFileExist, getHomeDirectory)

----------------------------------------------------

-- bn254
fieldOrder = 21888242871839275222246405745257275088548364400416034343698204186575808495617 :: Integer
-- fieldBits = 254 :: Int

newtype F = MkF Integer
  deriving (Eq, Ord, Enum, Real, Integral)

instance Show F where
  show (MkF f)
--    | f > fieldOrder `div` 2 = show (f - fieldOrder)
    | otherwise              = show f

instance Read F where
  readsPrec i s = map (first mkF) (readsPrec i s)

mkF = MkF . (`mod` fieldOrder)

instance Num F where
  fromInteger = mkF
  MkF a + MkF b = mkF (a + b)
  MkF a - MkF b = mkF (a - b)
  MkF a * MkF b = mkF (a * b)
  abs    = undefined
  signum = undefined

instance Fractional F where
  fromRational a = fromInteger (numerator a) / fromInteger (denominator a)
  recip (MkF a) = MkF $ go 0 1 fieldOrder a  where

    go t nt r 0  = if t < 0 then t + fieldOrder else t
    go t nt r nr = go nt (t - q*nt) nr m  where (q, m) = r `divMod` nr

---------------------------------

type Name = String

data Linear = MkLinear F [(F, Name)]

data Constraint a
  = CEq  a a
  | CMul a a a
  deriving Functor

data Circom = MkCircom
  { signals     :: [Name]
  , output      :: [Name]
  , constraints :: [Constraint Linear]
  }

data CircomInput = MkCircomInput [(Name, F)]

type CircuitName = String
type Proof = String
type OutputWithProof = ([F], Proof)


----------------------------------------------------------------

instance Show Linear where
  show (MkLinear c s) = intercalate " + " (show c: map f s)  where
    f (c, n) = show c ++ "*" ++ n

instance Show a => Show (Constraint a) where
  show (CEq a b) = "  " ++ show a ++ " === " ++ show b ++ ";"
  show (CMul a b c) = "  (" ++ show a ++ ")*(" ++ show b ++ ") === " ++ show c ++ ";"

instance Show Circom where
  show (MkCircom ss ns c) = unlines $
    "pragma circom 2.0.4;" : "" :
    "template zkf() {" :
      map renderInput ss ++ "" :
      map show c ++
    "}" : "" :
    ("component main {public [" ++ intercalate ", " ns ++ "]} = zkf();") :
    []
   where
    renderInput n = "  signal input " ++ n ++ ";"

instance Show CircomInput where
  show (MkCircomInput is) = "{ " <> intercalate ", " [show n <> ": " <> show (show i) | (n, i) <- is] <> " }"

readProcess' name args = do
  putStrLn $ unwords $ name: args
  (exitCode, out, err) <- readProcessWithExitCode name args ""
  case exitCode of
    ExitSuccess -> pure ()
    x -> error $ unlines [show x, out, err]

ptau = "powersOfTau28_hez_final_22.ptau"

----------------------------------------------------------------

publishCircom :: CircuitName -> Circom -> IO ()
publishCircom fn circuit = do
  writeFile (fn <> ".circom") $ show circuit
  readProcess' "circom" [fn <> ".circom", "--r1cs", "--json", "--wasm", "--c"]
  readCreateProcess ((proc "make" []) { cwd = Just $ fn <> "_cpp"}) "" >>= putStrLn
  readProcess' "snarkjs" ["groth16", "setup", fn <> ".r1cs", ptau, fn <> ".pk"]
  readProcess' "snarkjs" ["zkey", "export", "verificationkey", fn <> ".pk", fn <> ".vk"]

runCircom :: CircuitName -> CircomInput -> IO OutputWithProof
runCircom fn inp = do
--  c2 <- readFile (fn <> ".circom")
--  if c2 /= show circuit then error "unpublished circuit, run publishCircom and re-enter ghci" else do
    writeFile (fn <> ".input.json") $ show inp
    readProcess' ("./" <> fn <> "_cpp/" <> fn) [fn <> ".input.json", fn <> ".wtns"]
--    readProcess' "node" [fn <> "_js/generate_witness.js", fn <> "_js/" <> fn <> ".wasm", fn <> ".input.json", fn <> ".wtns"]
    home <- getHomeDirectory
    readProcess' (home <> "/share/rapidsnark" <> "/package/bin/prover") [fn <> ".pk", fn <> ".wtns", fn <> ".pf.json", fn <> ".inst.json"]
--    readProcess' "snarkjs" ["groth16", "prove", fn <> ".pk", fn <> ".wtns", fn <> ".pf.json", fn <> ".inst.json"]
    res <- readFile (fn <> ".inst.json") <&> unjson
    prf <- readFile (fn <> ".pf.json") -- <&> unjson
    pure (res, prf)
 where
  unjson = map (MkF . read) . words . map repl where
    repl c | isDigit c = c
           | otherwise = ' '

verifyCircom :: CircuitName -> OutputWithProof -> IO Bool
verifyCircom fn (res, prf) = do
  _ <- writeFile (fn' <> ".inst.json") $ "[" <> intercalate "," (map (show . show) res) <> "]"
  _ <- writeFile (fn' <> ".pf.json") prf
  (exitCode, _, _) <- readProcessWithExitCode "snarkjs" ["groth16", "verify", fn <> ".vk", fn' <> ".inst.json", fn' <> ".pf.json"] ""
  pure $ exitCode == ExitSuccess
 where
  fn' = fn <> "1"

