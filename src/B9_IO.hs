module B9_IO
  ( IO
  , runRefM, runIO
  , fail, catchErrors
  , putStr, presentationMode, getKey, askYN, getTerminalSize, clearScreen, setCursorPosition, cursorForward
  
  , FilePath, (</>)
  , parseFile, printFile, getTemporaryDir, parseDataFile
  
  , versionString
  , CLI (Files), command, runCLI
  )
 where

import B0_Builtins
import B1_Basic
import B2_String
import B3_RefM
import B4_Partial

-----------------------------------------------

data IO a = MkIO ((a -> Prog) -> Prog)

unIO (MkIO f) = f

instance Functor IO where
  f <$> MkIO h = MkIO \g -> h (g . f)

instance Applicative IO where
  pure a = MkIO \g -> g a
  MkIO f <*> MkIO h = MkIO \g -> f \f -> h (g . f)

instance Monad IO where
  MkIO f >>= h = MkIO \g -> f \f -> unIO (h f) g

instance MonadFail IO where
  fail s = runRefM $ fail s

catchErrors :: (MainException -> IO a) -> IO a -> IO a
catchErrors a (MkIO h) = MkIO \g -> case mainException of
  MkExcept w -> CatchError w (\e -> unIO (a e)) h g


runRefM :: RefM a -> IO a
runRefM m = MkIO \end -> Do m end

runIO m = runProg $ unIO
  (catchErrors (\e -> runRefM (print e) >>= die . appendLoc) m)
  \_ -> ProgEnd


-----------------------------------------------

type FilePath = String

(</>) :: FilePath -> FilePath -> FilePath
"" </> b = b
a </> b | lastStr a == '/' = a <> b
a </> b = a <> "/" <> b


-----------------------------------------------

die                        f = MkIO \_   -> Die (toPreludeString f)
getArgs                      = MkIO \end -> GetArgs \r -> end (map fromString $ foldrPrelude (:.) Nil r)
getTemporaryDir              = MkIO \end -> GetTemporaryDir \f -> end (fromString f)
presentationMode (MkIO m)    = MkIO \end -> PresentationMode (lazy (m \_ -> ProgEnd)) (lazy (end T0))
getTerminalSize              = MkIO \end -> GetTerminalSize (lazy (end (T2 119 131))) \w h -> end (T2 w h)

-----------------------------------------------

parseFile :: Parse a => FilePath -> FilePath -> IO (Maybe a)
parseFile dir f = MkIO \end ->
  ReadFile (toPreludeString $ dir </> f) (lazy (end Nothing)) \s ->
  Do (mkLocString f $ fromPreludeString s) (end . Just)

parseDataFile :: Parse a => FilePath -> RefM a
parseDataFile f = do
  dir <- fromString <$> getDataDirRaw
  readFileRaw (toPreludeString $ dir </> f) >>= \s -> mkLocString f (fromPreludeString s)

printFile :: Print a => FilePath -> a -> IO Tup0
printFile f a = do
  s <- runRefM $ print a
  MkIO \end -> WriteFile (toPreludeString f) (toPreludeString s) (lazy (end T0))

putStr :: String -> IO Tup0
putStr s = MkIO \end -> PutStr (toPreludeString (fixANSI s)) (lazy (end T0))

getChar :: IO Char
getChar = MkIO GetChar

askYN s = do
  putStr $ s <> " (Y/N)? "
  c <- getChar
  putStr "\n"
  case c of
    'y' -> pure True
    'n' -> pure False
    _ -> askYN s

getKey :: IO String
getKey = getChar >>= \case
  '\DEL' -> pure "Backspace"
  '\ESC' -> getChar >>= \case
    '[' -> getArgs >>= \case
      T2 (('1' :. Nil) :. _a) '~' -> pure "Home"
      T2 (('2' :. Nil) :. _a) '~' -> pure "Ins"
      T2 (('3' :. Nil) :. _a) '~' -> pure "Del"
      T2 (('4' :. Nil) :. _a) '~' -> pure "End"
      T2 (('5' :. Nil) :. _a) '~' -> pure "PageUp"
      T2 (('6' :. Nil) :. _a) '~' -> pure "PageDown"
      T2 _ 'A' -> pure "Up"
      T2 _ 'B' -> pure "Down"
      T2 _ 'C' -> pure "Right"
      T2 _ 'D' -> pure "Left"
      _ -> getKey
    _ -> pure "Esc"
  c -> pure $ takeStr 1 $ dropStr (charToWord c -. 32)
    " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~"
 where
  getArgs = first (reverse . map reverse) <$> f Nil Nil
  f i is = getChar >>= \case
    ';' -> f Nil (i:. is)
    c | isDigit c -> f (c:. i) is
    c -> pure (T2 (i:. is) c)


--------------------------------

clearScreen           = "\ESC[2J"
cursorForward n       = "\ESC[" <> showWord n <> "C"
setCursorPosition n m = "\ESC[" <> showWord (n + 1) <> ";" <> showWord (m + 1) <> "H"

versionString :: String
versionString = "1"


-------------------------------- command line interface

data CLI
  = Commands (List (Tup3 String String CLI)) CLI
  | Files (List String -> IO Tup0)
  | CEmpty

command :: String -> String -> CLI -> CLI
command a b c = Commands (T3 a b c :. Nil) CEmpty

instance Semigroup CLI where
  CEmpty <> b = b
  Commands as CEmpty <> Commands bs c = Commands (as <> bs) c
  Commands as CEmpty <> c = Commands as c
  a <> _ = a

runCLI :: String -> CLI -> IO Tup0
runCLI progname x = getArgs >>= eval Nil x
 where
  eval hs x (s:. _) | s == "-h" || s == "--help" = printHelp hs (usage x)
  eval hs (Commands ps _) (s:. ss)
    | Just (T2 h x) <- lookupList s (ps <&> \(T3 a h c) -> T2 a (T2 h c)) = eval (h:. hs) x ss
  eval hs (Commands _ p) ss = eval hs p ss
  eval _ (Files io) s = io s
  eval _ _ _ = putStr $ unlines $ "Usage:" :. "" :. (usage x <&> \h -> "  " <> progname <> h)

  usage = \case
    Files _ -> " FILE..." :. Nil
    Commands ps p -> (do (T3 a _b c) <- ps; r <- usage c; pure (" " <> a <> r)) <> usage p
    CEmpty -> Nil

  printHelp :: List String -> List String -> IO Tup0
  printHelp a hs = putStr $ unlines $ a <> case hs of
    hs | all nullStr hs -> Nil
    _  -> "" :. "Options:" :. hs

