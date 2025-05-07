module M8_IO
  ( getTerminalSize
  , getKey
  , askYN
  , presentationMode
  , putStr
  , flushStdout
  , (</>), directory
  , parseFile
  , printFile
  , CLI (Dir, Pure), command, runCLI
  , hashString
  , versionString
  , IO, FilePath
  , doesFileExist, doesDirectoryExist, getDataDir, getDataFileName, getTemporaryDirectory
  , listDirectory, createDirectoryIfMissing, removeDirectoryRecursive
  , clearScreen, setCursorPosition, setCursorHPosition, cursorUp, cursorDown, cursorForward, cursorBack
  , showCursor, hideCursor
  )
 where

import qualified A_Builtins as B
import A_Builtins hiding
  ( String, FilePath, doesFileExist, doesDirectoryExist, getDataDir, getDataFileName
  , getTemporaryDirectory, listDirectory, createDirectoryIfMissing, removeDirectoryRecursive
  , readFile, writeFile, stringToList
  )
import D_Base

-----------------------------------------------

type FilePath = String

doesFileExist = B.doesFileExist . fromString'
doesDirectoryExist = B.doesDirectoryExist . fromString'
getDataDir = fmap mkString B.getDataDir
getDataFileName = fmap mkString . B.getDataFileName . fromString'
getTemporaryDirectory = fmap mkString B.getTemporaryDirectory
listDirectory = fmap (map mkString) . B.listDirectory . fromString'
createDirectoryIfMissing b = B.createDirectoryIfMissing b . fromString'
removeDirectoryRecursive = B.removeDirectoryRecursive . fromString'
writeFile f s = B.writeFile (fromString' f) s

-----------------------------------------------

hashString :: String -> String
hashString = mconcat . map (charStr . char) . base 22 64 . hash . stringToList
 where
  hash :: List Char -> Word128
  hash = foldl (\h c -> 33 * h + wordToWord128 (ord c)) 5381   -- djb2

  base :: Word -> Word128 -> Word128 -> List Word
  base 0 _ _ = Nil
  base n b i = word128ToWord (mod i b):. base (n-.1) b (div i b)

  char i
    | i < 26 = chr $ i       + ord 'A'
    | i < 52 = chr $ i -. 26 + ord 'a'
    | i < 62 = chr $ i -. 52 + ord '0'
    | i == 62 = '-'
    | i == 63 = '_'
  char _ = impossible

-----------------------------------------------

(</>) :: FilePath -> FilePath -> FilePath
"" </> b = b
a </> b | lastStr a == '/' = a <> b
a </> b = a <> "/" <> b

directory = revDropStr 1 . fst . revSpanStr (/= '/')

parseFile :: (Parse a) => FilePath -> FilePath -> IO a
parseFile dir f = do
  s <- B.readFile (fromString' $ dir </> f)
  mkLocString f s

printFile :: (Print a) => FilePath -> a -> IO Tup0
printFile f a =
  writeFile f . fromString' =<< print a

putStr :: String -> IO Tup0
putStr s = mapM_ putChar (stringToList (fixANSI s)) >> flushStdout

flushStdout   :: IO Tup0
flushStdout   = hFlush stdout

askYN s = do
  putStr $ s <> " (Y/N)? "
  c <- getChar
  putStr "\n"
  case c of
    'y' -> pure True
    'n' -> pure False
    _ -> askYN s


runIO m = do
  hSetBuffering stdin noBuffering
  hSetBuffering stdout lineBuffering
  T0 <- reset
  catchError mainException (\e -> print e >>= die . fromString' . appendLoc) m

csi0 :: String -> String
csi0 code = "\ESC[" <> code

csi1 :: Word ->  String -> String
csi1 a code = "\ESC[" <> fromString' (showInt a) <> code

csi2 :: Word -> Word -> String -> String
csi2 a b code = "\ESC[" <> fromString' (showInt a) <> ";" <> fromString' (showInt b) <> code

clearScreen = csi1 2 "J"
setCursorHPosition n = csi1 (n + 1) "G"
setCursorPosition n m = csi2 (n + 1) (m + 1) "H"
cursorUp      n = csi1 n "A"
cursorDown    n = csi1 n "B"
cursorForward n = csi1 n "C"
cursorBack    n = csi1 n "D"

hideCursor = csi0 "?25l"
showCursor = csi0 "?25h"

presentationMode m = do
  putStr
    $  hideCursor
    <> "\ESC[?2004h"  -- turn on bracketed paste mode
    <> "\ESC[?1049h"  -- enable alternative screen buffer
    <> "\ESC[?7l"     -- turn line wrap off -- setterm -linewrap off
  hSetEcho stdin False
  m
 `finally` do
  hSetEcho stdin True
  putStr
    $  "\ESC[?7h"
    <> "\ESC[?1049l"
    <> "\ESC[?2004l"
    <> showCursor

defaultTerminalSize :: Tup2 Word Word
defaultTerminalSize = T2 119 31

getTerminalSize :: IO (Tup2 Word Word)
getTerminalSize = fromMaybe defaultTerminalSize <$> do
  b <- hIsTerminalDevice stdout
  if b then do
    putStr $ "\ESC7" -- save cursor
        <> setCursorPosition 9999 9999
    clearStdin
    putStr $ csi1 6 "n"
    hFlush stdout
    skip ('\ESC' :. '[' :. Nil)
    as <- getInt 0 ';'
    bs <- getInt 0 'R'
    putStr "\ESC8" -- restore cursor
    hFlush stdout
    pure $ T2 <$> bs <*> as
   else pure Nothing
 where
  clearStdin = do
    isReady <- hReady stdin
    when isReady $ do
      _ <- getChar
      clearStdin

  skip Nil = pure T0
  skip (c:. cs) = getChar >>= \c' -> if c' == c then skip cs else undefined

  getInt acc end = getChar >>= \c -> case c of
    c | c == end -> pure $ Just acc
    c | isDigit c -> getInt (10 * acc + digitToInt c) end
    _ -> pure Nothing


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
  c -> pure (charStr c)
 where
  getArgs = first (reverse . map reverse) <$> f Nil Nil
  f i is = getChar >>= \case
    ';' -> f Nil (i:. is)
    c | isDigit c -> f (c:. i) is
    c -> pure (T2 (i:. is) c)

versionString :: String
versionString = (mconcat . intersperse "." . map showInt) versionBranch

-------------------------------- command line interface

data CLI
  = Commands (List (Tup3 String String CLI)) CLI
  | Dir (String -> IO Tup0)
  | Pure (IO Tup0)
  | CEmpty

command :: String -> String -> CLI -> CLI
command a b c = Commands (T3 a b c :. Nil) CEmpty

instance Semigroup CLI where
  CEmpty <> b = b
  Commands as CEmpty <> Commands bs c = Commands (as <> bs) c
  Commands as CEmpty <> c = Commands as c
  a <> _ = a

runCLI :: String -> CLI -> IO Tup0
runCLI progname x = runIO (getArgs >>= eval Nil x . map mkString)
 where
  eval :: List String -> CLI -> List String -> IO Tup0
  eval hs x (s:. _) | s == "-h" || s == "--help" = printHelp hs (usage x)
  eval hs (Commands ps _) (s:. ss)
    | Just (T2 h x) <- lookupList s (ps <&> \(T3 a h c) -> T2 a (T2 h c)) = eval (h:. hs) x ss
  eval hs (Commands _ p) ss = eval hs p ss
  eval _ (Dir io) (s :. Nil) = io $ fromString' s
  eval _ (Pure io) Nil = io
  eval _ _ _ = putStr $ unlines $ "Usage:" :. "" :. (usage x <&> \h -> "  " <> progname <> h)

  usage = \case
    Dir _ -> " FILE|DIR" :. Nil
    Pure _ -> "" :. Nil
    Commands ps p -> (do (T3 a _b c) <- ps; r <- usage c; pure (" " <> a <> r)) <> usage p
    CEmpty -> Nil

  printHelp :: List String -> List String -> IO Tup0
  printHelp a hs = putStr $ unlines $ a <> case hs of
    hs | all nullStr hs -> Nil
    _  -> "" :. "Options:" :. hs

