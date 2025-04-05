module M8_IO
  ( getTerminalSize
  , getKey
  , askYN
  , presentationMode
  , putStr
  , flushStdout
  , (</>)
  , parseFile
  , printFile
  , CLI (Dir, Pure), command, runCLI
  , hashString
  , versionString
  , IO, FilePath, readFile, writeFile, getChar, putChar
  , doesFileExist, doesDirectoryExist, getTemporaryDirectory
  , listDirectory, createDirectoryIfMissing, removeDirectoryRecursive
  )
 where

import B_Prelude

-----------------------------------------------

hashString :: String -> String
hashString = map char . base 22 64 . hash
 where
  hash :: String -> Word128
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
a </> b | last a == '/' = a <> b
a </> b = a <> "/" <> b

parseFile :: (Parse a) => FilePath -> FilePath -> IO a
parseFile dir f = do
  s <- readFile (dir </> f)
  source f s

printFile :: (Print a) => FilePath -> a -> IO ()
printFile f a =
  writeFile f . chars =<< print a

putStr :: String -> IO ()
putStr s = mapM_ putChar (fixANSI s) >> flushStdout

flushStdout   :: IO ()
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
  () <- reset
  catchError mainException (\e -> print e >>= die . showSource) m

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

defaultTerminalSize :: (Word, Word)
defaultTerminalSize = (119, 31)

getTerminalSize :: IO (Word, Word)
getTerminalSize = fromMaybe defaultTerminalSize <$> do
  b <- hIsTerminalDevice stdout
  if b then do
    putStr $ "\ESC7" -- save cursor
        <> setCursorPosition 9999 9999
    clearStdin
    putStr $ CSI [6] 'n' ""
    hFlush stdout
    skip "\ESC["
    as <- getInt 0 ';'
    bs <- getInt 0 'R'
    putStr "\ESC8" -- restore cursor
    hFlush stdout
    pure $ (,) <$> bs <*> as
   else pure Nothing
 where
  clearStdin = do
    isReady <- hReady stdin
    when isReady $ do
      _ <- getChar
      clearStdin

  skip Nil = pure ()
  skip (c:. cs) = getChar >>= \c' -> if c' == c then skip cs else undefined

  getInt acc end = getChar >>= \c -> case c of
    c | c == end -> pure $ Just acc
    c | isDigit c -> getInt (10 * acc + digitToInt c) end
    _ -> pure Nothing


getKey = getChar >>= \case
  '\DEL' -> pure "Backspace"
  '\ESC' -> getChar >>= \case
    '[' -> getArgs >>= \case
      ("1":. _a, '~') -> pure "Home"
      ("2":. _a, '~') -> pure "Ins"
      ("3":. _a, '~') -> pure "Del"
      ("4":. _a, '~') -> pure "End"
      ("5":. _a, '~') -> pure "PageUp"
      ("6":. _a, '~') -> pure "PageDown"
      (_, 'A') -> pure "Up"
      (_, 'B') -> pure "Down"
      (_, 'C') -> pure "Right"
      (_, 'D') -> pure "Left"
      _ -> getKey
    _ -> pure "Esc"
  c -> pure [c]
 where
  getArgs = first (reverse . map reverse) <$> f "" Nil
  f i is = getChar >>= \case
    ';' -> f "" (i:. is)
    c | isDigit c -> f (c:. i) is
    c -> pure (i:. is, c)

versionString :: String
versionString = intercalate "." $ map showInt versionBranch

-------------------------------- command line interface

data CLI
  = Commands (List (String, String, CLI)) CLI
  | Dir (String -> IO ())
  | Pure (IO ())
  | CEmpty

command :: String -> String -> CLI -> CLI
command a b c = Commands [(a, b, c)] CEmpty

instance Semigroup CLI where
  CEmpty <> b = b
  Commands as CEmpty <> Commands bs c = Commands (as <> bs) c
  Commands as CEmpty <> c = Commands as c
  a <> _ = a

runCLI :: String -> CLI -> IO ()
runCLI progname x = runIO (getArgs >>= eval Nil x)
 where
  eval hs x (s:. _) | s == "-h" || s == "--help" = printHelp hs (usage x)
  eval hs (Commands ps _) (s:. ss)
    | Just (h, x) <- lookupList s (ps <&> \(a, h, c) -> (a, (h, c))) = eval (h:. hs) x ss
  eval hs (Commands _ p) ss = eval hs p ss
  eval _ (Dir io) [s] = io s
  eval _ (Pure io) Nil = io
  eval _ _ _ = putStr $ unlines $ ["Usage:", ""] ++ (usage x <&> \h -> "  " ++ progname ++ h)

  usage = \case
    Dir _ -> [" FILE|DIR"]
    Pure _ -> [""]
    Commands ps p -> (do (a, _b, c) <- ps; r <- usage c; pure (" " <> a <> r)) ++ usage p
    CEmpty -> Nil

  printHelp a hs = putStr $ unlines $ a ++ case hs of
    hs | all null hs -> Nil
    _  -> ["", "Options:"] ++ hs

