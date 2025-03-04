import M1_Base
import M3_Parse
import M4_Eval
import M6_Elab
import M7_Stage
import M8_IO

----------------------------

getTmpDir = do
  d <- getTemporaryDirectory <&> (</> "csip")
  createDirectoryIfMissing True d
  pure d

----------------------------

getCmd :: Source -> RefM ([[Source]], Source)
getCmd = \case
  Cons "#" (Cons " " (spanCh (/= '\n') -> (cmd, Cons "\n" s))) -> do
    cmd <- parse cmd >>= f
    (cmds, s) <- getCmd s
    pure (cmd: cmds, s)
  s -> pure ([], s)
 where
  f :: Raw -> RefM [Source]
  f (a :@ b) = print b >>= \b -> f a <&> \as -> as <> [b]
  f n = print n <&> (:[])

getSource f = parseFile' "" f >>= \case
  Nothing -> pure Nothing
  Just s -> Just . first maybeElab <$> getCmd s
 where
  maybeElab [] = [["elab"]]
  maybeElab cmds = cmds


showCmd :: [Source] -> String
showCmd = concat . intersperse " " . map chars

doCmds :: [Source] -> Source -> RefM String
doCmds cmd s = do
 () <- reset
 catchError mainException (\e -> show <$> print e) $ case cmd of
  [cmd]                       -> doCmd False cmd s <&> chars
  [cmd, "highlight"]          -> doCmd False cmd s <&> show
  [cmd, "quote"]              -> doCmd True  cmd s <&> chars
  [cmd, "quote", "highlight"] -> doCmd True  cmd s <&> show
  cmds ->  error $ "Unknown commands: " <> mconcat (intersperse " " cmds)
 where
  doCmd :: Bool -> Source -> Source -> RefM Source
  doCmd quote cmd s = case cmd of
    "source"    -> sh =<< (parse s :: RefM Source)
    "indent"    -> sh =<< (parse s :: RefM ISource)
    "lex"       -> sh =<< (parse s :: RefM [Token Spaced])
    "structure" -> sh =<< (parse s :: RefM (OpSeq' Spaced))
    "string"    -> sh =<< (parse s :: RefM (OpSeq' Stringed))
    "comment"   -> sh =<< (parse s :: RefM (OpSeq' Uncomment))
    "comments"  -> sh =<< (parse s :: RefM (OpSeq' Uncomments))
    "space"     -> sh =<< (parse s :: RefM (OpSeq' Unspaced))
    "layout"    -> sh =<< (parse s :: RefM (OpSeq' Layout))
    "op"        -> sh =<< (parse s :: RefM (ExpTree' Layout))
    "exptree"   -> sh =<< (parse s :: RefM (ExpTree' POp))
    "sugar"     -> sh =<< (parse s :: RefM (ExpTree' Desug))
    "scope"     -> sh =<< (parse s :: RefM Raw)
    "elab"      -> sh =<< (parse s :: RefM Tm)
    "eval"      -> sh =<< ((parse s :: RefM Tm) >>= evalClosed >>= quoteNF <&> fst)
    "type"      -> sh =<< (parse s >>= inferTop <&> snd >>= quoteNF')
    "evalquote" -> sh =<< ((parse s :: RefM Tm) >>= evalClosed >>= quoteNF')
    "stage"     -> sh =<< ((parse s :: RefM Tm) >>= evalClosed >>= stage)
    "haskell_stage"
                -> sh =<< ((parse s :: RefM Tm) >>= evalClosed >>= stageHaskell)
    _ -> error $ "Unknown command: " <> cmd
   where
    sh = if quote then sh' else print

  sh' :: (PPrint a) => a -> RefM Source
  sh' m = print $ pprint m


----------------------------

listDirRec f = doesDirectoryExist f >>= \case
  True -> listDirectory f >>= mapM (listDirRec . (f </>)) <&> concat
  False -> pure [f]

testNames dir = do
  ns <- listDirRec dir <&> \fs -> sort [f | f <- fs, Just _ <- [stripSuffix ".csip" f]]
  if null ns then error $ "no .csip files found at " <> fromString dir
    else pure ns


getResult odir fn s cmd _i n = do
  r <- parseFile' odir out
  pure (printFile' (odir </> out), r)
 where out = hashString $ "# " <> showCmd cmd <> " # " <> fn <> " # " <> show n <> " # " <> versionString <> "\n" <> chars s

getResult' odir fn s cmd i n = do
  (printres, r) <- getResult odir fn s cmd i n
  maybe (doCmds cmd s >>= \r -> printres r >> pure r) pure r

parseFile' dir f | fn <- dir </> f = doesFileExist fn >>= \case
  False -> pure Nothing
  True  -> parseFile dir f <&> Just

printFile' f s = do
  createDirectoryIfMissing True (directory f)
  printFile f s

directory f = case dropWhile (/= '/') $ reverse f of
  '/': bs -> reverse bs
  _ -> ""


tests accept dir = do
  odir <- getTmpDir
  testFiles accept dir odir

testFiles accept dir odir = do
 fs <- testNames dir
 forM_ fs \fn -> do
  Just (cmds, s) <- getSource fn
  forM_ (zip [0 :: Int ..] cmds) \(i, cmd) -> do
    if accept then do
      r <- getResult' odir fn s cmd i (length cmds)
      putStr
           $ invert (foreground cyan $ "           " <> showCmd cmd <> " " <> fn <> "           ") <> "\n"
          <> r <> "\n"
     else do
      (printres, r2) <- getResult odir fn s cmd i (length cmds)
      r <- doCmds cmd s
      when (r2 /= Just r) do
        putStr
           $ maybe "" (\r -> 
             invert (foreground cyan $ "   old     " <> showCmd cmd <> " " <> fn <> "           ") <> "\n"
          <> r <> "\n") r2
          <> invert (foreground cyan $ "   new     " <> showCmd cmd <> " " <> fn <> "           ") <> "\n"
          <> r <> "\n"
          <> maybe "" (\r' -> if lines r' /= lines r then
               invert (foreground red $ "    first diff    ")
            <> ["\n" <> a <> "\n" <> b <> "\n" | (a, b) <- zip (lines r' ++ repeat "") (lines r ++ repeat ""), a /= b] !! 0
            else "") r2
        askYN "accept" >>= \b -> if b then printres r else pure ()

present dir odir beg = do
  fs <- testNames dir
  let
   l = length fs
   f i = do
    let fn = fs !! i
        reload  = present dir odir fn
    getSource fn >>= \case
     Nothing -> reload
     Just (cmds, s) -> do

      rs <- forM (zip [0 :: Int ..] cmds) \(j, cmd) -> do
          r <- getResult' odir fn s cmd j (length cmds)
          pure (showCmd cmd <> " " <> fn, r)
      let
        g = do
          let
            nextF   = [f (i+1) | i+1 < l]
            prevF   = [f (i-1) | i > 0]
            end     = [pure ()]
            wait k  = listToMaybe $ case k of
              " "         -> nextF
              "\n"        -> nextF
              "Backspace" -> prevF
              "Left"      -> prevF
              "Right"     -> nextF
              "Esc"       -> end
              "q"         -> end
              "r"         -> [reload]
              _           -> []

          (w, h) <- getTerminalSize
          disp h (mkScreen True (w, h) cyan rs) wait
      g

  presentationMode $ f $ min (length fs - 1) $ length $ filter (< beg) fs

export dir odir = do
  (w, h) <- getTerminalSize
  fs <- testNames dir
  rs <- forM fs \fn -> do
    Just (cmds, s) <- getSource fn
    rs <- forM (zip [0 :: Int ..] cmds) \(j, cmd) -> do
      r <- getResult' odir fn s cmd j (length cmds)
      pure (showCmd cmd <> " " <> fn, r)
    pure $ mkScreen False (w, h) cyan rs
  pure (concat $ map (<>"\n") $ concat $ rs :: String)

distribute :: Int -> Int -> [Int]
distribute parts i = zipWith (-) is (0:is) where
  is = [(j * i - 1) `div` parts + 1 | j <- [1..parts]]

mkScreen :: Bool -> (Int, Int) -> Int -> [(String, String)] -> [String]
mkScreen rich (w, h) color ts
  = concat
    [ t: replicate o1 "" ++ ls ++ replicate o2 ""
    | (o, t: ls) <- zip os tls
    , let o1 = o `div` 2
    , let o2 = o - o1
    ]
 where
  mh = sum $ map length tls
  os = distribute (length tls) $ max 0 $ h - mh
  tls = map f ts

  f (title, s) =
    (if rich then invert . foreground color $ replicate t1 ' ' <> title <> replicate t2 ' '
             else replicate t1 '=' <> title <> replicate t2 '=')
    : [(if rich then cursorForward ow else replicate ow ' ') <> s | s <- ls]
   where
    ls = lines s
    mw = maximum (0: map lengthANSI ls)
    ow = max 0 $ (w - mw) `div` 2
    t1 = max 0 $ (w - length title) `div` 2
    t2 = max 0 $ w - t1 - length title

disp :: Int -> [String] -> (String -> Maybe (IO ())) -> IO ()
disp h ls' cont = wait 0
   where
    mz = max 0 $ length ls' - h
    wait z = do
      putStr
        $  clearScreen
        <> mconcat [setCursorPosition i 0 <> l | (i, l) <- zip [0..h-1] $ drop z ls']
      getKey >>= \case
        "Up"       | z > 0  -> wait (z-1)
        "Down"     | z < mz -> wait (z+1)
        "PageUp"   | z > 0  -> wait $ max 0  $ z - h
        "PageDown" | z < mz -> wait $ min mz $ z + h
        s -> maybe (wait z) id $ cont s

----------------------------

main = runCLI "csip"
   $ command "show"    "present files"           (Dir \dir -> getTmpDir >>= \odir -> present dir odir "")
  <> command "export"  "export presentation"     (Dir \dir -> getTmpDir >>= \odir -> export dir odir >>= putStr)
  <> command "diff"    "compare compiled output" (Dir $ tests False)
  <> command "clean"   "clean cache"             (Pure $ getTmpDir >>= removeDirectoryRecursive)
  <> Dir (tests True)

