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

getCmd :: Source -> RefM (List (List Source), Source)
getCmd = \case
  Cons' '#' (Cons' ' ' (spanCh (/= '\n') -> (cmd, Cons' '\n' s))) -> do
    cmd <- parse cmd >>= f
    (cmds, s) <- getCmd s
    pure (cmd:. cmds, s)
  s -> pure (Nil, s)
 where
  f :: Raw -> RefM (List Source)
  f (a :@ b) = print b >>= \b -> f a <&> \as -> as <> [b]
  f n = print n <&> (:.Nil)

getSource f = parseFile' "" f >>= \case
  Nothing -> pure Nothing
  Just s -> Just . first maybeElab <$> getCmd s
 where
  maybeElab Nil = [["elab"]]
  maybeElab cmds = cmds


showCmd :: List Source -> String
showCmd = concat . intersperse " " . map chars

doCmds :: List Source -> Source -> RefM String
doCmds cmd s = do
 () <- reset
 catchError mainException (\e -> showSource <$> print e) (doCmds_ cmd s)

doCmds_ :: List Source -> Source -> RefM String
doCmds_ cmd s = case cmd of
  [cmd]                       -> doCmd False cmd s <&> chars
  [cmd, chars -> "highlight"]          -> doCmd False cmd s <&> showSource
  [cmd, chars -> "quote"]              -> doCmd True  cmd s <&> chars
  [cmd, chars -> "quote", chars -> "highlight"] -> doCmd True  cmd s <&> showSource
  cmds ->  error $ "Unknown commands: " <> mconcat (intersperse " " cmds)
 where
  doCmd :: Bool -> Source -> Source -> RefM Source
  doCmd quote cmd s = case chars cmd of
    "source"    -> sh =<< (parse s :: RefM Source)
    "indent"    -> sh =<< (parse s :: RefM ISource)
    "lex"       -> sh =<< (parse s :: RefM (List (Token Spaced)))
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
    "eval"      -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= quoteNF <&> fst)
    "type"      -> sh =<< (parse s >>= inferTop <&> snd >>= quoteNF')
    "evalquote" -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= quoteNF')
    "stage"     -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= stage)
    "haskell_stage"
                -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= stageHaskell)
    _ -> error ("Unknown command: " <> cmd)
   where
    sh :: (PPrint a, Print a) => a -> RefM Source
    sh x = if quote then sh' x else print x

  sh' :: PPrint a => a -> RefM Source
  sh' m = print (pprint m)


----------------------------

listDirRec f = doesDirectoryExist f >>= \case
  True -> listDirectory f >>= mapM (listDirRec . (f </>)) <&> concat
  False -> pure [f]

testNames dir = do
  ns <- listDirRec dir <&> \fs -> sort (filter (isJust . stripSuffix ".csip") fs)
  if null ns then error $ "no .csip files found at " <> stringToSource dir
    else pure ns


getResult odir fn s cmd _i n = do
  r <- parseFile' odir out
  pure (printFile' (odir </> out), r)
 where out = hashString $ "# " <> showCmd cmd <> " # " <> fn <> " # " <> showInt n <> " # " <> versionString <> "\n" <> chars s

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
  '/':. bs -> reverse bs
  _ -> ""


tests accept dir = do
  odir <- getTmpDir
  testFiles accept dir odir

testFiles accept dir odir = do
 fs <- testNames dir
 forM_ fs \fn -> do
  Just (cmds, s) <- getSource fn
  forM_ (numberWith (,) 0 cmds) \(i, cmd) -> do
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
            <> (do (a, b) <- repNl (lines r') (lines r); guard (a /= b); pure ("\n" <> a <> "\n" <> b <> "\n")) !! 0
            else "") r2
        askYN "accept" >>= \b -> if b then printres r else pure ()

repNl as bs = zip (as ++ replicate (c-.a) "") (bs ++ replicate (c-.b) "")
 where
  a = length as; b = length bs; c = a + b

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

      rs <- forM (numberWith (,) 0 cmds) \(j, cmd) -> do
          r <- getResult' odir fn s cmd j (length cmds)
          pure (showCmd cmd <> " " <> fn, r)
      let
        g = do
          let
            nextF   = maybeList (f (i+1)) (i+1 < l) Nil
            prevF   = maybeList (f (i-.1)) (i > 0) Nil
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
              _           -> Nil

          (w, h) <- getTerminalSize
          disp h (mkScreen True (w, h) cyan rs) wait
      g

  presentationMode $ f $ min (length fs -. 1) $ length $ filter (< beg) fs

export dir odir = do
  wh <- getTerminalSize
  fs <- testNames dir
  rs <- forM fs \fn -> do
    Just (cmds, s) <- getSource fn
    rs <- forM (numberWith (,) 0 cmds) \(j, cmd) -> do
      r <- getResult' odir fn s cmd j (length cmds)
      pure (showCmd cmd <> " " <> fn, r)
    pure $ mkScreen False wh cyan rs
  pure (concat $ map (<>"\n") $ concat $ rs :: String)

distribute :: Word -> Word -> List Word
distribute ((+1) -> parts) i = zipWith (-.) is (0:.is) where
  is = enumFromTo 1 parts <&> \j -> (j * i -. 1) `div` parts

mkScreen :: Bool -> (Word, Word) -> Word -> List (String, String) -> List String
mkScreen rich (w, h) color ts
  = concat $ zip os tls <&> \case
    (o, t:. ls) ->
      let o1 = o `div` 2 in
      let o2 = o -. o1   in
         t:. replicate o1 "" ++ ls ++ replicate o2 ""
    _ -> impossible
 where
  mh = sum $ map length tls
  os = distribute (length tls) $ h -. mh
  tls = map f ts

  f (title, s) =
    (if rich then invert . foreground color $ replicate t1 ' ' <> title <> replicate t2 ' '
             else replicate t1 '=' <> title <> replicate t2 '=')
    :. (ls <&> \s -> (if rich then cursorForward ow else replicate ow ' ') <> s)
   where
    ls = lines s
    mw = maximum (0:. map lengthANSI ls)
    ow = (w -. mw) `div` 2
    t1 = (w -. length title) `div` 2
    t2 = w -. t1 -. length title

disp :: Word -> List String -> (String -> Maybe (IO ())) -> IO ()
disp h ls' cont = wait 0
   where
    mz = length ls' -. h
    wait z = do
      putStr
        $  clearScreen
        <> mconcat (zip (enumFromTo 0 h) (drop z ls') <&> \(i, l) -> setCursorPosition i 0 <> l)
      getKey >>= \case
        "Up"       | z > 0  -> wait (z-.1)
        "Down"     | z < mz -> wait (z+1)
        "PageUp"   | z > 0  -> wait $ z -. h
        "PageDown" | z < mz -> wait $ min mz $ z + h
        s -> maybe (wait z) id $ cont s

----------------------------

main = runCLI "csip"
   $ command "show"    "present files"           (Dir \dir -> getTmpDir >>= \odir -> present dir odir "")
  <> command "export"  "export presentation"     (Dir \dir -> getTmpDir >>= \odir -> export dir odir >>= putStr)
  <> command "diff"    "compare compiled output" (Dir $ tests False)
  <> command "clean"   "clean cache"             (Pure $ getTmpDir >>= removeDirectoryRecursive)
  <> Dir (tests True)

