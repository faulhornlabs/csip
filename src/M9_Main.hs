import D_Base
import E_Parse
import F_Eval
import H_Elab
import I_Stage
import M8_IO

----------------------------

getTmpDir = do
  d <- getTemporaryDirectory <&> (</> "csip")
  createDirectoryIfMissing True d
  pure d

----------------------------

getCmd :: String -> RefM (Tup2 (List (List String)) String)
getCmd = \case
  ConsChar '#' (ConsChar ' ' (spanStr (/= '\n') -> T2 cmd (ConsChar '\n' s))) -> do
    cmd <- parse cmd >>= f
    T2 cmds s <- getCmd s
    pure (T2 (cmd:. cmds) s)
  s -> pure (T2 Nil s)
 where
  f :: Raw -> RefM (List String)
  f (a :@ b) = print b >>= \b -> f a <&> \as -> as ++ b :. Nil
  f n = print n <&> (:.Nil)

getString f = parseFile' "" f >>= \case
  Nothing -> pure Nothing
  Just s -> Just . first maybeElab <$> getCmd s
 where
  maybeElab Nil = ("elab" :. Nil) :. Nil
  maybeElab cmds = cmds


showCmd :: List String -> String
showCmd = mconcat . intersperse " "

doCmds :: List String -> String -> RefM String
doCmds cmd s = do
 T0 <- reset
 catchError mainException (\e -> appendLoc <$> print e) (doCmds_ cmd s)

doCmds_ :: List String -> String -> RefM String
doCmds_ cmd s = case cmd of
  cmd :. Nil                       -> doCmd False cmd s
  cmd :. "highlight" :. Nil          -> doCmd False cmd s <&> appendLoc
  cmd :. "quote" :. Nil              -> doCmd True  cmd s
  cmd :. "quote" :. "highlight" :. Nil -> doCmd True  cmd s <&> appendLoc
  cmds ->  errorM $ pure $ "Unknown commands: " <> mconcat (intersperse " " cmds)
 where
  doCmd :: Bool -> String -> String -> RefM String
  doCmd quote cmd s = case cmd of
    "source"    -> sh =<< (parse s :: RefM String)
    "indent"    -> sh =<< (parse s :: RefM IString)
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
    "scope"     -> sh =<< (parse s :: RefM Raw)    -- TODO: remove
    "elab"      -> sh =<< (parse s :: RefM Tm)
    "eval"      -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= quoteNF)
    "type"      -> sh =<< (parse s >>= inferTop <&> (\(MkTmTy _ t) -> t) >>= quoteNF')
    "evalquote" -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= quoteNF')
    "stage"     -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= stage)
    "haskell_stage"
                -> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= stageHaskell)
    "stage_eval"-> sh =<< ((parse s :: RefM Tm) >>= evalClosed' >>= stage_eval)
    _ -> errorM $ pure ("Unknown command: " <> cmd)
   where
    sh :: (PPrint a, Print a) => a -> RefM String
    sh x = if quote then sh' x else print x

  sh' :: PPrint a => a -> RefM String
  sh' m = print (pprint m)


----------------------------

listDirRec f = doesDirectoryExist f >>= \case
  True -> listDirectory f >>= mapM (listDirRec . (f </>)) <&> concat
  False -> pure (f :. Nil)

testNames :: FilePath -> IO (List FilePath)
testNames dir = do
  ns <- listDirRec dir <&> \fs -> sort (filter (isJust . stripSuffix ".csip") fs)
  if null ns then errorM $ "no .csip files found at " <<>> pure dir
    else pure ns


getResult odir fn s cmd _i n = do
  r <- parseFile' odir out
  pure (T2 (printFile' (odir </> out)) r)
 where out = hashString $ "# " <> showCmd cmd <> " # " <> fn <> " # " <> showInt n <> " # " <> versionString <> "\n" <> s

getResult' odir fn s cmd i n = do
  T2 printres r <- getResult odir fn s cmd i n
  maybe (doCmds cmd s >>= \r -> printres r >> pure r) pure r

parseFile' dir f | fn <- dir </> f = doesFileExist fn >>= \case
  False -> pure Nothing
  True  -> parseFile dir f <&> Just

printFile' :: Print s => FilePath -> s -> IO Tup0
printFile' f s = do
  createDirectoryIfMissing True (directory f)
  printFile f s

tests accept dir = do
  odir <- getTmpDir
  testFiles accept dir odir

testFiles accept dir odir = do
 fs <- testNames dir
 forM_ fs \fn -> do
  Just (T2 cmds s) <- getString fn
  forM_ (numberWith T2 0 cmds) \(T2 i cmd) -> do
    if accept then do
      r <- getResult' odir fn s cmd i (length cmds)
      putStr
           $ invertColors (foreground cyan $ "           " <> showCmd cmd <> " " <> fn <> "           ") <> "\n"
          <> r <> "\n"
     else do
      T2 printres r2 <- getResult odir fn s cmd i (length cmds)
      r <- doCmds cmd s
      when (r2 /= Just r) do
        putStr
           $ maybe "" (\r -> 
             invertColors (foreground cyan $ "   old     " <> showCmd cmd <> " " <> fn <> "           ") <> "\n"
          <> r <> "\n") r2
          <> invertColors (foreground cyan $ "   new     " <> showCmd cmd <> " " <> fn <> "           ") <> "\n"
          <> r <> "\n"
          <> maybe "" (\r' -> if lines r' /= lines r then
               invertColors (foreground red $ "    first diff    ")
            <> mconcat (take 1 do T2 a b <- repNl (lines r') (lines r); guard (a /= b); pure ("\n" <> a <> "\n" <> b <> "\n"))
            else "") r2
        askYN "accept" >>= \b -> if b then printres r else pure T0

repNl as bs = zip (as ++ replicate (c-.a) "") (bs ++ replicate (c-.b) "")
 where
  a = length as; b = length bs; c = max a b

present dir odir beg = do
  fs <- testNames dir
  let
   l = length fs
   f i = do
    let fn = fs !! i
        reload  = present dir odir fn
    getString fn >>= \case
     Nothing -> reload
     Just (T2 cmds s) -> do

      rs <- forM (numberWith T2 0 cmds) \(T2 j cmd) -> do
          r <- getResult' odir fn s cmd j (length cmds)
          pure (T2 (showCmd cmd <> " " <> fn) r)
      let
        g = do
          let
            nextF   = condCons (i+1 < l) (f (i+1)) Nil
            prevF   = condCons (i > 0)  (f (i-.1)) Nil
            end     = pure T0 :. Nil
            wait k  = listToMaybe $ case k of
              " "         -> nextF
              "\n"        -> nextF
              "Backspace" -> prevF
              "Left"      -> prevF
              "Right"     -> nextF
              "Esc"       -> end
              "q"         -> end
              "r"         -> reload :. Nil
              _           -> Nil

          T2 w h <- getTerminalSize
          disp h (mkScreen True (T2 w h) cyan rs) wait
      g

  presentationMode $ f $ min (length fs -. 1) $ length $ filter (< beg) fs

export dir odir = do
  wh <- getTerminalSize
  fs <- testNames dir
  rs <- forM fs \fn -> do
    Just (T2 cmds s) <- getString fn
    rs <- forM (numberWith T2 0 cmds) \(T2 j cmd) -> do
      r <- getResult' odir fn s cmd j (length cmds)
      pure (T2 (showCmd cmd <> " " <> fn) r)
    pure $ mkScreen False wh cyan rs
  pure (mconcat $ map (<> "\n") $ concat rs)

distribute :: Word -> Word -> List Word
distribute ((+1) -> parts) i = zipWith (-.) is (0:.is) where
  is = enumFromTo 1 parts <&> \j -> (j * i -. 1) `div` parts

mkScreen :: Bool -> Tup2 Word Word -> Color -> List (Tup2 String String) -> List String
mkScreen rich (T2 w h) color ts
  = concat $ zip os tls <&> \case
    T2 o (t:. ls) ->
      let o1 = o `div` 2 in
      let o2 = o -. o1   in
         t:. replicate o1 "" ++ ls ++ replicate o2 ""
    _ -> impossible
 where
  mh = sum $ map length tls
  os = distribute (length tls) $ h -. mh
  tls = map f ts

  f :: Tup2 String String -> List String
  f (T2 title s) =
    (if rich then invertColors . foreground color $ replicateStr t1 ' ' <> title <> replicateStr t2 ' '
             else replicateStr t1 '=' <> title <> replicateStr t2 '=')
    :. (ls <&> \s -> (if rich then cursorForward ow else replicateStr ow ' ') <> s)
   where
    ls = lines s
    mw = maximum (0:. map lengthANSI ls)
    ow = (w -. mw) `div` 2
    t1 = (w -. lengthANSI title) `div` 2
    t2 = w -. t1 -. lengthANSI title

disp :: Word -> List String -> (String -> Maybe (IO Tup0)) -> IO Tup0
disp h ls' cont = wait 0
   where
    mz = length ls' -. h
    wait z = do
      putStr
        $  clearScreen
        <> mconcat (zip (enumFromTo 0 h) (drop z ls') <&> \(T2 i l) -> setCursorPosition i 0 <> l)
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

