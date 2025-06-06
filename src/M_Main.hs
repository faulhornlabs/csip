
import D_Calculus
import E3_Elab
import E4_Stage

----------------------------

getCmd :: String -> IO (Tup2 (List (List String)) String)
getCmd = \case
  ConsChar '#' (ConsChar ' ' (spanStr (/= '\n') -> T2 cmd (ConsChar '\n' s))) -> do
    cmd <- parse cmd >>= runMem . f
    T2 cmds s <- getCmd s
    pure (T2 (cmd:. cmds) s)
  s -> pure (T2 Nil s)
 where
  f :: Raw -> Mem (List String)
  f (a :@ b) = print b >>= \b -> f a <&> \as -> as ++ b :. Nil
  f n = print n <&> (:.Nil)

showCmd :: List String -> String
showCmd = mconcat . intersperse " "

doCmds :: List String -> String -> IO String
doCmds cmd s = do
 T0 <- runMem $ reset mainReset
 catchErrors (\e -> runMem $ appendLoc <$> print e) (doCmds_ cmd s)

doCmds_ :: List String -> String -> IO String
doCmds_ cmd s = case cmd of
  cmd :. Nil                           -> doCmd False cmd s
  cmd :. "highlight" :. Nil            -> doCmd False cmd s <&> appendLoc
  cmd :. "quote" :. Nil                -> doCmd True  cmd s
  cmd :. "quote" :. "highlight" :. Nil -> doCmd True  cmd s <&> appendLoc
  cmds -> fail $ pure $ "Unknown commands: " <> mconcat (intersperse " " cmds)
 where
  doCmd :: Bool -> String -> String -> IO String
  doCmd quote cmd s = case cmd of
    "source"    -> runMem . sh =<< (parse s :: IO String)
    "indent"    -> runMem . sh =<< (parse s :: IO IString)
    "lex"       -> runMem . sh =<< (parse s :: IO (List (Name Spaced)))
    "structure" -> runMem . sh =<< (parse s :: IO (NameSeq Spaced))
    "string"    -> runMem . sh =<< (parse s :: IO (NameSeq Stringed))
    "comment"   -> runMem . sh =<< (parse s :: IO (NameSeq Uncomment))
    "comments"  -> runMem . sh =<< (parse s :: IO (NameSeq Uncomments))
    "space"     -> runMem . sh =<< (parse s :: IO (NameSeq Unspaced))
    "layout"    -> runMem . sh =<< (parse s :: IO (NameSeq Layout))
    "op"        -> runMem . sh =<< (parse s :: IO (ExpTree' Layout))
    "exptree"   -> runMem . sh =<< (parse s :: IO (ExpTree' PatchedOp))
    "sugar1"    -> runMem . sh =<< (parse s :: IO (ExpTree' Desug))
    "sugar"     -> runMem . sh =<< (parse s :: IO (ExpTree' Import))
    "scope"     -> runMem . sh =<< (parse s :: IO (ExpTree' Scope))
    "elab"      -> runMem . sh =<< ((parse s :: IO Tm) >>= runMem . (walkTm True >=> unscope False))
    "eval"      -> runMem . sh =<< ((parse s :: IO Tm) >>= runMem . (evalClosed' >=> quoteNF >=> walkTm False >=> unscope False))
    "evalquote" -> runMem . sh =<< ((parse s :: IO Tm) >>= runMem . evalClosed' >>= runMem . quoteLets)
    "type"      -> runMem . sh =<< (parse s >>= runMem . infer <&> (\(MkTmTy _ t) -> t))
    "stage"     -> runMem . sh =<< (parse s >>= runMem . evalClosed' . getCode >>= runMem . stage)
    "pstage"    -> runMem . sh =<< (parse s >>= runMem . evalClosed' . getPCode >>= runMem . pstage)
    "haskell_stage"
                -> runMem . sh =<< (parse s >>= runMem . evalClosed' . getCode >>= runMem . stageHaskell)
    "stage_eval"-> runMem . sh =<< (parse s >>= runMem . evalClosed' . getCode >>= runMem . stage_eval)
    _ -> fail $ pure $ "Unknown command: " <> cmd
   where
    sh :: (PPrint a, Print a) => a -> Mem String
    sh x = case quote of
      True -> pprint' x
      _    -> print x

    getCode (MkCodeTm t) = t
    getPCode (MkPCodeTm t) = t


----------------------------

data Command = MkCommand String (List String) (String -> IO Tup0) (Maybe String)

splitFile :: FilePath -> String -> List (Tup2 FilePath String)
splitFile fn s = case go s of
  x :. Nil -> T2 fn x :. Nil
  xs -> numberWith (\i s -> T2 (fn <> "#" <> showWord i) s) 1 xs
 where
  go s = case find 0 s of
    Nothing -> s :. Nil
    Just (T2 i j) | T2 as bs <- splitAtStr i s -> as :. go (dropStr (j+1) bs)

  find :: Word -> String -> Maybe (Tup2 Word Word)
  find n (ConsChar '\n' s)
    | T2 a (ConsChar '\n' _) <- spanStr (== '#') s
    , len <- lengthStr a + 1
    , 6 <= len
    = Just (T2 n len)
  find n (ConsChar _ s) = find (n+1) s
  find _ _ = Nothing


testNames :: List FilePath -> IO (List (Tup2 FilePath (List Command)))
testNames files = do
  l <- mconcat <$> forM (filter (isJust . stripSuffix ".csip") files) \fn -> parseFile "" fn >>= \case
    Nothing -> pure Nil
    Just s -> forM (splitFile fn s) \(T2 fn s) -> do
      T2 cmds s <- getCmd s
      let n = length cmds
      rs <- forM (maybeElab cmds) \cmd -> do
        let str = "# " <> showCmd cmd <> " # " <> fn <> " # " <> showWord n <> " # " <> versionString <> "\n" <> s
        let out = hashString str <> ".csipout"
        tdir <- getTemporaryDir
        r <- parseFile tdir out
        pure $ MkCommand s cmd (printFile (tdir </> out)) r
      pure $ T2 fn rs
  case l of
    Nil  -> fail $ pure "no tasks given"
    _    -> pure l
 where
  maybeElab Nil = ("elab" :. Nil) :. Nil
  maybeElab cmds = cmds

getRR (MkCommand _ _ _   (Just m)) = pure m
getRR (MkCommand s cmd printres _) = doCmds cmd s >>= \r -> printres r >> pure r

testFiles accept files = do
 fs <- testNames files
 forM_ fs \(T2 fn cmds) -> do
  forM_ cmds \r_@(MkCommand s cmd printres r2) -> do
    let title msg r = invertColors (foreground cyan $ msg <> showCmd cmd <> " " <> fn <> "           ") <> "\n" <> r <> "\n"
    case accept of
     True -> getRR r_ >>= putStr . title "           "
     _    -> do
      r <- doCmds cmd s
      case r2 == Just r of
       True -> pure T0
       _    -> do
        putStr
           $ maybe "" (title "   old     ") r2 <> title "   new     " r
          <> maybe "" (\r' -> case lines r' /= lines r of
               True ->
                   invertColors (foreground red $ "    first diff    ")
                <> mconcat (take 1 do T2 a b <- repNl (lines r') (lines r); guard (a /= b); pure ("\n" <> a <> "\n" <> b <> "\n"))
               _    -> "") r2
        askYN "accept" >>= \case
          Just True -> printres r
          _         -> pure T0

repNl as bs = zipWith T2 (as ++ replicate (c-a) "") (bs ++ replicate (c-b) "") where

  a = length as; b = length bs; c = max a b

present :: List FilePath -> FilePath -> IO Tup0
present files beg = do
  fs <- testNames files

  let l = length fs

      f i = do
        rs <- forM cmds \r_@(MkCommand _ cmd _ _) -> T2 (showCmd cmd <> " " <> fn) <$> getRR r_
        wh <- getTerminalSize
        disp (snd wh) (mkScreen True wh cyan rs) wait
       where
        T2 fn cmds = fromMaybe (lazy $impossible) $ fs !! i
        wait k
          | k == " " || k == "\n" || k == "Right", i+1 < l = Just (f (i+ 1))
          | k == "Backspace"      || k == "Left" , i > 0   = Just (f (i-1))
          | k == "Esc" || k == "q"  = Just (pure T0)
          | k == "r"                = Just (present files fn)
          | True                    = Nothing

      ix = length $ takeWhile ((/= beg) . fst) fs

  f $ ix `mod` l

export files = do
  T2 w h <- getTerminalSize
  fs <- testNames files
  rs <- forM fs \(T2 fn cmds) -> do
    rs <- forM cmds \r_@(MkCommand _ cmd _ _) -> do
      r <- getRR r_
      pure (T2 (showCmd cmd <> " " <> fn) r)
    pure $ mkScreen False (T2 w h) cyan rs
  pure (mconcat $ map (<> "\n") $ mconcat rs)

mkScreen :: Bool -> Tup2 Word Word -> Color -> List (Tup2 String String) -> List String
mkScreen rich (T2 w h) color ts
  = mconcat $ zipWith T2 os tls <&> \case
    T2 o (t:. ls) ->
      let o1 = o `div` 2 in
      let o2 = o - o1   in
         t:. replicate o1 "" ++ ls ++ replicate o2 ""
    _ -> $impossible
 where
  mh = foldl (+) 0 $ map length tls
  os = distribute (length tls) $ h - mh
  tls = map f ts

  f :: Tup2 String String -> List String
  f (T2 title s) =
    (case rich of
      True -> invertColors . foreground color $ takeStr t1 spaces <> title <> takeStr t2 spaces
      _    -> takeStr t1 eqs <> title <> takeStr t2 eqs)
    :. (ls <&> \s -> (case rich of True -> cursorForward ow; _ -> takeStr ow spaces) <> s)
   where
    eqs    = "=========================================================================================================================================="
    spaces = "                                                                                                                                          "

    ls = lines s
    mw = foldl max 0 (map lengthANSI ls)
    ow = (w - mw) `div` 2
    t1 = (w - lengthANSI title) `div` 2
    t2 = w - t1 - lengthANSI title

disp :: Word -> List String -> (String -> Maybe (IO Tup0)) -> IO Tup0
disp h ls' cont = wait 0  where

  mz = length ls' - h
  wait z = do
    putStr $ clearScreen <> mconcat (zipWith T2 (enumFromTo 0 h) (drop z ls') <&> \(T2 i l) -> setCursorPosition i 0 <> l)
    getKey >>= \case
      "Up"       | z > 0  -> wait (z - 1)
      "Down"     | z < mz -> wait (z +  1)
      "PageUp"   | z > 0  -> wait (z - h)
      "PageDown" | z < mz -> wait (min mz $ z + h)
      s -> case cont s of
        Just m -> m
        _      -> wait z


----------------------------

main = runIO $ runCLI "csip"
   $ command "show"    "present files"           (Files \files -> presentationMode $ present files "")
  <> command "export"  "export presentation"     (Files \files -> export files >>= putStr)
  <> command "diff"    "compare compiled output" (Files \files -> testFiles False files)
  <> Files (testFiles True)
