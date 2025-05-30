module B4_Partial
  ( MonadFail (fail)

  , impossible, undefined, error
  , traceShow
  , MainException, mainException, tagError

  , head, tail, init, last, (!!)
  , initStr, lastStr, headStr, tailStr
  , fromJust
  , foldl1, maximum, minimum
  ) where

import B0_Builtins
import B1_Basic
import B2_String
import B3_RefM


--------------------------------------------------

class MonadFail m where
  fail :: HasCallStack => RefM String -> m a


----------------------------------------------- main exception

data MainException
  = MkMainException (RefM String)
  | MkTag (RefM String) MainException

instance Print MainException where
  print = \case
    MkMainException s -> s
    MkTag s (MkMainException r) -> (\s r -> stripSource r <> "\n" <> showLoc s) <$> s <*> r
    MkTag _ r -> print r

{-# noinline mainException #-}
mainException :: Except MainException
mainException = topM newExcept

tagError :: Print s => s -> Lazy (RefM a) -> RefM a
tagError s m = catchError mainException (throwError mainException . MkTag (print s)) m

instance MonadFail RefM where
  fail s = throwError mainException (MkMainException s)


{-# noinline error #-}
error :: HasCallStack => RefM String -> a
error s = topM (fail s)

{-# noinline error_ #-}
error_ :: HasCallStack => String -> a
error_ s = topM (throwError mainException (MkMainException (pure $ s <> "\n" <> fromString callStackRaw)))

undefined :: HasCallStack => a
undefined = error_ "TODO"

impossible :: HasCallStack => a
impossible = error_ "impossible"

traceShow :: String -> RefM String -> RefM Tup0
--traceShow ~s m  | s `elem` [{-"56", "57"-} "1","2","3","4","5","6","7"] = m >>= \s -> mapM_ putChar (stringToList s) >> putChar '\n'
traceShow _ _ = pure T0



head :: HasCallStack => List a -> a
head (a:. _) = a
head _ = impossible

tail :: HasCallStack => List a -> List a
tail (_:. as) = as
tail _ = impossible

init :: HasCallStack => List a -> List a
init (_ :. Nil) = Nil
init (x :. xs) = x :. init xs
init _ = impossible

last :: HasCallStack => List a -> a
last (x :. Nil) = x
last (_ :. xs) = last xs
last _ = impossible

foldl1 :: HasCallStack => (a -> a -> a) -> List a -> a
foldl1 f (x :. xs) = foldl f x xs
foldl1 _ _ = impossible

maximum, minimum :: (HasCallStack, Ord a) => List a -> a
maximum xs = foldl1 max xs
minimum xs = foldl1 min xs

fromJust :: HasCallStack => Maybe a -> a
fromJust (Just a) = a
fromJust _ = impossible

infixl 9 !!

(!!) :: HasCallStack => List a -> Word -> a
(x :. _)  !! 0 = x
(_ :. xs) !! i = xs !! (i -. 1)
_         !! _ = impossible

headStr :: HasCallStack => String -> Char
headStr (ConsChar c _) = c
headStr _ = impossible

tailStr :: HasCallStack => String -> String
tailStr (ConsChar _ s) = s
tailStr _ = impossible

lastStr :: HasCallStack => String -> Char
lastStr s = case snd (revSplitAtStr 1 s) of
  ConsChar c _ -> c
  _ -> impossible

initStr :: HasCallStack => String -> String
initStr NilStr = impossible
initStr s = fst (revSplitAtStr 1 s)

