module M0_StringMap
  ( StringMap, lookupSM, insertSM, topStringMap
  ) where

import B_Prelude

-----------------------------------------------

itemsMask = 127 :: Word
itemsMask' = itemsMask + 1 :: Word

hashString (c:. _cs) = ord c .&. itemsMask
hashString _ = 0

data HItem a
  = NilHM
  | YesHM a
  | ConsHM Char (HItem a) (HItem a)

consHM _ NilHM b = b
consHM c a b = ConsHM c a b

newtype StringMap a = MkSM (IOArray (HItem a))

newStringMap :: RefM (StringMap a)
newStringMap = MkSM <$> unsafeNewArray_ itemsMask'

resetStringMap (MkSM m) = do
  forM_ (enumFromTo 0 itemsMask') \i -> unsafeWrite m i NilHM

topStringMap :: (StringMap a -> RefM ()) -> StringMap a
topStringMap init = top_ do
  m@(MkSM hm) <- newStringMap
  resetStringMap m
  init m
  elems <- forM (enumFromTo 0 itemsMask') \i -> unsafeRead hm i
  let reset = forM_ (zip (enumFromTo 0 itemsMask') elems) \(i, e) -> unsafeWrite hm i e
  pure (m, reset)

lookupSM_ :: String -> StringMap a -> RefM (HItem a)
lookupSM_ s (MkSM hm) | h <- hashString s = unsafeRead hm h <&> f s
   where
    f Nil = \case
      ConsHM _ _ t -> f Nil t
      z -> z
    f (c:. cs) = \case
      ConsHM c' a b
        | c' == c   -> f cs a
        | True -> f (c:. cs) b
      _ -> NilHM

lookupSM :: String -> StringMap a -> RefM (Maybe a)
lookupSM s sm = lookupSM_ s sm <&> \case
  YesHM a -> Just a
  NilHM   -> Nothing
  _ -> impossible

updateSM :: String -> HItem a -> StringMap a -> RefM ()
updateSM s x (MkSM hm) | h <- hashString s = do
    t <- unsafeRead hm h
    unsafeWrite hm h $ ins s t
   where
    ins Nil = \case
      ConsHM c a b -> ConsHM c a (ins Nil b)
      _ -> x
    ins (c:. cs) = \case
      ConsHM c' a b
        | c' == c   -> consHM c' (ins cs a) b
        | True -> ConsHM c' a (ins (c:.cs) b)
      z -> ConsHM c (ins cs NilHM) z

insertSM :: String -> a -> StringMap a -> RefM ()
insertSM s a sm = updateSM s (YesHM a) sm

{-
runStringMap :: (StringMap a -> RefM b) -> RefM b
runStringMap cont = newStringMap >>= cont

localInsert :: StringMap a -> String -> a -> RefM b -> RefM b
localInsert sm s a m = do
  x <- lookupSM sm s
  updateSM s (YesHM a) sm
  b <- m
  updateSM s x sm
  pure b
-}

