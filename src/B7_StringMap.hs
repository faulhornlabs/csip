module B7_StringMap
  ( StringMap, lookupSM, insertSM, topStringMap
  ) where

import B0_Builtins
import B1_Basic
import B2_String
import B3_RefM
import B4_Partial

-----------------------------------------------

itemsMask = 127 :: Word

hashString' (c:. _cs) = ord c .&. itemsMask
hashString' _ = 0

data HItem a
  = NilHM
  | YesHM a
  | ConsHM Char (HItem a) (HItem a)

consHM _ NilHM b = b
consHM c a b = ConsHM c a b

data StringMap a = MkSM (Array (HItem a))

topStringMap :: (StringMap a -> RefM Tup0) -> StringMap a
topStringMap init = topMReset do
  m <- newArray itemsMask NilHM
  init (MkSM m)
  pure $ T2 (MkSM m) do
    forM_ (enumFromTo 0 $ itemsMask + 1) \i -> writeArray m i NilHM
    init (MkSM m)

lookupSM_ :: String -> StringMap a -> RefM (HItem a)
lookupSM_ (stringToList -> s) (MkSM hm) | h <- hashString' s = readArray hm h <&> f s  where

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

updateSM :: String -> HItem a -> StringMap a -> RefM Tup0
updateSM (stringToList -> s) x (MkSM hm) | h <- hashString' s = do
    t <- readArray hm h
    writeArray hm h $ ins s t
   where
    ins Nil = \case
      ConsHM c a b -> ConsHM c a (ins Nil b)
      _ -> x
    ins (c:. cs) = \case
      ConsHM c' a b
        | c' == c   -> consHM c' (ins cs a) b
        | True -> ConsHM c' a (ins (c:.cs) b)
      z -> ConsHM c (ins cs NilHM) z

insertSM :: String -> a -> StringMap a -> RefM Tup0
insertSM s a sm = updateSM s (YesHM a) sm
