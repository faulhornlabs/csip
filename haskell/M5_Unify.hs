module M5_Unify
  ( conv
  ) where

import M1_Base
import M3_Parse
import M4_Eval

-------------

expr a = foreground yellow a

conv  :: Val -> Val -> RefM ()
conv aa bb = go aa bb where

 go a_ b_ = do
  (fa, va) <- force' a_
  (fb, vb) <- force' b_
  case (view va, view vb) of
    _ | va == vb -> pure ()
    (VMeta, _) -> updateClosed va fb
    (_, VMeta) -> updateClosed vb fa
    (VSup c _, _) -> do
      v <- mkName (varName c) <&> vVar
      va' <- vApp fa v
      vb' <- vApp fb v
      go va' vb'
    (_, VSup c _) -> do
      v <- mkName (varName c) <&> vVar
      va' <- vApp fa v
      vb' <- vApp fb v
      go va' vb'
    (VMetaApp{}, VMetaApp{}) -> solveMeta va fb  -- TODO!
    (VMetaApp{}, _) -> solveMeta va fb
    (_, VMetaApp{}) -> solveMeta vb fa
    (VApp f a, VApp g b) -> go f g >> go a b
    _ -> do
      sa <- print =<< force_ aa
      sb <- print =<< force_ bb
      error $ fromString $ chars $ "Expected type\n " <> expr sb <> "\ninstead of\n " <> expr sa
