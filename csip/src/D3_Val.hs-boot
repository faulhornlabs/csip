module D3_Val where

import C_Syntax
import D1_Combinator

data Val

instance HasName Val
instance IsRigid Val
instance IsClosed Val
