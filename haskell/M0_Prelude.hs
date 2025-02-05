module M0_Prelude
  ( module P

  , lookupList
  , singletonSet, insertSet, fromListSet
  , assocs

  , stripSuffix
  , firstJust
  )
 where

----------------------------------------------- public imports

import Data.Function as P
  ( on, ($), (.), const, flip, id )
import Prelude as P
  ( ($!), seq
  , Char, String
  , Int, Integer, fromIntegral
  , Bool (True, False), (&&), (||), not, otherwise
  , fst, snd, curry, uncurry
  , Ordering (LT, EQ, GT)
  )
import Data.List as P
  ( group, groupBy, partition, nub, nubBy, init, inits, last, tails, (!!), (++), (\\), drop, dropWhile, take, takeWhile, filter
  , iterate, map, mapAccumL, mapAccumR, partition, replicate, reverse, scanl, scanr, sort, sortBy, sortOn, span, splitAt, transpose, zip, zipWith, unzip
  , intercalate, intersperse, stripPrefix, repeat
  )
import Data.Maybe as P
  ( Maybe (Just, Nothing), maybe, fromMaybe, maybeToList, listToMaybe, isJust, isNothing )
import Data.Either as P
  ( Either (Left, Right), either, isLeft, isRight )
import Data.String as P
  ( IsString (fromString), unlines, lines, words )
import Data.Set as P
  ( Set, member, delete, isSubsetOf)
import Data.Map as P
  ( Map, size, insert, lookup, singleton, fromList, unionsWith, restrictKeys, withoutKeys )

import Prelude as P
  ( Eq ((==)), (/=)
  , Ord (compare, (<=), (>=), (<), (>), max, min)
  , Num ((+), (-), (*))
  , Integral (div, mod)
  , Show (show)
  , read
  )
import Prelude as P
  ( Semigroup ((<>))
  , Monoid (mempty), mconcat
  )
import Data.Functor as P
  ( Functor (fmap), (<$>), ($>), (<$), (<&>) )
import Control.Applicative as P 
  ( Applicative (pure, (<*>)), (<*), (*>), liftA2, Const, getConst )
import Control.Arrow as P
  ( Arrow (arr, (***)), first, second, (&&&) )
import Control.Monad as P
  ( void, when
  , Monad ((>>=), (>>)), join, (>=>), (<=<), (=<<), forM, forM_, filterM, foldM
  , fail
  )
import Data.Foldable as P
  ( Foldable (foldMap), toList, foldr, foldl, foldl1, foldr1, null, length, elem, maximum, minimum, sum, all, and, any, or
  , concat, concatMap, find, foldlM, foldrM, for_, mapM_, maximumBy, minimumBy, sequence_, sequenceA_, traverse_
  )
import Data.Traversable as P
  ( Traversable (sequenceA), traverse, sequence, mapM )

-- import Debug.Trace as P (trace)
import Data.Coerce as P (coerce)

----------------------------------------------- private imports

import qualified Prelude
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Control.Applicative as Q

----------------------------------------------- renamings

lookupList = Prelude.lookup

singletonSet = Set.singleton
fromListSet = Set.fromList
insertSet = Set.insert

assocs = Map.toList

stripSuffix a b = fmap reverse $ stripPrefix (reverse a) (reverse b)

firstJust :: Maybe a -> Maybe a -> Maybe a
firstJust = (Q.<|>)
