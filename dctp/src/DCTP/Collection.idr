-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Collection

import DCTP.Core
import DCTP.Event
import Control.Category
import Control.Arrow
import Data.SortedMap
import Debug.Trace

%default total
%access public export

||| Apply a list of wires over a list of inputs. If there isn't enough
||| input supply the given default value
zipWire : Monad m => a -> List (Wire m a b) -> Wire m (List a) (List b)
zipWire def ws {a} = feedback ws $ effect $ \(xs, ws) => go id xs ws
  where go : (List (b, Wire m a b) -> List (b, Wire m a b)) -> List a -> List (Wire m a b) -> m (List b, List (Wire m a b))
        go acc _ [] = pure (unzip $ acc [])
        go acc [] (w::ws) =
          do (sf, x) <- stepWire w def
             go (acc . ((x, sf)::)) [] ws
        go acc (x::xs) (w::ws) =
          do (sf, x) <- stepWire w x
             go (acc . ((x, sf)::)) xs ws

dZipWire : Monad m => a -> List (Wire m a b) -> Wire m (List a) (List b)
dZipWire def ws = delay (replicate (length ws) def) id >>> (zipWire def ws)

-- this is probably the most ugly function in this library
gatherMany : (Monad m, Ord k)
          => (k -> Wire m a (Event b))
          -> Wire m (SortedMap k a) (SortedMap k b)
gatherMany gen {a} = feedback (the (SortedMap k (Wire m a (Event b))) empty)
                   $ effect $ \(x, col) =>
  do let kvs = toList x
     sfs <- map catMaybes
            $ the (m (List (Maybe (Wire m a (Event b), k, b))))
            $ flip traverse kvs $ \(k, v) =>
              case lookup k col of
                   Nothing => do (sf, b) <- stepWire (gen k) v
                                 case b of
                                      NotNow => pure Nothing
                                      Now b  => pure (Just (sf, k, b))
                   Just w  => do (sf, b) <- stepWire w v
                                 case b of
                                      NotNow => pure Nothing
                                      Now b  => pure (Just (sf, k, b))
     let (co, bs) = foldl (\(acc, bs), (sf, k, b) => (insert k sf acc, insert k b bs))
                           (col, the (SortedMap k b) empty) sfs
     pure (bs, co)

gather : (Monad m, Ord k) => (k -> Wire m a (Event b)) -> Wire m (k, a) (SortedMap k b)
gather gen = arrow single >>> gatherMany gen
  where single : (k, a) -> SortedMap k a
        single (k, a) = insert k a empty

-- dynamic : Monad m => (k -> Wire m a (Event b)) -> Wire m (k, a) (List b)

-- mux : (Monad m, Ord k) -> (k -> Wire m a b) -> Wire m (k, a) b

parA : (Monad m, Traversable f)
    => ({sf:_} -> a -> f sf -> f (sf, b))
    -> f (Wire m b c)
    -> Wire m a (f c)
parA tran col = feedback col $ effect $ \(x, co) =>
  do sfs <- traverse (map (map (Force . Force) . swap) . uncurry stepWire) (tran x co)
     pure (map fst sfs, map snd sfs)
