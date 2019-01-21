-- -*- coding: utf-8 -*-
-- Copyright: © 2019 Simon Nielsen Knights <tauoverpi@yandex.com>
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
zipWire : Monad m => %static a -> List (Wire m a b) -> Wire m (List a) (List b)
zipWire def ws {a} = feedback ws $ effect $ \(xs, ws) => go id id xs ws
  where go : (List (Wire m a b) -> List (Wire m a b))
          -> (List b -> List b)
          -> List a
          -> List (Wire m a b)
          -> m (List b, List (Wire m a b))
        go sfs bs _ [] = pure (bs [], sfs [])
        go sfs bs [] (w::ws) =
          do (sf, b) <- stepWire w def
             go (sfs . (sf::)) (bs . (b::)) [] ws
        go sfs bs (x::xs) (w::ws) =
          do (sf, b) <- stepWire w x
             go (sfs . (sf::)) (bs . (b::)) xs ws

dZipWire : Monad m => a -> List (Wire m a b) -> Wire m (List a) (List b)
dZipWire def ws = delay (replicate (length ws) def) id >>> (zipWire def ws)

||| Apply a collection of inputs to a collection of wires. If there's no
||| wire bound to `k`, create one. If the wire inhibits, remove it.
gatherMany : (Monad m, Ord k)
          => (k -> Wire m a (Event b))
          -> Wire m (SortedMap k a) (SortedMap k b)
gatherMany gen {a} = feedback empty' (effect update)
  where empty' : (Monad m, Ord k) => SortedMap k (Wire m a (Event b))
        empty' = empty

        empty'' : Ord k => SortedMap k b
        empty'' = empty

        step : (Monad m, Ord k)
            => (SortedMap k b, SortedMap k (Wire m a (Event b)))
            -> (k, a)
            -> m (SortedMap k b, SortedMap k (Wire m a (Event b)))
        step (so, sw) (k, x) =
          case lookup k sw of
               Nothing => do (sf, b) <- stepWire (gen k) x
                             case b of
                                  NotNow => pure (so, delete k sw)
                                  Now b  => pure (insert k b so, insert k sf sw)
               Just sf => do (sf, b) <- stepWire sf x
                             case b of
                                  NotNow => pure (so, delete k sw)
                                  Now b  => pure (insert k b so, insert k sf sw)

        update : (Monad m, Ord k)
              => (SortedMap k a, SortedMap k (Wire m a (Event b)))
              -> m (SortedMap k b, SortedMap k (Wire m a (Event b)))
        update (si, sw) = foldlM step (empty'', sw) (toList si)

||| Apply input to a collection of wires. If there's no wire
||| bound to `k`, create one. If the wire inhibits, remove it.
gather : (Monad m, Ord k) => (k -> Wire m a (Event b)) -> Wire m (k, a) (SortedMap k b)
gather gen = arrow single >>> gatherMany gen
  where single : (k, a) -> SortedMap k a
        single (k, a) = insert k a empty

-- TBD: WellFounded recursion
dynamic : (Monad m, Eq k) => (k -> Wire m a (Event b)) -> Wire m (k, a) (List b)
dynamic gen {a} = feedback [] (effect (update id id))
  where update : (Monad m, Eq k)
              => (List (k, Wire m a (Event b), b) -> List (k, Wire m a (Event b), b))
              -> (List b -> List b)
              -> ((k,a), List (k, Wire m a (Event b), b))
              -> m (List b, List (k, Wire m a (Event b), b))

        update sfs bs ((k, x), []) =
          do (sf, Now b) <- stepWire (gen k) x | _ => pure (bs [], sfs [])
             let sfs = sfs . (List.(::) (k, sf, b))
             let bs  = bs . (b::)
             pure (bs [], sfs [])

        update sfs bs ((k, x), (k', sf, b) :: cs) =
          if k == k'
             then do (sf, Now b) <- stepWire sf x
                      | _ => pure (bs (map (snd . snd) cs), sfs cs)
                     let sfs = sfs . ((k', sf, b)::)
                     let bs  = bs . (b::)
                     pure (bs (map (snd . snd) cs), sfs cs)
             else assert_total $ update (sfs . ((k', sf, b)::)) (bs . (b::)) ((k, x), cs)

-- TBD
-- mux : (Monad m, Ord k) => (k -> Wire m a b) -> Wire m (k, a) b
-- mux gen {a} = feedback empty' (effect update)
--   where empty' : (Monad m, Ord k) => SortedMap k (Wire m a b)
--         update : (Monad m, Ord k)
--               => ((k, a), SortedMap k (Wire m a b))
--               -> m (b, SortedMap k (Wire m a b))

parA : (Monad m, Traversable f)
    => %static ({sf:_} -> a -> f sf -> f (sf, b))
    -> f (Wire m b c)
    -> Wire m a (f c)
parA tran col = feedback col $ effect $ \(x, co) =>
  do sfs <- traverse (map (map (Force . Force) . swap) . uncurry stepWire) (tran x co)
     pure (map fst sfs, map snd sfs)
