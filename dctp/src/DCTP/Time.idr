-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Time

import DCTP.Core
import DCTP.Trans
import DCTP.Switch
import DCTP.Event
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Category
import Control.Arrow

%default total
%access public export

||| Compute delta time
dt : (Monad m, Neg b) => m b -> Wire m a b
dt tm {b} = switch id $ effect $ \_ =>
  do (_, t) <- stepWire time ()
     pure (0, Now (dt' t))
  where time : Num b => Wire m a b
        time = effect (const tm)
        dt' : Neg b => b -> Wire m a b
        dt' t = time - pure t

||| Compute the integral of a given initial value and a time source
integral : (Monad m, Num a) => (source : m a) -> a -> Wire m a a
integral time init = feedback init (x + dt*dx &&& x)
  where dt = effect (const time)
        dx = arrow fst
        x  = arrow snd

||| Inhibit on a specific interval determined by a given predicate
interval : (Monad m, Num n, Ord n)
        => (test : n -> n -> Bool)
        -> m n
        -> n
        -> Wire m a (Event a)
interval test tm lim = switch id (never &&& map (Now . wire) time)
  where time : Wire m a n
        time = effect (const tm)
        wire : (Monad m, Num n, Ord n) => n -> Wire m a (Event a)
        wire o = let limit = pure (o + lim)
                     event = edge . liftA2 test limit (now o ->> time)
                 in liftA2 (map . const) id event

||| Live for a given time period then dead there after
||| + inhibits: after the given time offset
for : (Monad m, Num n, Ord n) => m n -> n -> Wire m a (Event a)
for time limit = interval (>) time limit >> never

||| Live after a given time period
||| + inhibits: until the given time offset
after : (Monad m, Neg n, Ord n) => m n -> n -> Wire m a (Event a)
after time limit = interval (<) time (limit - 1)

||| Live at every interval
||| + inhibits: between every interval
every : (Monad m, Num n, Ord n) => m n -> n -> Wire m a (Event a)
every time limit = resetSelf (interval (==) time limit >>> id &&& id)
