-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Switch

import DCTP.Core
import DCTP.Event
import Control.Arrow
import Control.Category

%default total
%access public export

||| Generic switch
||| + switch: once, now, reset
||| + inhibits: same as first given wire
switch : Monad m => (c -> Wire m a b) -> Wire m a (b, Event c) -> Wire m a b
switch = WSwitch

||| Generic switch in the next frame
||| + switch: once, next, reset
||| + inhibits: same as first given wire
dSwitch : Monad m => (c -> Wire m a b) -> Wire m a (b, Event c) -> Wire m a b
dSwitch = WDSwitch

||| Reset switch
||| + switch: recuring, now, reset
||| + inhibits: same as given wire
reset : Monad m => Wire m a b -> Wire m (a, Event c) b
reset old = feedback old $ effect $ \((x, c), sf) =>
  case c of
       NotNow => do (sf, x) <- stepWire sf x; pure (x, sf)
       Now _  => do (sf, x) <- stepWire old x; pure (x, sf)

||| Reset self switch in the next frame
||| + switch: recuring, next, reset
||| + inhibits: same as given wire
resetSelf : Monad m => Wire m a (b, Event c) -> Wire m a b
resetSelf sf = feedback NotNow $ reset sf

become : Monad m => Wire m a (Event b) -> Wire m a b -> Wire m a b
become sf sg = dSwitch id $ feedback sf $ effect $ \(x, sf) =>
  do (sf, b) <- stepWire sf x
     case b of
          NotNow => do (sg, b) <- stepWire sg x; pure ((b, Now sg), sf)
          Now b  => pure ((b, NotNow), sf)

becomeE : Monad m => Wire m a (Event b) -> Wire m a (Event b) -> Wire m a (Event b)
becomeE sf sg = switch id $ feedback sf $ effect $ \(x, sf) =>
  do (sf, b) <- stepWire sf x
     case b of
          NotNow => pure ((NotNow, Now sg), sg)
          Now _  => pure ((b, NotNow), sf)

alt : Monad m => Wire m a (Event b) -> Wire m a b -> Wire m a b
alt sf sg = feedback (sf, sg) $ effect $ \(x, sf, sg) =>
  do (sf, b) <- stepWire sf x
     case b of
          NotNow => do (sg, b) <- stepWire sg x; pure (b, sf, sg)
          Now b  => pure (b, sf, sg)

altE : Monad m => Wire m a (Event b) -> Wire m a (Event b) -> Wire m a (Event b)
altE sf sg = feedback (sf, sg) $ effect $ \(x, sf, sg) =>
  do (sf, b) <- stepWire sf x
     case b of
          NotNow => do (sg, b) <- stepWire sg x; pure (b, sf, sg)
          Now b  => pure (Now b, sf, sg)

rSwitch : Monad m => Wire m a b -> Wire m (a, Event (Wire m a b)) b
rSwitch sf = feedback sf $ effect $ \((x, e), sf) =>
  case e of
       NotNow => do (sf, b) <- stepWire sf x; pure (b, sf)
       Now w  => do (sf, b) <- stepWire w  x; pure (b, sf)

drSwitch : Monad m => Wire m a b -> Wire m (a, Event (Wire m a b)) b
drSwitch sf = feedback sf $ effect $ \((x, e), sf) =>
  case e of
       NotNow => do (sf, b) <- stepWire sf x; pure (b, sf)
       Now w  => do (sf, b) <- stepWire sf x; pure (b, w)

kSwitch : Monad m
       => Wire m a b
       -> Wire m (a, b) (Event c)
       -> (Wire m a b -> c -> Wire m a b)
       -> Wire m a b
kSwitch sf test gen = dSwitch id $ feedback sf $ effect $ \(x, w) =>
  do (sf, b) <- stepWire w x
     (st, c) <- stepWire test (x, b)
     case c of
          Now c  => do (sn, b) <- stepWire (gen sf c) x; pure ((b, Now sn), sn)
          NotNow => pure ((b, NotNow), sf)

dkSwitch : Monad m
        => Wire m a b
        -> Wire m (a, b) (Event c)
        -> (Wire m a b -> c -> Wire m a b)
        -> Wire m a b
dkSwitch sf test gen = dSwitch (uncurry gen) $ feedback sf $ effect $ \(x, w) =>
  do (ss, b) <- stepWire w x
     (st, c) <- stepWire test (x, b)
     case c of
          Now c  => pure ((b, Now (ss, c)), ss)
          NotNow => pure ((b, NotNow), ss)

||| Parallel switch
||| + switch: once, now, reset
||| + inhibits: same as first given wire
pSwitch : (Monad m, Traversable f)
       => ({sf:_} -> a -> f sf -> f (sf, b))
       -> f (Wire m b c)
       -> Wire m (a, f c) (Event d)
       -> (f (Wire m b c) -> d -> Wire m a (f c))
       -> Wire m a (f c)
pSwitch tran col test k = switch id $ feedback col $ effect $ \(x, co) =>
  do sfs <- traverse (map (map (Force . Force) . swap) . uncurry stepWire) (tran x co)
     let cs = map fst sfs
     let ws = map snd sfs
     (sf, d) <- stepWire test (x, cs)
     case d of
          NotNow => pure ((cs, NotNow), ws)
          Now d  => do (sf, cs) <- stepWire (k ws d) x
                       pure ((cs, Now sf), ws)

||| Parallel switch in the next frame
||| + switch: once, next, reset
||| + inhibits: same as first given wire
dpSwitch : (Monad m, Traversable f)
       => ({sf:_} -> a -> f sf -> f (sf, b))
       -> f (Wire m b c)
       -> Wire m (a, f c) (Event d)
       -> (f (Wire m b c) -> d -> Wire m a (f c))
       -> Wire m a (f c)
dpSwitch tran col test k = dSwitch id $ feedback col $ effect $ \(x, col) =>
  do sfs <- traverse (map (map (Force . Force) . swap) . uncurry stepWire) (tran x col)
     let cs = map fst sfs
     let ws = map snd sfs
     (sf, d) <- stepWire test (x, cs)
     case d of
          NotNow => pure ((cs, NotNow), ws)
          Now d  => pure ((cs, Now (k ws d)), ws)

infixr 1 </>
(</>) : Monad m => Wire m a (Event b) -> Wire m a b -> Wire m a b
(</>) = alt

(<|>) : Monad m => Wire m a (Event b) -> Wire m a (Event b) -> Wire m a (Event b)
(<|>) = altE

infixl 6 ->>
(->>) : Monad m => Wire m a (Event b) -> Wire m a b -> Wire m a b
(->>) = become

(>>) : Monad m => Wire m a (Event b) -> Wire m a (Event b) -> Wire m a (Event b)
(>>) = becomeE

