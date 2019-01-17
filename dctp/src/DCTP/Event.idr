-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Event

import DCTP.Core
import Control.Arrow
import Control.Category

%default total
%access public export

event : b -> (a -> b) -> Event a -> b
event b f NotNow = b
event b f (Now a) = f a

Functor Event where
  map f NotNow = NotNow
  map f (Now a) = Now (f a)

Applicative Event where
  pure = Now
  (Now f) <*> (Now x) = Now (f x)
  _       <*> _       = NotNow

Monad Event where
  join (Now a) = a
  join _       = NotNow

hold : Monad m => a -> Wire m (Event a) a
hold a = feedback a (arrow sum)
  where sum (NotNow, a) = (a, a)
        sum (Now a , _) = (a, a)

hold' : Monad m => a -> Wire m (Event a) a
hold' a = delay a (hold a)

never : Wire m a (Event b)
never = WConst NotNow

now : b -> Wire m a (Event b)
now b = WGen $ \_ => (never, Now b)

one : Wire m a (Event a)
one = WGen $ \x => (never, Now x)

accumE : Monad m => (a -> b -> b) -> b -> Wire m (Event a) b
accumE plus b = feedback b (arrow sum)
  where sum (NotNow, b) = (b, b)
        sum (Now a , b) = let r = plus a b in (r, r)

filterE : Monad m => (a -> Bool) -> Wire m a (Event a)
filterE p = arrow $ \x => if p x then Now x else NotNow

eventE : Monad m => Wire m (Event a) (Either a ())
eventE = arrow $ \x => case x of
                            NotNow => Right ()
                            Now c  => Left c

onEvent : Monad m => Wire m a b -> Wire m (Event a) (Event b)
onEvent sf = eventE >>> (sf >>> arrow Now) \|/ pure NotNow

infixr 1 -?>
(-?>) : Monad m => Wire m a (Event b) -> Wire m b c -> Wire m a (Event c)
e -?> s = e >>> onEvent s

||| Clip if the given value is outside given bounds
clip : (Monad m, Ord a) => a -> a -> Wire m a a -> Wire m a (Event a)
clip l u w = w >>> predicate (\x => x < l || x > u) >>> never \|/ arrow Now

