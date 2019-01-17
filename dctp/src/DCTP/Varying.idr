-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Varying

import DCTP.Core
import DCTP.Event
import DCTP.Switch
import Control.Arrow

%default total
%access public export

record Varying a where
  constructor MkVarying
  changed : Bool
  value   : a

Functor Varying where
  map f (MkVarying c v) = MkVarying c (f v)

Applicative Varying where
  pure = MkVarying False
  (MkVarying c f) <*> (MkVarying c' x) =
    MkVarying (c || c') (f x)

Monad Varying where
  join (MkVarying c (MkVarying c' x)) = MkVarying (c || c') x

Num a => Num (Varying a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  fromInteger = pure . fromInteger

Neg a => Neg (Varying a) where
  (-) = liftA2 (-)
  negate = map negate

Abs a => Abs (Varying a) where
  abs = map abs

Integral a => Integral (Varying a) where
  div = liftA2 div
  mod = liftA2 mod

Fractional a => Fractional (Varying a) where
  (/) = liftA2 (/)
  recip = map recip

holdV : Monad m => a -> Wire m (Event a) (Varying a)
holdV a = feedback a $ arrow sum
  where sum (NotNow, c) = (MkVarying False c, c)
        sum (Now c , _) = (MkVarying True  c, c)

changeV : (Monad m, Eq a) => Wire m a (Varying a)
changeV = WGen $ \x => (next x, MkVarying False x)
  where next x = feedback x $ arrow $ \(a, c) =>
          if a /= c then (MkVarying True  a, a)
                    else (MkVarying False c, c)

accumV : Monad m => (a -> b -> b) -> b -> Wire m (Event a) (Varying b)
accumV plus b = feedback b $ arrow sum
  where sum (NotNow, c) = (MkVarying False c, c)
        sum (Now a , c) = let r = plus a c in (MkVarying True r, r)

varyingE : Monad m => Wire m (Varying a) (Event a)
varyingE = arrow $ \x => if changed x then Now (value x) else NotNow

animateV : Monad m => (a -> m b) -> Wire m (Varying a) (Varying b)
animateV f = switch id $ effect $ \x =>
  do b <- f (value x); pure (MkVarying True b, Now (aniV b))
  where aniV : Monad m => b -> Wire m (Varying a) (Varying b)
        aniV v = feedback v $ effect $ \(x, c) =>
          if changed x
             then do b <- f (value x); pure (MkVarying True b, b)
             else pure (MkVarying False c, c)
