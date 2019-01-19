-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Core

import Control.Arrow
import Control.Category
import Control.Monad.Identity
import Control.Monad.Syntax

%default total
%access public export

data Event a
  = NotNow
  | Now a

data Wire : (m : Type -> Type) -> (a, b : Type) -> Type where
  ||| Generic opaque pure wire for when there's no other suitable wire
  WGen     : (a -> (Inf $ Lazy $ Wire m a b, b)) -> Wire m a b
  ||| Pure function without any state, possible to compose
  WArr     : (a -> b) -> Wire m a b
  ||| Constant wire
  WConst   : b -> Wire m a b
  ||| Composition, transformations performed for reducing the program
  ||| graph size aim to eliminate this.
  WComp    : Wire m b c -> Wire m a b -> Wire m a c
  ||| Identity wire, safe to remove
  WId      : Wire m a a
  ||| Stateful wire
  WLoop    : c -> Wire m (a, c) (b, c) -> Wire m a b
  ||| Switch in the current frame
  WSwitch  : (c -> Wire m a b) -> Wire m a (b, Event c) -> Wire m a b
  ||| Switch in the next frame
  WDSwitch : (c -> Wire m a b) -> Wire m a (b, Event c) -> Wire m a b
  ||| Lift a monadic effect into a wire network
  WEff     : (a -> m b) -> Wire m a b

Wire' : (a, b : Type) -> Type
Wire' = Wire Identity

WireM : (Type -> Type) -> Type -> Type
WireM m b = ArrowMonad (Wire m) b

||| Step a single frame of the wire network within some monad
stepWire : Monad m => Wire m a b -> a -> m (Inf $ Lazy $ Wire m a b, b)
stepWire w x =
  case w of
       WGen f => pure (f x)
       WArr f => pure (WArr f, f x)
       WConst x => pure (WConst x, x)
       -- Left identity
       WComp WId sf => stepWire sf x
       -- Right identity
       WComp sf WId => stepWire sf x
       -- Function composition
       WComp (WArr f) (WArr g) =>
        let k = f . g in pure (WArr k, k x)
       -- Constant folding
       WComp (WArr f) (WConst x) =>
        let r = f x in pure (WConst r, r)
       -- Constant elimination
       WComp (WConst x) (WConst _) =>
        pure (WConst x, x)
       -- Effect composition
       WComp (WEff m) (WEff m') =>
        do let mm' = m' >=> m
           x <- mm' x
           pure (WEff mm', x)
       WComp sf sg =>
        do (sg, b) <- stepWire sg x
           (sf, c) <- stepWire sf b
           pure (WComp sf sg, c)
       WId => pure (WId, x)
       -- Loop fusion
       WLoop c (WLoop c' sf) =>
        do (sf, ((b, c), c')) <- stepWire sf ((x, c), c')
           let aw = (WComp (WArr (\((b,c),c') => (b,c,c'))) sf)
           let wa = (WComp aw (WArr (\(b,c,c') => ((b,c),c'))))
           pure (WLoop (c, c') wa, b)
       WLoop c sf =>
        do (sf, x, c) <- stepWire sf (x, c)
           pure (WLoop c sf, x)
       WSwitch gen sf =>
        do (sf, x', c) <- stepWire sf x
           case c of
                NotNow => pure (WSwitch gen sf, x')
                Now c  => stepWire (gen c) x
       WDSwitch gen sf =>
        do (sf, x', c) <- stepWire sf x
           case c of
                NotNow => pure (WDSwitch gen sf, x')
                Now c  => pure (gen c, x')
       WEff m =>
        do x <- m x
           pure (WEff m, x)

Category (Wire m) where
  id = WId
  (.) = WComp

Monad m => Arrow (Wire m) where
  arrow = WArr

  first WId = WId
  first sf = WLoop sf $ WEff $ \((x, c), sf) =>
    do (sf, x) <- stepWire sf x
       pure ((x, c), sf)

  second WId = WId
  second sf = WLoop sf $ WEff $ \((c, x), sf) =>
    do (sf, x) <- stepWire sf x
       pure ((c, x), sf)

  WId *** WId = WId
  (WConst x) *** (WConst y) = WConst (x, y)
  sf *** sg = WLoop (sf, sg) $ WEff $ \((x, y), sf, sg) =>
    do (sf, x) <- stepWire sf x
       (sg, y) <- stepWire sg y
       pure ((x, y), sf, sg)

Monad m => ArrowChoice (Wire m) where

  left WId = WId
  left sf = WLoop sf $ WEff $ \(x, sf) =>
    case x of
         Left l  => do (sf, l) <- stepWire sf l; pure (Left l, sf)
         Right r => pure (Right r, sf)

  right WId = WId
  right sf = WLoop sf $ WEff $ \(x, sf) =>
    case x of
         Left l  => pure (Left l, sf)
         Right r => do (sf, r) <- stepWire sf r; pure (Right r, sf)

  WId +++ WId = WId
  sf +++ sg = WLoop (sf, sg) $ WEff $ \(x, sf, sg) =>
    case x of
         Left l  => do (sf, l) <- stepWire sf l; pure (Left l, sf, sg)
         Right r => do (sg, r) <- stepWire sg r; pure (Right r, sf, sg)

Monad m => ArrowApply (Wire m) where
  app = WEff $ \(sf, x) => snd <$> stepWire sf x

Monad m => Functor (Wire m a) where
  map f (WArr g)        = arrow (f . g)
  map f (WConst x)      = WConst (f x)
  map f WId             = arrow f
  map f sf              = sf >>> arrow f

Monad m => Applicative (Wire m a) where
  pure = WConst
  (WArr f)   <*> (WConst x) = arrow (flip f x)
  (WConst f) <*> (WConst x) = pure (f x)
  WId        <*> (WConst x) = arrow (flip apply x)
  (WConst f) <*> WId        = arrow f
  f <*> x                   = f &&& x >>> arrow (uncurry apply)

(Monad m, Num b) => Num (Wire m a b) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  fromInteger = pure . fromInteger

(Monad m, Neg b) => Neg (Wire m a b) where
  (-) = liftA2 (-)
  negate = map negate

(Monad m, Abs b) => Abs (Wire m a b) where
  abs = map abs

(Monad m, Integral b) => Integral (Wire m a b) where
  div = liftA2 div
  mod = liftA2 mod

(Monad m, Fractional b) => Fractional (Wire m a b) where
  (/) = liftA2 (/)
  recip = map recip

(Monad m, Semigroup b) => Semigroup (Wire m a b) where
  (<+>) = liftA2 (<+>)

(Monad m, Monoid b) => Monoid (Wire m a b) where
  neutral = pure neutral

||| Introduce state to a given wire
feedback : c -> Wire m (a, c) (b, c) -> Wire m a b
feedback = WLoop

||| Delay the input stream by one frame
delay : Monad m => b -> Wire m a b -> Wire m a b
delay b sf = feedback b (first sf >>> arrow swap)

||| Accumulate a result with a given function and starting point
accum : Monad m => (a -> b -> b) -> b -> Wire m a b
accum plus b = feedback b (arrow (uncurry plus) >>> id &&& id)

||| Lift a predicate to wires
predicate : Monad m => (a -> Bool) -> Wire m a (Either a a)
predicate p = arrow (\x => if p x then Left x else Right x)

||| Run a monadic effect as a wire
effect : (a -> m b) -> Wire m a b
effect = WEff

eff : m b -> Wire m a b
eff = effect . const

||| Clamp the output stream between a given range
clamp : (Monad m, Ord a) => a -> a -> Wire m a a -> Wire m a a
clamp l u w = w >>> predicate (\x => x < l)
                >>> pure l \|/ (predicate (\x => x > u) >>> pure u \|/ id)

wire : Monad m => Wire m a b -> a -> WireM m b
wire w a = MkArrowMonad (pure a >>> w)

infixl 1 -<
(-<) : Monad m => Wire m a b -> a -> WireM m b
(-<) = wire
