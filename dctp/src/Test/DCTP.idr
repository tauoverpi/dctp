-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module Test.DCTP

import DCTP
import DCTP.Collection
import DCTP.Switch
import DCTP.Trans
import DCTP.Varying
import DCTP.Time
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Arrow
import Control.Category
import Test.Unit
import Data.SortedMap
import Data.IORef

%default total
%access public export

-- UTILS -----------------------------------------------------------------------

Show a => Show (Event a) where
  show (Now a) = "[now: " ++ show a ++ "]"
  show NotNow  = "[not now]"

Eq a => Eq (Event a) where
  (Now a) == (Now b) = a == b
  NotNow  == NotNow  = True
  _       == _       = False

traceWire : Wire IO a b -> List a -> IO (List b)
traceWire w n = go n id w
  where go : List a -> (List b -> List b) -> Wire IO a b -> IO (List b)
        go [] acc sf = pure (acc [])
        go (x::xs) acc sf =
          do (sf, b) <- stepWire sf x
             go xs (acc . (b::)) sf

equal : (Eq b, Show b)
       => String
       -> Wire IO a b
       -> (given : List a)
       -> (expected : List b)
       -> IO Bool
equal title program given expected =
  genericTest (Just title) !(traceWire program given) expected (==)

-- TESTS -----------------------------------------------------------------------

testDelay : IO Bool
testDelay =
  let program  = delay 0 (pure 1)
      input    = [(),(),()]
      expected = [0,1,1]
  in equal "delay" program input expected

testAccum : IO Bool
testAccum =
  let program  = accum (+) 0
      input    = [1,1,1,1,1]
      expected = [1,2,3,4,5]
  in equal "accum" program input expected

testPredicate : IO Bool
testPredicate =
  let program  = predicate (==1)
      input    = [0,1,8,1]
      expected = [Right 0, Left 1, Right 8, Left 1]
  in equal "predicate" program input expected

testEffect : IO Bool
testEffect =
  let program  = effect pure
      input    = [1,2,3,4]
      expected = [1,2,3,4]
  in equal "effect" program input expected

testHold : IO Bool
testHold =
  let program  = hold 0
      input    = [NotNow, Now 1, NotNow, Now 2, NotNow]
      expected = [0,1,1,2,2]
  in equal "hold" program input expected

testAccumE : IO Bool
testAccumE =
  let program  = accumE (+) 0
      input    = [Now 1, NotNow, NotNow, Now 1, NotNow]
      expected = [1,1,1,2,2]
  in equal "accumE" program input expected

testReset : IO Bool
testReset =
  let program  = reset (accum (+) 0)
      input    = [(1, NotNow),(1, NotNow),(1,Now ()),(1,NotNow),(1,NotNow)]
      expected = [1,2,1,2,3]
  in equal "reset" program input expected

testResetSelf : IO Bool
testResetSelf =
  let program  = resetSelf (accum (+) 0
                            >>> id &&& id
                            >>> second (predicate (>=3) >>> arrow Now \|/ never))
      input    = [1,1,1,1,1]
      expected = [1,2,3,1,2]
  in equal "resetSelf" program input expected

testBecome : IO Bool
testBecome =
  let program  = now 3 >> now 2 >> now 1 ->> pure 0
      input    = [(),(),(),(),()]
      expected = [3,2,1,0,0]
  in equal "become, becomeE" program input expected

testSwitch : IO Bool
testSwitch =
  let program  = switch id $ pure (1, Now (pure 2))
      input    = [(),(),()]
      expected = [2,2,2]
  in equal "switch" program input expected

testAlt : IO Bool
testAlt =
  let program  = now 1 <|> now 2 <|> now 3 </> pure 4
      input    = [(),(),(),(),()]
      expected = [1,2,3,4,4]
  in equal "alt, altE" program input expected

testDSwitch : IO Bool
testDSwitch =
  let program  = dSwitch id $ pure (1, Now (pure 2))
      input    = [(),(),()]
      expected = [1,2,2]
  in equal "dSwitch" program input expected

testRSwitch : IO Bool
testRSwitch =
  let program  = rSwitch (accum (+) 0)
      input    = [(1, NotNow), (2, NotNow), (3, Now (pure 0)), (4, NotNow)]
      expected = [1,3,0,0]
  in equal "rSwitch" program input expected

testDRSwitch : IO Bool
testDRSwitch =
  let program  = drSwitch (accum (+) 0)
      input    = [(1, NotNow), (2, NotNow), (3, Now (pure 0)), (4, NotNow)]
      expected = [1,3,6,0]
  in equal "rSwitch" program input expected

testKSwitch : IO Bool
testKSwitch =
  let program  = kSwitch {c=Int} (accum (+) 0)
                         (arrow (\(_,b) => if b >= 2 then Now 1 else NotNow))
                         (\sf, c => sf + pure 1)
      input    = [1,1,1,1]
      expected = [1,4,5,6]
  in equal "kSwitch" program input expected

testDKSwitch : IO Bool
testDKSwitch =
  let program  = dkSwitch {c=Int} (accum (+) 0)
                         (arrow (\(_,b) => if b >= 2 then Now 1 else NotNow))
                         (\sf, c => sf + pure 1)
      input    = [1,1,1,1]
      expected = [1,2,4,5]
  in equal "kSwitch" program input expected

testZipWire : IO Bool
testZipWire =
  let program  = zipWire 0 [accum (+) 0, id]
      input    = [[],[1,1],[1],[1,1]]
      expected = [[0,0],[1,1],[2,0],[3,1]]
  in equal "zipWire" program input expected

testDZipWire : IO Bool
testDZipWire =
  let program  = dZipWire 0 [accum (+) 0, id]
      input    = [[],[1,1],[1],[1,1]]
      expected = [[0,0],[0,0],[1,1],[2,0]]
  in equal "dZipWire" program input expected

testGather : IO Bool
testGather =
  let program  = gather {a=()} {k=Int} (\_ => now 0 >> now 1 >> now 2) >>> arrow toList
      input    = [(0,()),(0,()),(1,()),(0,()),(42,()),(0,())]
      expected = [[(0,0)],[(0,1)],[(1,0)],[(0,2)],[(42,0)],[]]
  in equal "gather" program input expected

testDynamic : IO Bool
testDynamic =
  let program  = dynamic {a=()} {k=Int} (\_ => now 0 >> now 1 >> now 2)
      input    = [(0,()), (1,()), (0,()), (0,()), (0,())]
      expected = [[0], [0,0], [1,0], [2,0], [0]]
  in equal "dynamic" program input expected

testParA : IO Bool
testParA =
  let program  = parA (\a => map (flip MkPair a)) [accum (+) 0, id]
      input    = [1,1,1,1,1]
      expected = [[1,1],[2,1],[3,1],[4,1],[5,1]]
  in equal "parA" program input expected

testAnimate : IO Bool
testAnimate =
  let program  = pure (pure 1) >>> animate
      input    = [(),(),()]
      expected = [1,1,1]
  in equal "animate" program input expected

testRunReader : IO Bool
testRunReader =
  let program  = runReaderW askW
      input    = [(1,1),(2,1),(3,1)]
      expected = [1,2,3]
  in equal "runReaderW" program input expected

testChangeV : IO Bool
testChangeV =
  let program  = changeV >>> arrow changed
      input    = [1,1,2,2,3,3]
      expected = [False,False,True,False,True,False]
  in equal "changeV" program input expected

testAnimateV : IO Bool
testAnimateV =
  do ref <- newIORef (the Int 0)
     let program  = animateV (const $ do modifyIORef ref (+1); readIORef ref)
                    >>> arrow value
     let input    = map (flip MkVarying ()) [False,False,True,False,True,False]
     let expected = [1,1,2,2,3,3]
     equal "animateV" program input expected

testFor : IO Bool
testFor =
  do ref <- newIORef (the Int 0)
     let clock    = do modifyIORef ref (+1); readIORef ref
     let program  = for clock 3
     let input    = [1,1,1,1,1]
     let expected = [Now 1, Now 1, Now 1, NotNow, NotNow]
     equal "for" program input expected

testAfter : IO Bool
testAfter =
  do ref <- newIORef (the Int 0)
     let clock    = do modifyIORef ref (+1); readIORef ref
     let program  = after clock 3
     let input    = [1,1,1,1,1]
     let expected = [NotNow, NotNow, NotNow, Now 1, Now 1]
     equal "after" program input expected

testEvery : IO Bool
testEvery =
  do ref <- newIORef (the Int 0)
     let clock    = do modifyIORef ref (+1); readIORef ref
     let program  = every clock 1
     let input    = [1,1,1,1,1]
     let expected = [NotNow, Now 1, NotNow, Now 1, NotNow]
     equal "every" program input expected

-- RUNNER ----------------------------------------------------------------------

tests : IO ()
tests = runTests
  -- Core
  [ testAccum
  , testHold
  , testAccumE
  -- Switch
  , testReset
  , testResetSelf
  , testBecome
  , testAlt
  , testSwitch
  , testDSwitch
  , testRSwitch
  , testDRSwitch
  , testKSwitch
  , testDKSwitch
  -- Collection
  , testZipWire
  , testDZipWire
  , testGather
  , testDynamic
  , testParA
  -- Controller
  , testAnimate
  -- Trans
  , testRunReader
  -- Varying
  , testChangeV
  , testAnimateV
  -- Time
  , testFor
  , testAfter
  , testEvery
  ]
