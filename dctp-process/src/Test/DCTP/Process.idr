-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module Test.DCTP.Process

import DCTP
import DCTP.Process
import Control.Category
import Control.Arrow
import Test.Unit

%default total
%access public export

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

testThread : IO Bool
testThread =
  pure True <* traceWire (thread (effect print >>> pure (Now ()))) (map Now [1,2,3,4,5])

tests : IO ()
tests = runTests
  [ testThread
  ]
