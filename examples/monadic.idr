-- -*- coding: utf-8 -*-
-- Copyright: © 2019 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module Main

import DCTP
import Control.Arrow
import Control.Category

%default total
%access public export

program : WireM IO (Event ())
program =
  do attempts <- accum (+) 0              -< the Int 1
     rng      <- clip 0 100 (id*id + id) -< attempts
     guess    <- prompt
     if cast guess == rng
        then print "you win" *> pure (Now ())
        else do print ("wrong! was " ++ show rng ++ ". try again")
                pure NotNow

  where prompt : WireM IO String
        prompt = (eff (putStr "guess: ") >>> eff getLine) -< ()

        print : String -> WireM IO ()
        print text = wire (eff (putStrLn text)) ()

covering
main : IO ()
main = control (runArrowMonad program)
