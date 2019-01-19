-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module Main

import DCTP
import Control.Arrow
import Control.Category

%default total
%access public export

program : Wire IO () (Event ())
program =
  let attempts : Wire IO () Int    = accum (+) 0 . 1
      rng      : Wire IO () Int    = clamp 0 100 (id*id + id) . attempts
      prompt   : Wire IO () String = eff getLine . eff (putStr "guess: ")
      print    : Wire IO String () = effect putStrLn
      failtext = pure ()
             >>> pure "wrong! was " <+> map show rng <+> pure ". try again"
             >>> print
             >>> pure NotNow
      wintext  = pure "you win" >>> print >>> pure (Now ())
  in liftA2 (==) (map cast prompt) rng
     >>> predicate id
     >>> wintext \|/ failtext

covering
main : IO ()
main = control program
