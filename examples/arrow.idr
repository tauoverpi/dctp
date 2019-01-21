-- -*- coding: utf-8 -*-
-- Copyright: © 2019 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module Main

import DCTP
import DCTP.Syntax
import Control.Arrow
import Control.Category

%default total
%access public export

program : Wire IO () (Event ())
program =
  let attempts = pure (the Int 1) >>> accum (+) 0
      rng      = attempts >>> clip 0 100 (id*id + id)
      prompt   = eff (putStr "guess: ") >>> eff getLine
      print    = effect putStrLn
      failtext = pure "wrong! was " <+> map show rng <+> pure ". try again"
             >>> print
             >>> pure NotNow
      wintext  = pure "you win" >>> print >>> pure (Now ())
  in ifW (liftA2 (==) (map cast prompt) rng)
         then wintext
         else failtext

covering
main : IO ()
main = control program
