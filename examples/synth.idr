-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module Main

import DCTP
import DCTP.Time
import DCTP.Trans
import Control.Arrow
import Control.Category
import Control.Monad.Reader
import Control.Monad.Identity

%default total
%access public export

Bytebeat : Type
Bytebeat = Wire (ReaderT Bits32 Identity) Bits32 Bits32

infixr 4 .|.
(.|.) : Bytebeat -> Bytebeat -> Bytebeat
(.|.) = liftA2 prim__orB32

infixr 5 .&.
(.&.) : Bytebeat -> Bytebeat -> Bytebeat
(.&.) = liftA2 prim__andB32

infixr 6 .>>., .<<.
(.>>.) : Bytebeat -> Bytebeat -> Bytebeat
(.>>.) = liftA2 prim__lshrB32

(.<<.) : Bytebeat -> Bytebeat -> Bytebeat
(.<<.) = liftA2 prim__shlB32

infixr 7 .%.
(.%.) : Bytebeat -> Bytebeat -> Bytebeat
a .%. b = assert_total
  (b >>> predicate (==0) >>> pure 0 \|/ liftA2 prim__uremB32 a b)

time : Bytebeat
time = askW

triangle : Bytebeat
triangle = time .&. (time .>>. 8)

odd : Bytebeat
odd = time .>>. time

chaotic : Bytebeat
chaotic = (time .>>. (pure 8 .&. time)) * time

ambient : Bytebeat
ambient = (time .>>. (pure 8 .&. time)) * (time .>>. (pure 15 .&. time))

what : Bytebeat
what = time .%. ((time .>>. pure 8) .|. (time .>>. pure 16))

glitchcore : Bytebeat
glitchcore =
  liftA2 prim__subB32
    (((time .%. (time >>> pure 16) .|. (time .>>. pure 8)) .>>. pure 2) .&. time)
    1

covering
writeWire : Bytebeat -> IO ()
writeWire w =
     control $
      let count = pure (the Bits32 1) >>> accum (+) 0
          track = (count &&& pure 0) >>> generalize (runReaderW w)
      in map (chr . prim__zextB32_Int) track
         >>> effect putChar
         >>> pure NotNow

help : IO ()
help = putStrLn """
usage: synth track

tracks:
  triangle
  odd
  chaotic
  ambient
  what
  glitchcore
"""

select : String -> Bytebeat
select "triangle"   = triangle
select "odd"        = odd
select "chaotic"    = chaotic
select "ambient"    = ambient
select "what"       = what
select "glitchcore" = glitchcore
select _            = time

partial
main : IO ()
main = case !getArgs of
            [_, track] => writeWire (select track)
            _ => help
