-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Time

import DCTP.Core
import DCTP.Trans
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Category
import Control.Arrow

%default total
%access public export

Timed : (t : Type) -> (m : Type -> Type) -> (a, b : Type) -> Type
Timed t m a b = Wire (ReaderT t m) a b

timed : Monad m => Wire m a b -> Timed t m a b
timed {t} {m} sf = hoistW id {m'=m} {m=ReaderT t m} (const lift) sf

runTimedW : Monad m => Timed t m a b -> Wire m (t, a) b

time : Monad m => Timed t m a t
time = askW

for : Ord t => t -> Timed t m a b -> Timed t m a (Event b)

at : Eq t => t -> Timed t m a b -> Timed t m a (Event b)

after : Ord t => t -> Timed t m a b -> Timed t m a (Event b)

(<|>) : Monad m
     => Timed t m a (Event b)
     -> Timed t m a (Event b)
     -> Timed t m a (Event b)
