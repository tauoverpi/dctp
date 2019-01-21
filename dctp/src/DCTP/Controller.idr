-- -*- coding: utf-8 -*-
-- Copyright: © 2019 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Controller

import DCTP.Core
import DCTP.Event

%default total
%access public export

animate : Functor m => Wire m (m a) a
animate = effect id

covering
control : Monad m => Wire m () (Event b) -> m b
control sf =
  do (_, Now b) <- stepWire sf () | (sf, _) => control sf
     pure b

trace : Monad m => Nat -> Wire m () (Event b) -> m (Maybe b)
trace Z sf =
  do (_, Now b) <- stepWire sf () | _ => pure Nothing
     pure (Just b)
trace (S n) sf =
  do (sf, Now b) <- stepWire sf () | (sf, _) => trace n sf
     pure (Just b)
