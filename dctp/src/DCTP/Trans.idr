-- -*- coding: utf-8 -*-
-- Copyright: © 2019 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Trans

import DCTP.Core
import DCTP.Controller
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Arrow
import Control.Category

%default total
%access public export

asksW : MonadReader r m => Wire m (r -> b) b
asksW = arrow asks >>> animate

askW : MonadReader r m => Wire m a r
askW = arrow (const ask) >>> animate

hoistW : (Monad m', Monad m)
      => (a -> a')
      -> ({x:_} -> a -> m' x -> m x)
      -> Wire m' a' b
      -> Wire m a b
hoistW f trans sf = feedback sf $ effect $ \(x, sf) =>
  do (sf, b) <- trans x (stepWire sf (f x))
     pure (b, sf)

runReaderW : Monad m => Wire (ReaderT e m) a b -> Wire m (e, a) b
runReaderW = hoistW snd $ \x, c => runReaderT c (fst x)

generalize : Monad m => Wire' a b -> Wire m a b
generalize sf = feedback sf $ effect $ \(x, sf) =>
  do let (sf, b) = runIdentity $ stepWire sf x
     pure (b, sf)

