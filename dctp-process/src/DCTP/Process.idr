-- -*- coding: utf-8 -*-
-- Copyright: © 2019 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Process

import DCTP
import DCTP.Switch
import DCTP.Event
import DCTP.Syntax
import DCTP.Collection
import System.Concurrency.Raw
import Control.Category
import Control.Arrow
import Data.SortedMap

%default total
%access public export

||| Spawn a thread which runs a given wire in a loop. If the given wire inhibits
||| the thread is killed. If there are no messages from the parent thread it's
||| passed NotNow to allow for computation to continue.
thread : Wire IO (Event a) (Event b) -> Wire IO (Event a) (Event b)
thread w = switch id $ effect $ \x =>
  do pid <- fork proc
     False <- nullPtr pid         | _ => pure (NotNow, Now never)
     cid <- sendToThread pid 0 () | 0 => pure (NotNow, Now never)
     pure (NotNow, Now (wire pid cid))

  where procSend : Ptr -> Int -> b -> IO ()
        procSend pid cid val = sendToThread pid cid val *> pure ()

        procGet : Ptr -> Int -> IO (Event a)
        procGet pid cid = maybe NotNow Now <$> getMsgFrom pid cid

        wireSend : Ptr -> Int -> a -> IO Bool
        wireSend pid cid val = (==0) <$> sendToThread pid cid val

        wireGet : Ptr -> Int -> IO (Event b)
        wireGet pid cid = join . maybe NotNow Now <$> getMsgFrom pid cid

        -- It's safe to assert totality here even if the function itself
        -- is partial due to it running on another thread.
        proc : IO ()
        proc = assert_total $
          do checkMsgsTimeout 5
             Just (pid, cid) <- listenMsgs | _ => stopThread
             let send  = effect (procSend pid cid)
             let recv  = eff (procGet pid cid)
             let check = eff (checkMsgsFrom pid cid)
             let die   = eff stopThread
             let proc  = (w ->> die) >>> send >>> pure NotNow
             control $ ifW check
                           then recv >>> proc
                           else pure NotNow >>> proc

        wire : (pid : Ptr) -> (cid : Int) -> Wire IO (Event a) (Event b)
        wire pid cid =
          let send  = effect (wireSend pid cid)
              recv  = eff (wireGet pid cid)
              check = eff (checkMsgsFrom pid cid)
          in onEvent send >>> decide check recv (pure NotNow)
