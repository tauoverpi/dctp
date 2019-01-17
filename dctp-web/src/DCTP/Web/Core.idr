-- -*- coding: utf-8 -*-
-- Copyright: © 2018 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module Main

import DCTP
import DCTP.Switch
import DCTP.Event
import DCTP.Trans
import DCTP.Varying
import Control.Monad.Reader
import Control.Arrow
import Control.Category
import Control.Monad.Identity
import Control.Monad.Trans
import Data.IORef

%default total
%access public export

---- TYPES ---------------------------------------------------------------------

data Element = MkElement Ptr
data WebEvent = OnClick | OnMouseMove

DTime : Type
DTime = Int

Show WebEvent where
  show OnClick = "click"
  show OnMouseMove = "mousemove"

---- PRIMITIVES ----------------------------------------------------------------

document : Element
document = MkElement (unsafePerformIO (foreign FFI_JS "document" (JS_IO Ptr)))
%freeze document

addEventListener : Element -> WebEvent -> Bool -> (Ptr -> JS_IO ()) -> JS_IO ()
addEventListener (MkElement ptr) event bubbles handler = assert_total $
  foreign FFI_JS "%0.addEventListener(%1, %2, %3)"
          (Ptr -> String -> JsFn (Ptr -> JS_IO ()) -> Int -> JS_IO ())
          ptr (show event) (MkJsFn handler) (if bubbles then 1 else 0)

requestAnimationFrame : (() -> JS_IO ()) -> JS_IO ()
requestAnimationFrame fn = assert_total $
  foreign FFI_JS "requestAnimationFrame(%0)"
          (JsFn (() -> JS_IO ()) -> JS_IO ())
          (MkJsFn fn)

---- FRAMEWORK -----------------------------------------------------------------

namespace Core

  Web : Type -> Type -> Type -> Type
  Web sub = Wire (ReaderT sub Identity)

  runWeb : Monad m => Web e a b -> Wire m (e, a) b
  runWeb _w = feedback _w $ effect runner
    where runner ((e, a), w) =
            do let (w, b) = runIdentity (runReaderT (stepWire w a) e)
               pure (b, w)

  covering
  controlWeb : Wire JS_IO () () -> JS_IO ()
  controlWeb _w = go _w ()
    where go w () =
            do (w, _) <- stepWire w ()
               requestAnimationFrame (go w)

---- SUBSCRIPTIONS

namespace Sub

  Sub : Type -> Type -> Type
  Sub = Wire JS_IO

  epochTime : Sub a Int
  epochTime = effect . const $ foreign FFI_JS "Date.now()" (JS_IO Int)

  performanceNow : Sub a Double
  performanceNow = effect . const $ foreign FFI_JS "performance.now()" (JS_IO Double)

  mkSubHandler : (elem : Element)
              -> (event : WebEvent)
              -> (default : a)
              -> (after : IORef a -> JS_IO ())
              -> (handler : IORef a -> Ptr -> JS_IO ())
              -> Sub x a
  mkSubHandler elem event def after handler {a} = switch id $ effect $ \_ =>
    do ref <- newIORef' def
       addEventListener elem event False (handler ref)
       pure (def, Now (wire ref))
    where wire : IORef a -> Sub x a
          wire ref = effect $ \_ =>
            do r <- readIORef' ref
               after ref
               pure r

  MouseXY : Type
  MouseXY = Pair Int Int

  mouseXY : Sub a (Varying MouseXY) -- varying to avoid recomputing
  mouseXY = mkSubHandler document OnMouseMove default after $ \ref, p =>
    do x <- foreign FFI_JS "%0.clientX" (Ptr -> JS_IO Int) p
       y <- foreign FFI_JS "%0.clientY" (Ptr -> JS_IO Int) p
       writeIORef' ref (MkVarying True (x, y))
    where default = MkVarying False (0,0)
          after ref = modifyIORef' ref (record {changed = False})

  mouseClickXY : Sub a (Event MouseXY)
  mouseClickXY = mkSubHandler document OnClick NotNow after $ \ref, p =>
      do x <- foreign FFI_JS "%0.clientX" (Ptr -> JS_IO Int) p
         y <- foreign FFI_JS "%0.clientY" (Ptr -> JS_IO Int) p
         writeIORef' ref (Now (x, y))
    where after = flip writeIORef' NotNow

---- WIRES

namespace Wire

  ||| Compute the integral of a given initial value and a time source
  integral : (Monad m, Num a) => (source : m a) -> a -> Wire m a a
  integral time init = feedback init (effect (const time) &&& id >>> arrow sum)
    where sum (dt, dx, x) = (x, x + dt * dx)

  ||| Clip framerate in respect to a given time source
  framerate : (Monad m, Num a, Ord a) => m a -> a -> Wire m b (Event b)

  ||| Compute delta time
  dt : (Monad m, Neg b) => m b -> Wire m a b
  dt tm {b} = switch id $ effect $ \_ =>
    do (_, t) <- stepWire time ()
       pure (0, Now (dt' t))
    where time : Num b => Wire m a b
          time = effect (const tm)
          dt' : Neg b => b -> Wire m a b
          dt' t = time >>> arrow (flip (-) t)

---- DEBUGGER

namespace Debug

  Recording : (Type -> Type) -> Type -> Type -> Type
  Recording m a b = List (Wire m a b)

  ||| Record inputs, outputs, and the network state. Only works for pure wires.
  ||| @limit max number of frames to keep in memory, pass nothing for unbounded
  rec : Monad m => (limit : Maybe Integer)
                -> Wire m a b
                -> Wire m a (b, Recording m a b)

  ||| Replay a recording of a wire
  replay : Monad m => Recording m a b -> Wire m a (Event b)

  ||| Replay a recording in reverse order
  rewind : Monad m => Recording m a b -> Wire m a (Event b)

---- RENDERING -----------------------------------------------------------------

data HtmlTag = Div | Span
data HtmlEvent a = MkHEvent a
Attribute : Type
Attribute = List (String, String)
data Html : Type -> Type where
  HtmlElem : HtmlTag
          -> List Attribute
          -> List (HtmlEvent a)
          -> List (Html a)
          -> Html a
  HtmlText : String -> Html a

style : (List Attribute -> List Attribute) -> Html a -> Html a
style f (HtmlElem x xs ys zs) = HtmlElem x (f xs) ys zs
style f x = x

---- TAGS

decl syntax htmltag {name} [tag] =
  ||| Html element constructor
  name : HtmlTag
      -> (events : List (HtmlEvent a))
      -> (nodes : List (Html a))
      -> Html a
  name t = HtmlElem t []

htmltag div Div
htmltag span Span

text : String -> Html a
text = HtmlText

---- COMPILE

compile : Html a -> Wire JS_IO () (Event a)

---- SIMPLE GAME ---------------------------------------------------------------

namespace SimpleGame

  record SimpleGame where
    constructor MkSG
    time   : Double
    cursor : MouseXY

  Game : Type -> Type -> Type
  Game = Wire (ReaderT SimpleGame Identity)

---- DEMO ----------------------------------------------------------------------

record App sub input output where
  constructor MkApp
  subscriptions : Sub x sub
  application   : Web sub input output
  view          : Html input

main : JS_IO ()
