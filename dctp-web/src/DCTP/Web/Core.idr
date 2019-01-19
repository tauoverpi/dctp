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
import Text.PrettyPrint.WL

%default total
%access public export

---- TYPES ---------------------------------------------------------------------

data Element = MkElement Ptr

data HtmlTag = Div | Span

Show HtmlTag where
  show Div = "div"
  show Span = "span"

DTime : Type
DTime = Int

data WebEvent = OnClick | OnMouseMove

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

createElement : HtmlTag -> JS_IO Element
createElement tag =
  do ptr <- foreign FFI_JS "document.createElement(%0)" (String -> JS_IO Ptr)
            (show tag)
     pure (MkElement ptr)

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

  ||| Clip framerate in respect to a given time source
  framerate : (Monad m, Num a, Ord a) => m a -> a -> Wire m b (Event b)

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

data HtmlEvent a = MkHEvent WebEvent a
Attribute : Type
Attribute = (String, String)
data Html : Type -> Type where
  HtmlElem : HtmlTag
          -> List Attribute
          -> List (HtmlEvent a)
          -> List (Html a)
          -> Html a
  HtmlText : String -> Html a

Show a => Show (HtmlEvent a) where
  show (MkHEvent e a) =
    "on" ++ show e ++ "=\"dctp_" ++ show e ++ "(" ++ show a ++ ")\""

Show a => Show (Html a) where
  show = toString . prettyHtml
    where prettyHtml : Show a => Html a -> Doc
          prettyHtml (HtmlText s) = text s
          prettyHtml (HtmlElem tag attr event html) =
            let events = concatMap ((" "++) . show) event
                attrs  = case attr of
                              [] => ""
                              _  => " style=\""
                                    ++ concatMap (\(a,b) => a ++ ": " ++ b ++ ";") attr
                                    ++ "\""
                open = angles $
                    text (show tag)
                    |+| text events
                    |+| text attrs
                content = assert_total (concatMap prettyHtml html)
                close = angles $
                    text "/" |+| text (show tag)
            in open |$| (indent 2 content) |$| close

style : (List Attribute -> List Attribute) -> Html a -> Html a
style f (HtmlElem x xs ys zs) = HtmlElem x (f xs) ys zs
style f x = x

---- TAGS

decl syntax htmltag {name} [tag] =
  ||| Html element constructor
  name : (events : List (HtmlEvent a))
      -> (nodes : List (Html a))
      -> Html a
  name = HtmlElem tag []

htmltag div Div
htmltag span Span

text : String -> Html a
text = HtmlText

render : Element -> Html a -> Html a -> JS_IO ()

---- COMPILE

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
