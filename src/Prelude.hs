{-# LANGUAGE MagicHash #-}
module Prelude
  (module BasicPrelude,
   module Data.Semigroup,
   module Data.Foldable,
   Generic,
  --  module Lib.Pretty,
   module Text.PrettyPrint.ANSI.Leijen,
   module Control.Lens,
   module Control.Applicative,
   module Control.Category,
   IsString(..),
   module Data.Void,
   HashMap,
  --  PtrEq(..),
   unsafeCoerce,
   module Data.Hashable,
   module Data.Proxy,
   module Data.Constraint,
   module Control.Monad.Trans,
   module GHC.Exts,
   module Data.Type.Equality,
   module Data.Reflection,
   module Data.Coerce,
   module Debug.Trace,
   module Data.Maybe,
   module Control.Monad.State,
   module Control.Monad.Trans.Maybe,
   module Data.Functor.Compose,
   module Control.Monad.Fail,
   pack, unpack, module Data.Data,
   fromJust
    ) where


import BasicPrelude hiding ((\\),empty,(<>),uncons,(<.>),union,sum,product,concat,HashMap,fail)
import Data.Semigroup hiding (Arg(..))
import Data.Foldable -- hiding (toList)
import GHC.Generics (Generic)
import Control.Lens hiding (Level)
import Control.Applicative
import Data.String (IsString(..))
import Data.Void
import Data.HashMap.Lazy (HashMap)
import Unsafe.Coerce
import Data.Hashable
import Data.Proxy
import Data.Constraint hiding ((&&&),(***),trans)
import Control.Monad.Trans
import GHC.Exts (IsList(fromList),Proxy#,proxy#)
import Data.Type.Equality
import Data.Reflection
import Data.Coerce
import Debug.Trace
import Data.Maybe (fromMaybe)

import Control.Monad.State hiding (fail)
import Control.Monad.Trans.Maybe

import Data.Functor.Compose

-- import Lib.Pretty(Pretty(..),pretty,prettyPrint)
import Text.PrettyPrint.ANSI.Leijen (Doc)

-- import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

import Control.Category

import Data.List (sortBy)

import Control.Monad.Fail

import System.Mem.StableName
import System.IO.Unsafe

import Data.Data (Data)

-- newtype PtrEq a = PtrEq a

-- instance Eq (PtrEq a) where
--   PtrEq a == PtrEq b = unsafePerformIO $ do
--     na <- makeStableName $! a
--     nb <- makeStableName $! b
--     pure $! na == nb
-- instance Hashable (PtrEq a) where
--   hashWithSalt s (PtrEq a) = unsafePerformIO $ do
--     na <- makeStableName $! a
--     pure (hashStableName na `hashWithSalt` s)


pack :: IsString a => String -> a
pack = fromString

unpack :: Text -> String
unpack = T.unpack

-- instance (Pretty k, Pretty v, Ord k) => Pretty (HashMap k v) where
--   prettyPrec _ = pretty . sortOn fst . HM.toList


fromJust (Just x) = x
