{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes, TypeApplications #-}
module Security.Sec (Sec, sec, open, up
                    , declassify, endorse
                    )where

import Control.Monad
import Security.Lattice

newtype Sec s a = MkSec a

instance Monad (Sec s) where
  return = pure

  MkSec a >>= k =
    MkSec $ let MkSec b = k a in b

instance Functor (Sec s) where
  fmap = liftM

instance Applicative (Sec s) where
  pure = sec
  MkSec ab <*> MkSec a = MkSec (ab a)


--used to protect value `a`
sec :: a -> Sec s a
sec = MkSec

-- look at a protected value given
-- that you can produce a security
-- level `s`
open :: Sec s a -> s -> a
open (MkSec a) s = s `seq` a

up :: forall a sl sh . Less sl sh => Sec sl a -> Sec sh a
up (MkSec x) = (less @sl @sh) `seq` sech
  where
    sech = (MkSec x)

-- -- only for trusted code
-- reveal :: Sec s a -> a
-- reveal (MkSec x) = x

declassify :: Sec H a -> Sec L a
declassify (MkSec x) = (MkSec x)

endorse :: Sec L a -> Sec H a
endorse (MkSec x) = (MkSec x)
