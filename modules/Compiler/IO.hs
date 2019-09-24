{-# LANGUAGE NoImplicitPrelude #-}

module Compiler.IO (unsafeInterleaveIO,
                    unsafePerformIO)
    where

import Compiler.Base -- for seq, IO = IOActionX, LazyIO, IOAndPass, MFIX, IOReturn
import Data.Tuple    -- for snd
import Compiler.ST

unsafeInterleaveIO x = LazyIO x

unsafePerformIO f = snd (run_state 0 f)
