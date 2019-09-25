{-# LANGUAGE NoImplicitPrelude #-}

module Compiler.IO (unsafeInterleaveIO,
                    unsafePerformIO)
    where

import Compiler.Base -- for seq, IO = IOActionX, LazyIO, IOAndPass, MFIX, IOReturn
import Data.Tuple    -- for snd
import Compiler.ST

unsafeInterleaveIO x = LazyIO x

unsafePerformIO x = case run_state 0 x of (s',x') -> s' `seq` x'
