{-# LANGUAGE NoImplicitPrelude #-}

module Compiler.ST (unsafeInterleaveST,
                    runST,
                    run_state)
    where

import Compiler.Base -- for seq, IO = IOActionX, LazyIO, IOAndPass, MFIX, IOReturn
import Data.Tuple    -- for snd

unsafeInterleaveST x = LazyIO x

run_state s  (IOAction f) = f s
run_state s  (LazyIO f) = run_state s f
run_state s0 (IOAndPass (LazyIO f) g) = let (_,x) = run_state s0 f in run_state s0 (g x)
run_state s0 (IOAndPass f g) = let (s1,x) = run_state s0 f in run_state s1 (g x)
run_state s  (MFix f) = let (s',x) = run_state s (f x) in (s',x)
run_state s  (IOReturn x) = (s,x)

runST' x = case run_state 0 x of (s',x') -> s' `join` x'

builtin reapply 2 "reapply" "Prelude"
runST x = reapply runST' x
