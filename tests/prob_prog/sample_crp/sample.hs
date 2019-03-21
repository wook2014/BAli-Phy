import Distributions

import Tree

main = do
  xs <- Lazy $ sample $ crp 2.0 10 2
  return $ log_all [ xs %% "xs"]

