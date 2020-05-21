module Main where

import Probability

import Data.ReadFile

xs = read_file_as_double "xs"

n_points = length xs

cluster_dist = do
  mean <- normal 0.0 10.0
  prec <- gamma 1.0 1.0
  let sigma = 1.0/prec
  return $ normal mean sigma

model = do
  alpha <- gamma 0.5 10.0
  dists <- dp n_points alpha cluster_dist
  return (dists, ["alpha" %=% alpha])

main = do

  (dists, loggers) <- random $ model

  observe (independent dists) xs

  return loggers