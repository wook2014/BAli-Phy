module IModel where
{
import Distributions;
import Tree;
  
builtin rs05_branch_HMM 5 "rs05_branch_HMM" "Alignment";
builtin builtin_rs05_lengthp 2 "rs05_lengthp" "Alignment";
builtin rs07_branch_HMM 4 "rs07_branch_HMM" "Alignment";
builtin builtin_rs07_lengthp 2 "rs07_lengthp" "Alignment";

rs05_lengthp m l = doubleToLogDouble (builtin_rs05_lengthp m l);

rs05_model logRate meanIndelLengthMinus1 tau tree = Prefix "RS05"
(do {
   logRate' <- Prefix "logRate" logRate;
   Log "logRate" logRate';
   let {rate = exp logRate';
        x = exp (-2.0*rate);
        delta = x/(1.0+x)};

   meanIndelLengthMinus1' <- Prefix "meanIndelLengthMinus1" meanIndelLengthMinus1;
   Log "meanIndelLength" (meanIndelLengthMinus1'+1.0);
   let {epsilon = meanIndelLengthMinus1'/(1.0 + meanIndelLengthMinus1')};

   tau' <- Prefix "tau" tau;
   Log "tau" tau';

   return (\heat training -> let {m = rs05_branch_HMM epsilon delta tau' heat training} in (\d b -> m, rs05_lengthp m))
});

rs07_lengthp e l = doubleToLogDouble (builtin_rs07_lengthp e l);

rs07_model logLambda meanIndelLengthMinus1 tree = Prefix "RS07"
(do {
--   logLambda <- laplace (-4.0) (1.0/sqrt 2.0);
   logLambda' <- Prefix "logLambda" logLambda;
   Log "logLambda" logLambda';
   let {lambda = exp logLambda'};

--   meanIndelLengthMinus1 <- exponential 10.0;
   meanIndelLengthMinus1' <- Prefix "meanIndelLengthMinus1" meanIndelLengthMinus1;
   Log "meanIndelLength" (meanIndelLengthMinus1'+1.0);
   let {epsilon = meanIndelLengthMinus1'/(1.0 + meanIndelLengthMinus1')};

   return (\heat training -> (\d b ->rs07_branch_HMM epsilon (lambda*d!b) heat training, rs07_lengthp epsilon))
});

rs07_relaxed_rates_model tree = Prefix "RelaxedRatesRS07"
(do {
   let {n_branches = numBranches tree;
        delta = 4};

   mean <- iid (n_branches + delta) (laplace (-4.0) (1.0/sqrt 2.0));
   sigma <- iid (n_branches + delta) (gamma 1.05 0.05);
  
   alpha <- gamma 2.0 (1.0/6.0);
   Log "alpha" alpha;

   category <- crp alpha n_branches delta;

   z <- iid n_branches (normal 0.0 1.0);

  let {logLambdas = [ mean!!k + z!!i * sigma!!k | i <- take n_branches [0..], let {k=category!!i}]};

  meanIndelLengthMinus1 <- exponential 10.0;
    
  let {epsilon = meanIndelLengthMinus1/(1.0 + meanIndelLengthMinus1);
      lambdas = map exp logLambdas};

  return $ (\d b heat training -> rs07_branch_HMM epsilon (lambdas!!b * d!b) heat training, \l -> rs07_lengthp epsilon l)
});

}
