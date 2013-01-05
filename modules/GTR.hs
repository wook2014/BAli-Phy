module GTR where
{
  import SModel;
  import Distributions;
  note [ag,at,ac,gt,gc,tc] ~ dirichlet [2.0/8.0, 1.0/8.0, 1.0/8.0, 1.0/8.0, 1.0/8.0, 2.0/8.0];
  note ag := 2.0/8.0;
  note at := 1.0/8.0;
  note ac := 1.0/8.0;
  note gt := 1.0/8.0;
  note gc := 1.0/8.0;
  note tc := 1.0/8.0;
  main = \nuca -> gtr nuca ag at ac gt gc tc;
}