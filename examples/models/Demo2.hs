module Demo2 where
{
import Distributions;

main = do
{
  xs <- sample $ iid 10 (normal 0.0 1.0);

  let {ys = map (\x -> x*x) xs};

  return (Nothing,[
           ("xs",(Just xs,[])),
           ("ys",(Just ys,[])),
           ("sum",(Just $ sum ys,[]))
           ]);
}
}
