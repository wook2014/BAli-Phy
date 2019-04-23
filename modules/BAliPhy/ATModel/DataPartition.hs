module BAliPhy.ATModel.DataPartition where

import Data.Maybe
import Tree

data IModel
data SModel
data HMM
data LeafSequence
data ConditionalLikelihoodVector
data PairwiseAlignment
data Matrix
data Partition = Partition SModel (Maybe IModel) Double Tree (Array Int LeafSequence) (Array Int PairwiseAlignment) (Maybe (Array Int HMM)) (Array Int Matrix) (Array Int ConditionalLikelihoodVector)

smodel              (Partition s _ _ _  _  _  _  _  _ ) = s
imodel              (Partition _ i _ _  _  _  _  _  _ ) = i
scale               (Partition _ _ s _  _  _  _  _  _ ) = s
get_tree            (Partition _ _ _ t  _  _  _  _  _ ) = t
leaf_sequences      (Partition _ _ _ _  ls _  _  _  _ ) = ls
pairwise_alignments (Partition _ _ _ _  _  as _  _  _ ) = as
hmms                (Partition _ _ _ _  _  _  hs _  _ ) = hs
transition_ps       (Partition _ _ _ _  _  _  _  ps _ ) = ps