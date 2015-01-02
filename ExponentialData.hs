{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, InstanceSigs, ScopedTypeVariables
  #-}
module ExponentialData where

{----------
  First, declare a simple class of data structures
 ----------}

class DataStructure a b where
    compute :: [a] -> b

class Updateable a b where
    update :: b -> a -> b
    -- laws:
    -- (update (compute as) a)  is related to (compute (as ++ [a]))

instance DataStructure a b => DataStructure a ([a], b) where
  compute as = (as, compute as)

-- It's trivial to get an Updateable from a DataStructure, but
-- this is often inefficient.
{-
instance DataStructure a b => Updateable a ([a], b) where
  update (as, _) a = compute (as ++ [a])
 -}


{-------------
  Start with the "mergeable" variant
 -------------}

class Mergeable b where
    merge :: b -> b -> b

newtype Hierarchical b = Hier [Maybe b]
  deriving Show

instance (DataStructure a b, Mergeable b) => Updateable a (Hierarchical b) where
    update :: Hierarchical b -> a -> Hierarchical b
    update (Hier levels) a = Hier (updateLevel levels (compute [a]))
        where
          updateLevel [] carry = Just carry : []
          updateLevel (Nothing : levels) carry = Just carry : levels
          updateLevel (Just b : levels) carry = Nothing : (updateLevel levels (merge b carry))

instance (DataStructure a b, Mergeable b) => DataStructure a (Hierarchical b) where
    compute = foldl update (Hier [])


{--------------------
 De-amortized version
 --------------------}

class MergeableSteps b interm where
    mergeStart :: b -> b -> interm
    mergeStep :: interm -> Either interm b
    -- Laws assumed to support:
    -- Assume x and y are elements each of size n, then mergeStart followed by n sequential calls of produces an element b of size 2n

newtype HierarchicalD b interm = HierD [(Maybe (interm, b,b), Maybe b)]
    deriving (Show, Read, Eq)

--instance (DataStructure a b, MergeableSteps b interm) => DataStructure a (HierarchicalD b interm) where
--    compute = foldr update (compute [])

instance (DataStructure a b, MergeableSteps b interm) => Updateable a (HierarchicalD b interm) where
    update :: HierarchicalD b interm -> a -> HierarchicalD b interm
    update (HierD levels) x = HierD (updateLevel levels (Just $ compute [x]))
        where
          updateLevel :: [(Maybe (interm, b, b), Maybe b)] -> (Maybe b) -> [(Maybe (interm, b, b), Maybe b)]
          updateLevel [] Nothing = [] -- Natural base case

          updateLevel [] (Just carry) = (Nothing, Just carry) : [] -- Create a new level

          updateLevel ((Nothing, Nothing) : _) _ = undefined -- Shouldn't happen

          updateLevel ((Nothing, Just s1) : levels) Nothing = 
              (Nothing, Just s1) : updateLevel levels Nothing

          updateLevel ((Nothing, Just s1) : levels) (Just s2) = 
              (Just (mergeStart s1 s2, s1, s2), Nothing) : updateLevel levels Nothing

          updateLevel ((Just (i, s1, s2), live) : levels) Nothing =
              let Left i' :: Either interm b = mergeStep i in
              (Just (i', s1, s2), live) : updateLevel levels Nothing

          updateLevel ((Just (i, s1, s2), Nothing) : levels) (Just live) = 
              let Left i' :: Either interm b = mergeStep i in
              (Just (i', s1, s2), Just live) : updateLevel levels Nothing

          updateLevel ((Just (i, _, _), Just s1) : levels) (Just s2) = 
              let Right carry = mergeStep i in
              (Just (mergeStart s1 s2, s1, s2), Nothing) : updateLevel levels (Just carry)

instance (DataStructure a b, MergeableSteps b interm) => DataStructure a (HierarchicalD b interm) where
    compute = foldl update (HierD [])
