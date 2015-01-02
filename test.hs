{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables
  #-}

import ExponentialData
import Data.List
import Data.IORef
import Control.Monad

-- Example: Sorted Lists

newtype SortedList = SortedList [Int] 
    deriving (Show, Eq)

instance DataStructure Int SortedList where
    compute = SortedList . sort

instance Mergeable SortedList where
    merge (SortedList as) (SortedList bs) = SortedList $ merge' as bs
        where
          merge' as [] = as
          merge' [] bs = bs
          merge' (a : as) (b : bs) | a <= b    = a : merge' as (b:bs)
                                   | otherwise = b : merge' (a:as) bs


testList1 = [75, 2, 47, 81, 93, 77, 2, 77, 52, 73, 61, 93, 83, 54, 
  62, 87, 76, 96, 28, 96, 47, 55, 38, 11, 80, 89, 24, 84, 38, 66, 32, 13] :: [Int]

test1 :: IO ()
test1 = do
  acc <- newIORef (compute ([] :: [Int]) :: Hierarchical SortedList);
  readIORef acc >>= putStrLn . show
  forM testList1 $ \x -> do
      readIORef acc >>= writeIORef acc . flip update x
      readIORef acc >>= putStrLn . show
  return ()

instance MergeableSteps SortedList ([Int], [Int], [Int]) where
    mergeStart (SortedList as) (SortedList bs) = ([], as, bs)
    mergeStep (acc, as, bs) =
        --let (acc1, as1, bs1) = merge' acc  as  bs  in
        let (acc2, as2, bs2) = merge' acc as bs in 
        case (acc2, as2, bs2) of 
          (_, [], []) -> Right (SortedList acc2)
          _ -> Left (acc2, as2, bs2)
          where
            merge' acc (a : as) [] = (acc ++ [a], as, [])
            merge' acc [] (b : bs) = (acc ++ [b], [], bs)
            merge' acc (a : as) (b : bs) 
                | a <= b    = (acc ++ [a], as, b:bs)
                | otherwise = (acc ++ [b], a:as, bs)

test2 :: IO ()
test2 = do
  acc <- newIORef (compute ([] :: [Int]) :: HierarchicalD SortedList ([Int], [Int], [Int]));
  readIORef acc >>= putStrLn . show
  forM testList1 $ \x -> do
      readIORef acc >>= writeIORef acc . flip update x
      readIORef acc >>= putStrLn . show
  return ()

