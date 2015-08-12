-- Conclusion.... not working

{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, GADTs, StandaloneDeriving #-}

import Data.TypeLevel (Nat, Succ, Add)
import Data.TypeLevel.Num.Reps

data FSVec s a where
    Empty :: FSVec D0 a
    Cons :: Nat n => a -> FSVec n a -> FSVec (Succ n) a

deriving instance (Nat n, Show a) => Show (FSVec n a)

sum' :: Nat n => FSVec n Int -> Int
sum' Empty = 0
sum' (Cons a rest) = a + (sum' rest)

test :: FSVec D2 Int
test = Cons 5 $ Cons 3 $ Empty

append :: (Num x, Num y, Add x y z) => FSVec x a -> FSVec y a -> FSVec z a
append Empty a = a
append (Cons x rest) a = Cons x (append rest a)

length' :: (Num n) => FSVec n a -> Int
length' Empty = 0
--length' (Cons _ rest) = 1 + length' rest
