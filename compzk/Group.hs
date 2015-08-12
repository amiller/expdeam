{-# LANGUAGE FlexibleInstances, UndecidableInstances, ScopedTypeVariables #-}

{--
 Groups and homomorphisms
 --}
module Group where
import Data.Monoid

class Monoid g => Group g where
  inv :: g -> g
  -- law: (inv g) `mappend` g = mempty = g `mappend` (inv g)

{-- Product group (product monoid is already known) --}
instance (Group g, Group h) => Group (g,h) where inv (g,h) = (inv g, inv h)
  
{-- Group homomorphisms --}
data Hom g h = Hom (g -> h)
-- laws: hom (mempty) == mempty, (hom x) `mappend` (hom y) == hom (x `mappend` y)



{-- Groups of integers under addition --}
newtype Z = Z Int
instance Monoid Z where
    mempty = Z 0
    mappend (Z a) (Z b) = Z (a + b)

instance Group Z where
    inv (Z z) = Z $ negate z


{-- 
  Group for Z* and Z+ mod n
 --}
class Nat n where
    toNum :: Num a => n -> a

-- Type of integers, with an associated range (not all elements need lie in this range)
newtype Zbound n = Zbound Int deriving Eq
instance Show (Zbound n) where
    show (Zbound x) = show x

instance Nat n => Monoid (Zbound n) where
    mempty = Zbound 0
    mappend = (+)

instance Num (Zbound n) where
    Zbound x + Zbound y = Zbound $ x + y
    Zbound x * Zbound y = Zbound $ x * y
    abs (Zbound n) = Zbound $ abs n
    signum (Zbound n) = Zbound $ signum n
    negate (Zbound n) = Zbound $ negate n
    fromInteger = Zbound . fromInteger

-- Type of integers mod n under multiplication
newtype Zn n = Zn Int 
    deriving (Eq)
instance Nat n => Show (Zn n) where
    show (Zn n) = show n ++ " % Z*_" ++ show (toNum (undefined :: n) :: Int)

instance Nat n => Num (Zn n) where
    Zn x + Zn y = Zn $ x + y `mod` toNum (undefined :: n)
    Zn x * Zn y = Zn $ x * y `mod` toNum (undefined :: n)
    abs (Zn n) = Zn $ abs n
    signum (Zn n) = Zn $ signum n
    negate (Zn n) = Zn $ negate n
    fromInteger = Zn . flip mod (toNum (undefined :: n)) . fromInteger

instance Nat n => Monoid (Zn n) where
    mempty = Zn 1
    mappend = (*)

-- Type of integers mod n under addition
newtype ZnP n = ZnP Int
    deriving Eq
instance Nat n => Show (ZnP n) where
    show (ZnP n) = show n ++ " % Z+_" ++ show (toNum (undefined :: n) :: Int)

instance Nat n => Num (ZnP n) where
    ZnP x + ZnP y = ZnP $ x + y `mod` toNum (undefined :: n)
    ZnP x * ZnP y = ZnP $ x * y `mod` toNum (undefined :: n)
    abs (ZnP n) = ZnP $ abs n
    signum (ZnP n) = ZnP $ signum n
    negate (ZnP n) = ZnP $ negate n
    fromInteger = ZnP . flip mod (toNum (undefined :: n)) . fromInteger

instance Nat n => Monoid (ZnP n) where
    mempty = ZnP 0
    mappend = (+)



-- Power by repeated squaring
pow :: Monoid g => g -> Int -> g
pow g 0 = mempty
pow g 1 = g
pow g n | n `mod` 2 == 1 = g `mappend` pow g (n-1)
        | otherwise = half `mappend` half where half = pow g (n `div` 2)

instance Nat n => Group (Zn n) where
    inv n = pow n (toNum (undefined :: n) - 2)

instance Nat n => Group (ZnP n) where
    inv = negate
