{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies, Rank2Types, ScopedTypeVariables, InstanceSigs
  #-}
module Sigma where

import System.Random
import Control.Monad.Random.Class
import Control.Monad
import Control.Monad.State
import Data.Monoid
import Data.Int
import qualified Data.Vec as V

import Group

type Bit = Bool

randomBit :: MonadRandom m => m Bit
randomBit = getRandom

randomBits n = forM [1..n] $ \_ -> getRandom

xor True False = True
xor False True = True
xor _ _ = False

bitsToNum [] = 0
bitsToNum (True  : bits) = 0 + 2 * bitsToNum bits
bitsToNum (False : bits) = 1 + 2 * bitsToNum bits

{-- Sampleable --}
-- Sampleable a indicates there is a way to sample uniformly from elements of a 
class Sampleable a where
  sample :: MonadRandom m => m a -- True uniform sample
  psample :: [Bit] -> a          -- Best effort sample using bits, however many are available

  -- Laws:
  --  sample must produce a uniform distribution over elements of type a

instance Nat n => Sampleable (Zbound n) where
    sample = getRandomR (1 :: Int, (toNum (undefined :: n)) - 1 :: Int) >>= return . Zbound
    psample bits = bitsToNum bits

instance Nat n => Sampleable (Zn n) where
    sample = getRandomR (1 :: Int, (toNum (undefined :: n)) - 1 :: Int) >>= return . Zn
    psample bits = bitsToNum bits

instance Nat n => Sampleable (ZnP n) where
    sample = getRandomR (0 :: Int, (toNum (undefined :: n)) - 1 :: Int) >>= return . ZnP
    psample bits = bitsToNum bits

-- Composition of sampleables
splitInHalf xs = let half = length xs `div` 2 in (take half xs, drop half xs)
instance (Sampleable a, Sampleable b) => Sampleable (a,b) where
  sample = do { a <- sample; b <- sample; return (a,b) }
  psample bits = let (a,b) = splitInHalf bits in (psample a, psample b)


{-- Sigma Protocols --}
data SigmaProtocol com resp wit aux = SigmaProtocol {
    commit :: MonadRandom m => wit -> m (com, aux)
  , respond :: (wit, aux, [Bit]) -> resp
  , verify :: (com, [Bit], resp) -> Bool
  , simulate :: MonadRandom m => [Bit] -> m (com, resp)
  , extract :: (com, ([Bit],resp), ([Bit],resp)) -> wit
  , check :: wit -> Bool -- Check that this is a witness of the NP statement
  , chalbits :: Int      -- Indicate how many bits are required
}


{--
  AND composition
  --}
spAnd :: (SigmaProtocol comA respA witA auxA,
          SigmaProtocol comB respB witB auxB) -> 
         SigmaProtocol (comA, comB) (respA, respB) (witA, witB) (auxA, auxB)
spAnd (a, b) = SigmaProtocol {
    commit = \(wA, wB) -> do { (cA,aA) <- commit a wA; (cB,aB) <- commit b wB; return ((cA,cB),(aA,aB)) }
  , respond = undefined
  , verify = undefined
  , simulate = undefined
  , extract = undefined
  , check = undefined
  , chalbits = chalbits a + chalbits b -- Need bits for both
}


{--
  Multiple (parallel) repetitions of a sigma protocol using a common witness, to reduce the knowledge error
 --}
-- Ideally these should be vectors instead of lists
spRepeat :: Int -> SigmaProtocol com resp wit aux -> SigmaProtocol [com] [resp] wit [aux]
spRepeat n sp = SigmaProtocol {
    commit = \w -> replicateM n (commit sp w) >>= return . unzip
  , respond = undefined
  , verify = undefined
  , simulate = undefined
  , extract = undefined
  , check = undefined
  , chalbits = n * chalbits sp
}

{--
  OR composition
--}

spOr :: forall comA comB respA respB witA witB auxA auxB.
        (SigmaProtocol comA respA witA auxA,
         SigmaProtocol comB respB witB auxB) ->
        SigmaProtocol (comA, comB) (respA, respB, ([Bit],[Bit])) (Either witA witB) ([Bit], Either (auxA,respB) (auxB,respA))
spOr (a, b) = SigmaProtocol {
    commit = commit'
  , verify = undefined
  , respond = undefined
  , simulate = \bits -> do
      bitsL <- randomBits (chalbits $ spOr (a,b));
      bitsR <- return $ zipWith xor bits bitsL;
      (rL,sL) <- simulate a bitsL;
      (rR,sR) <- simulate b bitsR; 
      return ((rL,rR), (sL, sR, (bitsL, bitsR)))

  , extract = undefined
  , check = undefined
  , chalbits = max (chalbits a) (chalbits b)
  } where
  commit' :: forall m. MonadRandom m => (Either witA witB) -> m ((comA, comB), ([Bit], Either (auxA,respB) (auxB,respA)))
  commit' = \w -> case w of
       Left w -> do
         bitsR <- randomBits (chalbits $ spOr (a,b));          -- sample random bits
         (rR,sR) <- simulate b bitsR;
         (rL,aL) <- commit a w;
         return ((rL,rR), (bitsR, Left (aL, sR)))
       Right w -> do
         bitsL <- randomBits (chalbits $ spOr (a,b));
         (rL,sL) <- simulate a bitsL;
         (rR,aR) <- commit b w;
         return ((rL,rR), (bitsL, Right (aR, sL)))


{--
 Instantiation of SigmaProtocol from Homomorphisms
 --}

type SigmaProtocolPhi g h = SigmaProtocol h g g g

sp_phi_binary :: (Eq h, Sampleable g, Group g, Group h) => Hom g h -> h -> SigmaProtocolPhi g h
sp_phi_binary (Hom phi) x = SigmaProtocol {
    commit = \w -> do 
       k <- sample;
       let r = phi k in
         return (r, k)
  , respond = \(w, k, [c]) -> k `mappend` (if c then inv w else mempty)     -- Set s := k - cw
  , verify = \(r, [c], s) -> r == phi s `mappend` (if c then x else mempty) -- Check r == phi(s)*x^c
  , simulate = \[c] -> do
       s <- sample;
       let r = phi s `mappend` (if c then x else mempty) in
         return (r, s)
  , extract = undefined
  , check = \w -> phi w == x
  , chalbits = 1
}


{-- More efficient version with special homomorphisms --}

data SpecialHom g h = SpecialHom {
  sh_hom :: g -> h,
  sh_v :: Int,
  sh_u :: h -> g
  -- law: (sh_hom (sh_u x)) = mconcat (replicate v x)  x**v = u(x)
}


specialFromZn :: forall n g. (Monoid g, Nat n) => (g -> (Zn n)) -> SpecialHom g (Zn n)
specialFromZn phi = SpecialHom {
                      sh_hom = phi,
                      sh_v = (toNum (undefined :: n)),
                      sh_u = const mempty
                    }

sp_phi_special :: (Eq h, Sampleable g, Group g, Group h) => SpecialHom g h -> h -> SigmaProtocolPhi g h
sp_phi_special sh x = SigmaProtocol {
    commit = \w -> do 
       k <- sample;
       let r = phi k in
         return (r, k)
  , respond = \(w, k, c) -> k `mappend` (w `pow` (negate $ bitsToNum c))  -- Set s := k - cw
  , verify = \(r, c, s) -> r == phi s `mappend` (x `pow` (bitsToNum c)) -- Check r == phi(s)*x^c
  , simulate = \c -> do
       s <- sample;
       let r = phi s `mappend` (x `pow` (bitsToNum c)) in
         return (r, s)
  , extract = undefined -- TODO
  , check = \w -> phi w == x
  , chalbits = 1
}
    where phi = sh_hom sh
