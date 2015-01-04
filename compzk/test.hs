{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies, Rank2Types, ScopedTypeVariables
  #-}
import System.Random
import Control.Monad.Random.Class
import Control.Monad
import Control.Monad.State
import Data.Monoid
import Data.Int

{-- Sampleable --}
-- Sampleable a indicates there is a way to sample uniformly from elements of a 
class Sampleable a where
  sample :: MonadRandom m => m a
  -- Laws:
  --  sample must produce a uniform distribution over elements of type a

-- Composition
instance (Sampleable a, Sampleable b) => Sampleable (a,b) where
  sample = do { a <- sample; b <- sample; return (a,b) }


{-- Sigma Protocols --}
data SigmaProtocol com chal resp wit aux = SigmaProtocol {
    commit :: MonadRandom m => wit -> m (com, aux)
  , respond :: (wit, aux, chal) -> resp
  , verify :: (com, chal, resp) -> Bool
  , simulate :: MonadRandom m => chal -> m (com, resp)
  , extract :: (com, (chal,resp), (chal,resp)) -> wit
  , check :: wit -> Bool -- Check that this is a witness of the NP statement
}

{--
  AND composition
  --}
spAnd :: (SigmaProtocol comA chalA respA witA auxA,
          SigmaProtocol comB chalB respB witB auxB) -> 
         SigmaProtocol (comA, comB) (chalA, chalB) (respA, respB) (witA, witB) (auxA, auxB)
spAnd (a, b) = SigmaProtocol {
    commit = \(wA, wB) -> do { (cA,aA) <- commit a wA; (cB,aB) <- commit b wB; return ((cA,cB),(aA,aB)) }
  , respond = undefined
  , verify = undefined
  , simulate = undefined
  , extract = undefined
  , check = undefined
}

{--
  Multiple (parallel) repetitions of a sigma protocol using a common witness, to reduce the knowledge error
 --}
-- Ideally these should be vectors instead of lists
spRepeat :: Int -> SigmaProtocol com chal resp wit aux -> SigmaProtocol [com] [chal] [resp] wit [aux]
spRepeat n sp = SigmaProtocol {
    commit = \w -> replicateM n (commit sp w) >>= return . unzip
  , respond = undefined
  , verify = undefined
  , simulate = undefined
  , extract = undefined
  , check = undefined
}

{--
  OR composition
 --}
instance RandomGen [Int32] where
  next (x:xs) = (fromIntegral x, xs)
  genRange _ = (fromIntegral (minBound :: Int32), fromIntegral (maxBound :: Int32))
  
instance MonadRandom m => MonadRandom (StateT [Int32] m) where

{--
 --}
spOr :: forall chalA chalB comA comB respA respB witA witB auxA auxB. (Sampleable chalA, Sampleable chalB) =>
        Int -> 
        (SigmaProtocol comA chalA respA witA auxA,
         SigmaProtocol comB chalB respB witB auxB) ->
        SigmaProtocol (comA, comB) [Int32] (respA, respB, ([Int32],[Int32])) (Either witA witB) ([Int32], Either auxA auxB)
spOr bits (a, b) = SigmaProtocol {
  commit = commitA
  , verify = undefined
  } where
  commitA :: forall m. MonadRandom m => (Either witA witB) -> m ((comA, comB), ([Int32], Either auxA auxB))
  commitA = (\w -> case w of
       Left w -> do
         (cR :: chalB, nums :: [Int32]) <- runStateT (sample :: StateT [Int32] m chalB) [];
         (rR,sR) <- simulate b cR;
         (rL,sL) <- commit a w;
         return ((rL,rR), (nums, Left sR))
       Right w -> undefined) 

{--
 Instantiation of SigmaProtocol from Homomorphisms
 --}

{--
 Groups and homomorphisms
 --}
class Monoid g => Group g where
  inv :: g -> g
  -- law: (inv g) `mappend` g = mempty = g `mappend` (inv g)
  
data Hom g h = Hom (g -> h)
mb
data SpecialHom g h = SpecialHom {
  sh_hom :: g -> h,
  sh_v :: Int,
  sh_u :: h -> g
  -- law: (sh_hom (sh_u x)) = mconcat (replicate v x)
}

sp_phi_binary :: (Eq h, Sampleable g, Group g, Group h) => Hom g h -> h -> SigmaProtocol h Bool g g g
sp_phi_binary (Hom phi) x = SigmaProtocol {
    commit = \w -> do 
       k <- sample;
       let r = phi k in
         return (r, k)
  , respond = \(w, k, c) -> k `mappend` (if c then inv w else mempty)     -- Set s := k - cw
  , verify = \(r, c, s) -> r == phi s `mappend` (if c then x else mempty) -- Check r == phi(s)*x^c
  , simulate = \c -> do
       s <- sample;
       let r = phi s `mappend` (if c then x else mempty) in
         return (r, s)
  , extract = undefined
  , check = \w -> phi w == x
}


