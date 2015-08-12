-- Conclusion.... Sure, this is viable

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies, Rank2Types, ScopedTypeVariables, InstanceSigs, GADTs, UndecidableInstances, StandaloneDeriving
  #-}

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


-- Or composition
newtype Or a b = Or (Either a b)

data SigmaProtocolGuts wit com resp aux = SigmaProtocolGuts {
    commit :: MonadRandom m => wit -> m (com, aux)
  , respond :: (wit, aux, [Bit]) -> resp
  , verify :: (com, [Bit], resp) -> Bool
  , simulate :: MonadRandom m => [Bit] -> m (com, resp)
  , extract :: (com, ([Bit],resp), ([Bit],resp)) -> wit
  , check :: wit -> Bool -- Check that this is a witness of the NP statement
  , chalbits :: Int      -- Indicate how many bits are required
}

class SigmaProtocol a where
    type Com a
    type Resp a
    type Aux a
    guts :: SigmaProtocolGuts a (Com a) (Resp a) (Aux a)

instance (SigmaProtocol a, SigmaProtocol b) => SigmaProtocol (Or a b) where
        type Com (Or a b) = (Com a, Com b)
        type Resp (Or a b) = (Resp a, Resp b, ([Bit],[Bit]))
        type Aux (Or a b) = ([Bit], Either (Aux a, Resp b) (Aux b, Resp a))
        guts = SigmaProtocolGuts {
          commit = \(Or w) -> 
          case w of
            Left w -> do
                   bitsR <- randomBits bits;
                   (rR, sR) <- simulate b bitsR;
                   (rL,aL) <- commit a w;
                   return ((rL,rR), (bitsR, Left (aL, sR)))
            Right w -> do
                   bitsL <- randomBits bits;
                   (rL,sL) <- simulate a bitsL;
                   (rR,aR) <- commit b w;
                   return ((rL,rR), (bitsL, Right (aR, sL))),
          verify = undefined,
          respond = undefined,
          simulate = undefined,
          extract = undefined,
          check = undefined,
          chalbits = bits
               } where
            bits = max (chalbits a) (chalbits b)
            a :: SigmaProtocolGuts a (Com a) (Resp a) (Aux a) = guts
            b :: SigmaProtocolGuts b (Com b) (Resp b) (Aux b) = guts
                                                                    

-- Zero Knowledge composition
-- Mostly for the sake of being able to manipulate ephemeral commitments
class Show stmt => Statement stmt where
    type Witness stmt
    checkWitness :: stmt -> Witness stmt -> Bool

data RangeStmt lo hi where
    MkRangeStmt :: (Nat lo, Nat hi) => RangeStmt lo hi

instance Show (RangeStmt lo hi) where
    show MkRangeStmt = "inRange: " ++ show (toNum (undefined :: lo)) ++ show (toNum (undefined :: hi))

instance Statement (RangeStmt lo hi) where
    type Witness (RangeStmt lo hi) = Int 
    checkWitness MkRangeStmt x = lo' <= x && x <= hi'
      where
        lo' = toNum (undefined :: lo)
        hi' = toNum (undefined :: hi)

data MulStmt a = MulStmt String

instance Show (MulStmt a) where
    show (MulStmt product) = "mul (w1,w2) = " ++ show product
-- Start with g^x h^r   g^y

data Proof stmt proof = Proof {
      prove :: Witness stmt -> proof,
      verifyProof :: proof -> Bool,
      extractProof :: (forall m. MonadRandom m => m proof) -> Witness stmt,
      simulateProof :: MonadRandom m => m (Witness stmt)
    }

class HomClass a where 
    type Dom a
    type Cod a
    toHom :: a -> Hom (Dom a) (Cod a)

instance HomClass (Hom a b) where
    type Dom (Hom a b) = a
    type Cod (Hom a b) = b
    toHom = id

-- given homomorphisms phi(x) = y, phi'(x) = z, phi''(x) = (y,z) is also
data ProdHom a b c where
    ProdHom :: Hom a b -> Hom a c -> ProdHom a b c

instance HomClass (ProdHom a b c) where
    type Dom (ProdHom a b c) = a
    type Cod (ProdHom a b c) = (b,c)
    toHom (ProdHom (Hom f) (Hom g)) = Hom (\x -> (f x, g x))

-- a group generator
data GroupGenerator g where
    MkGenerator :: Group g => g -> GroupGenerator g

-- given a group element, the mapping phi(x) = g^x is a homomorphism
data ZExponHom g where
    ZExponHom :: Group g => g -> ZExponHom g

instance HomClass (ZExponHom g) where
    type Dom (ZExponHom g) = Z
    type Cod (ZExponHom g) = g
    toHom (ZExponHom g) = Hom (\(Z x) -> pow g x)

--instance HomClass a, HomClass b
---instance (HomClass a b, Hom a c) => Hom a (b,c) where
    



{--
mkRangeProof :: RangeStmt lo hi -> Proof (RangeStmt lo hi) (Int, Int, ())
mkRangeProof _ = let hom = undefined in Proof {
        prove = \x -> 
                let c1 = undefined in -- intermediate commitment,
                let c2 = undefined in --
                  undefined,
        verifyProof = \_ -> \(c1, c2, pf) ->
            let sp = undefined in --sp_phi_special hom (c1, c2) in
            undefined, --sp == 1,
        extractProof = \adv -> do
          undefined, -- rewinding proof... pass adv to underlying sigma protocol
        simulateProof = undefined
      }
--}


{----
 Some tools for assembling homomorphisms based on simpler statements
 ----}

data WitnessIsomorphism a b where
    WitnessIsomorphism :: (Statement a, Statement b) => (Witness a -> Witness b) -> (Witness b -> Witness a) -> WitnessIsomorphism a b
    -- laws: witIsoFwd (witIsoRev b) = b, witIsoRev (witIsoFwd a) = a
--class (Statement a, Statement b) => WitnessIsomorphism a b where
--    witIsoFwd :: Witness a -> Witness b
--    witIsoRev :: Witness b -> Witness a


{--
instance WitnessIsomorphism (MulStmt p) (Hom a) where
    witIsoFwd = undefined
    witIsoRev = undefined
    -- undefined
--}

--instance WitnessIsomorphism a b => WitnessIsomorphism b a where
--    witIsoFwd = witIsoRev
--    witIsoRev = witIsoFwd

mkIsoProof :: WitnessIsomorphism a b -> Proof a pa -> Proof b pa
mkIsoProof (WitnessIsomorphism fwd rev) p = Proof {
                 prove = \witB -> prove p (rev witB),
                 verifyProof = verifyProof p,
                 simulateProof = undefined,
                 extractProof = undefined
             }

-- RSAGroup is a kind of group under multiplication
class Nat n => RSAModulus n where
    assertProductOfSafePrimes :: n -> Bool
    
data RSAGroup n where
    RSAGroup :: RSAModulus n => RSAGroup (Zn n)
-- Law: n must be the product of safe primes


-- Proof that c is a commitment to a positive value
data IsPositiveStatement n where
    IsPositiveStatement :: Nat n => (Zn n) -> IsPositiveStatement n
  
deriving instance Show (IsPositiveStatement n)

instance Statement (IsPositiveStatement n) where
    type Witness (IsPositiveStatement n) = Zn n
    checkWitness _ (Zn n) = n >= 0

--    describe n = show (toNum n) ++ "is positive"


-- Given a positive number x, finds a,b,c,d such that a*a+b*b+c*c+d*d = x
-- An algorithm for this is given in 
fourSquares :: Int -> (Int, Int, Int, Int)
fourSquare = undefined 


lagrangeProof :: RSAGroup n -> WitnessIsomorphism (Int, Int, Int, Int) ()
lagrangeProof = undefined
