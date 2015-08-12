{-# LANGUAGE FlexibleInstances, UndecidableInstances, ScopedTypeVariables #-}

import Group
import Sigma
import Data.Monoid

-- Examples of Zn groups and elements

data D3
data D11

type Zm11 = Zn D11 -- Integers under multiplication mod 11

instance Nat D3 where toNum = const 3
instance Nat D11 where toNum = const 11

elemD11 n = Zn n :: Zn D11

-- A sigma protocol of knowledge of a preimage


-- Proof of opening a Pedersen commitment
-- Proof of phi(w) = z, where phi((x,y)) = g^x h^r
commitmentOpeningBit :: (Nat n, Eq h, Group h) => h -> h -> h -> SigmaProtocol h (Zn n, Zn n) (Zn n, Zn n) (Zn n, Zn n)
commitmentOpeningBit g h z = sp_phi_binary (Hom hom) z
    where 
      hom (Zn x, Zn r) = (g `pow` x) `mappend` (h `pow` r)

-- Proof of opening a Pedersen commitment
-- Proof of phi(w) = z, where phi((x,y)) = g^x h^r
-- Group of g is modulus q, but order p
commitmentOpening :: (Nat p, Nat q) => (Zn q, Zn q) -> Zn q -> SigmaProtocol (Zn q) (ZnP p, ZnP p) (ZnP p, ZnP p) (ZnP p, ZnP p)
commitmentOpening (g, h) z = sp_phi_special (specialFromZn hom) z
    where 
      hom (ZnP x, ZnP r) = (g `pow` x) `mappend` (h `pow` r)

{--
-- Proof that two commits (in different groups) are equal
-- z = g^x h^r,  z' = g'^x h^r'... this suggests
-- phi (x,r,r') = (g^x h^r, g'^x h'^r')
   But what group is x a member of?
   If Z, then this is a homomorphism, but it's not really guaranteeing equality.
   If the order of 
--}
commitmentsEqual :: (Nat q, Nat q', Nat p) => (Zn q, Zn q, Zn q', Zn q') -> (Zn q, Zn q') -> SigmaProtocolPhi (Zn q, Zn q', Zn q) (ZnP p, ZnP p')
commitmentsEqual (g, h, g', h') (z, z') = undefined --sp_phi_special (specialFromZn hom) (z,z')
    where 
      hom = undefined --(ZnP x, ZnP r) = (g `pow` x) `mappend` (h `pow` r)


{--
  From the Camenisch/Lsyanskaya accumulators paper:

   X_{A,B} is the set of primes { e : e is prime and A <= e <= B }, and A and B are arbitrary
   polynomials in k, as long as 2 < A and B < A^2
   X'_{A,B} is a superset of X_{A,B}, and is a subset of the integer range [2, A^2 - 1]

   Further, regarding q', the order of the accumulated value commitment group, 
      B 2^(k'+k''+2) < A^2 - 1 < q'/2

 n: modulus of QR group (n is an RSA modulus)
   g,h are generators of this group
 p: modulus of a Schnorr group, of order q
   g', h' are generators of this group
 
 --}

commitedValueAccum :: (Nat n, Nat p) => (Zn n, Zn n, Zn p, Zn p) -> (Zn p, Zn n, Zn n, Zn n) -> ()
commitedValueAccum (g, h, g', h') (ce', ce, cu, cr) =
    undefined
    where
      hom (alpha, beta, gamma, delta, epsilon, zeta, phi, psi, nu, theta, xi) = 
          -- Ce = g'^alpha h'^phi
          ((g' `pow` alpha) `mappend` (h' `pow` phi),

           -- g' = (Ce / g')^gamma h'^psi
           (((ce' `mappend` (inv g')) `pow` gamma) `mappend` (h' `pow` psi)), 

           -- g' = (g' Ce)^theta h'^xi
           undefined, 
           undefined, -- Cr = h^epsilon g^zeta
           undefined, -- Ce = h^alpha g^nu
           undefined, -- v = Cu ^alpha (1/h)^beta
           undefined, -- 1 = Cr ^alpha (1/h)^delta (1/g)^beta
           undefined -- alpha in range [-B 2^(k'+k''+2, B 2^(k'+k''+2)]
          )
