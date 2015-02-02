import System.IO.Unsafe

import Lambda

-- CEK abstract machine for TermB
-- From matt.might's blog

type Var  = Int
type Env  = [D]
type Sig  = (TermB,Env,Kont)
data D    = Clo (TermB, Env) | V TermB | IntD Int | PairD D D | UnitD | LD D | RD D deriving Show
data Kont = Mt
          | Ar (TermB,Env,Kont)
          | Fn (TermB,Env,Kont)
          | Binop1 Binop (TermB,Env,Kont)
          | Binop2 Binop (TermB,Env,Kont)
  deriving Show

data Binop = OpPlus | OpTimes deriving Show

step :: Sig -> Sig
inject :: TermB -> Sig
isFinal :: Sig -> Bool

terminal :: (Sig -> Sig) -> (Sig -> Bool) -> Sig -> Sig
terminal step isFinal s | isFinal s = s
                        | otherwise = terminal step isFinal (step s)

terminal' :: (Sig -> Sig) -> (Sig -> Bool) -> Sig -> Sig
terminal' step isFinal s = unsafePerformIO $ do
                             putStrLn $ show s
                             return $ terminal'' where
                                             terminal'' | isFinal s = s
                                                        | otherwise = terminal' step isFinal (step s)

evaluate :: TermB -> Sig
evaluate pr = terminal' step isFinal (inject pr)

inject e = (e, [], Mt)

step (VarB x, rho, k) = case rho !! x of
                          Clo (lam, rho') -> (AbsB lam,rho',k)
                          V v -> (v, rho, k)
step (AppB f e, rho, k) = (f, rho, Ar (e, rho, k))
step (AbsB lam, rho, Ar(e, rho', k)) = (e, rho', Fn(lam, rho, k))
step (AbsB lam, rho, Fn(e, rho', k)) = (e, rho' ++ [Clo (lam, rho)], k)
step (LitB n, rho, Fn(e, rho', k)) = (e, rho' ++ [V $ LitB n], k)

step (PlusB a b, rho, k) = (a, rho, Binop1 OpPlus (b,rho,k))
step (TimesB a b, rho, k) = (a, rho, Binop1 OpTimes (b,rho,k))
step (LitB a, _, Binop1 op (b,rho,k)) = (b, rho, Binop2 op (LitB a,rho,k))
step (LitB b, _, Binop2 op (LitB a,rho,k)) = (LitB (opp op a b), rho, k)
    where 
      opp OpPlus = (+)
      opp OpTimes = (*)

isFinal (AbsB _, _, Mt) = True
isFinal (LitB _, _, Mt) = True
isFinal _ = False



-- Example
testEval = evaluate $ debruijnize $ App (App tApplyTwice tDouble) (Lit 5)
