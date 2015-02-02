{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies #-}
-- Version with seqhashes representing state
import Lambda
import System.IO.Unsafe
import Prelude hiding (concat, lookup, length)
import qualified Prelude

-- A class for seghash-style data structures
class Show t => SeqHash m t | m -> t where
    build :: [t] -> m
    concat :: m -> m -> m
    length :: m -> Int
    prefix :: m -> Int -> m
    suffix :: m -> Int -> m
    lookup :: m -> Int -> t

append :: SeqHash m t => m -> t -> m
append m t = m `concat` build [t]

-- The simplest (inefficient) implementation of SeqHash is just using a list directly
instance Show t => SeqHash [t] t where
    build = id
    concat = (++)
    length = Prelude.length
    prefix = flip take
    suffix m l = reverse $ take l $ reverse m
    lookup = (!!)


-- SECD machine (from https://gist.github.com/ijp/4981308 )
type Stack = [Value]
type Env = [Value]

data Controllee = AP
                | APBin Binop
                | AE TermB
                  deriving (Show)

data Binop = OpPlus | OpTimes deriving Show

data Value = Clo TermB Env
           | V Int 
             deriving Show

type Control = [Controllee]
type Offset = Int

type SeqHashConcrete = [(Stack, Env, Control, Offset)]

type Sig = (SeqHashConcrete, (Stack, Env, Control, Offset))

inject :: TermB -> Sig
inject e = ([],([], [], [AE e], 0))

isFinal :: Sig -> Bool
isFinal (tree,([s], e, [], skip)) | skip == length tree = True
isFinal _ = False


-- Heart of SECD machine, transition rules
step :: Sig -> Sig

-- This is the only operation that consumes/pops from the 'dump'
-- Instead, look it up in the tree
step (tree, state@([s], e, [], skip)) = (tree `append` state, (s:s', e', c', d'+skip+2))
    where
      (Clo b _ : __ : s', e', (AP : c'), d') = lookup tree (length tree - skip - 1)

-- This is the only operation that pushes onto the 'dump'
step (tree, state@(Clo b e' : s2 : ss, e, (AP : cs), skip)) = (tree `append` state, ([], e'', [AE b], 0))
  where e'' = e' ++ [s2]

step (tree, state@(s, e, (AE (VarB i):cs), d))        = (tree `append` state, (e !! i : s, e, cs, d+1))
step (tree, state@(s, e, (AE (AbsB b) : cs), d))      = (tree `append` state, (Clo b e : s, e, cs, d+1))
step (tree, state@(s, e, (AE (AppB op arg) : cs), d)) = (tree `append` state, (s, e, (AE arg : AE op : AP : cs), d+1))
step (tree, state@(s, e, (AE (LitB o):cs), d))         = (tree `append` state, (V o : s, e, cs, d+1))
step (tree, state@(s, e, (AE (PlusB  a1 a2) : cs), d)) = (tree `append` state, (s, e, (AE a1 : AE a2 : APBin OpPlus  : cs), d+1))
step (tree, state@(s, e, (AE (TimesB a1 a2) : cs), d)) = (tree `append` state, (s, e, (AE a1 : AE a2 : APBin OpTimes : cs), d+1))
step (tree, state@(V a2 : V a1 : ss, e, (APBin bin : cs), d)) = (tree `append` state, (V (op bin a1 a2) : ss, e, cs, d+1)) where
    op OpPlus  = (+)
    op OpTimes = (*)
step (_, (s, e, c, d)) = error "crash"


terminal :: (Sig -> Sig) -> (Sig -> Bool) -> Sig -> Sig
terminal step isFinal s | isFinal s = s
                        | otherwise = terminal step isFinal (step s)

terminal' :: (Sig -> Sig) -> (Sig -> Bool) -> Sig -> Sig
terminal' step isFinal s = unsafePerformIO $ do
                             putStrLn $ show (snd s)
                             return $ terminal'' where
                                             terminal'' | isFinal s = s
                                                        | otherwise = terminal' step isFinal (step s)

evaluate :: TermB -> Sig
evaluate pr = terminal' step isFinal (inject pr)
