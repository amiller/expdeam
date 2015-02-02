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
                | APop
                  deriving (Show)

data Binop = OpPlus | OpTimes deriving Show

data Value = Clo TermB Env
           | V Int 
             deriving Show

type Control = [Controllee]

type Offset = Int 

data Dump = Dump Stack Env Control Dump
          | InitState
            deriving (Show)

type SeqHashConcrete = [(Stack, Env, Control, Dump, Offset)]

type Sig = (SeqHashConcrete, (Stack, Env, Control, Dump, Offset))

inject :: TermB -> Sig
inject e = (build [], ([], [], [AE e], InitState, 0))

isFinal :: Sig -> Bool
isFinal (t,(s:_, e, [], InitState, o))           = True
isFinal _ = False

-- Heart of SECD machine, transition rules
step :: Sig -> Sig

-- This is the only operation that consumes/pops from the 'dump'
step (t,([s], e, [], (Dump s' e' c' d'), o))  = (t,(s:s', e', c', d', o))
-- This is the only operation that pushes onto the 'dump'
step (t,(Clo b e' : s2 : ss, e, (AP : cs), d, o)) = (t,([], e'', [AE b], d', o))
  where e'' = e' ++ [s2]
        d'  = Dump ss e cs d

step (t, (s, e, (AE (VarB i):cs), d, o))        = (t, (e !! i : s, e, cs, d, o))
step (t, (s, e, (AE (AbsB b) : cs), d, o))      = (t, (Clo b e : s, e, cs, d, o))
step (t, (s, e, (AE (AppB op arg) : cs), d, o)) = (t, (s, e, (AE arg : AE op : AP : cs), d, o))
step (t, (s, e, (AE (LitB v):cs), d, o))         = (t, (V v : s, e, cs, d, o))
step (t, (s, e, (AE (PlusB  a1 a2) : cs), d, o)) = (t, (s, e, (AE a1 : AE a2 : APBin OpPlus  : cs), d, o))
step (t, (s, e, (AE (TimesB a1 a2) : cs), d, o)) = (t, (s, e, (AE a1 : AE a2 : APBin OpTimes : cs), d, o))
step (t, (V a2 : V a1 : ss, e, (APBin bin : cs), d, o)) = (t, (V (op bin a1 a2) : ss, e, cs, d, o)) where
    op OpPlus  = (+)
    op OpTimes = (*)

step (t, state@(s, e, (AE (ArticB a):cs), d, o))        = (t `append` state, ([], e, [AE a, APop], InitState, 0))
step (t, state@([s], e, [APop], InitState, o))        = (t `append` state, (s:s', e', c', d', (o'+o+2)))
    where (s', e', (AE (ArticB _):c'), d', o') = lookup t (length t - o - 1)

step (t, (s, e, c, d, o)) = error "crash"


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



findGreatestCommonPrefix :: SeqHashConcrete -> SeqHashConcrete -> Int
findGreatestCommonPrefix a b | a == b = undefined
