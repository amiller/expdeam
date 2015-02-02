import Lambda
import System.IO.Unsafe


-- SECD machine (from https://gist.github.com/ijp/4981308 )
type Stack = [Value]
type Env = [Value]

data Control = Call
             | Ret
             | Prim1 Prim1 Control
             | Prim2 Prim2 Control
             | Prim3 Prim3 Control
             | CCase TermB TermB Control
             | CFix Control
             | AE TermB Control
                  deriving (Show)

data Prim1 = P1 String (Value -> Value)
data Prim2 = P2 String (Value -> Value -> Value)
data Prim3 = P3 String (Value -> Value -> Value -> Value)
instance Show Prim1 where show (P1 s _) = s
instance Show Prim2 where show (P2 s _) = s
instance Show Prim3 where show (P3 s _) = s

data Binop = OpPlus | OpTimes deriving Show

data Value = Clo TermB Env
           | VInt Int
           | VPair Value Value
           | VLeft Value
           | VRight Value
           | VUnit
           | FClo TermB Env
--             deriving Show
instance Show Value where
    show (VInt n) = show n
    show (Clo b e) = "Clo " ++  show b ++ show e
    show (FClo b e) = "Fix " ++  show b ++ show e
    show (VLeft a) = "<" ++ show a
    show (VRight a) = ">" ++ show a
    show (VPair a b) = "(" ++ show a ++ "," ++ show b ++ ")"
    show (VUnit) = "()"

-- 
data Dump = Dump Stack Env Control Dump
          | InitState
            deriving (Show)

type Sig = (Stack, Env, Control, Dump)

inject :: TermB -> Sig
inject e = ([], [], AE e Ret, InitState)

isFinal :: Sig -> Bool
isFinal (s:_, e, Ret, InitState)           = True
isFinal _ = False

-- Heart of SECD machine, transition rules
step :: Sig -> Sig

step (FClo b e' : s, e, c, d) = ([], e' ++ [FClo b e'], AE b Ret, Dump s e c d)
--
step ([s], e, Ret, (Dump s' e' c' d'))  = (s:s', e', c', d')
step (s, e, (AE (VarB i) c), d)      = (e !! i  : s, e, c, d)
step (s, e, (AE (AbsB b) c), d)      = (Clo b e : s, e, c, d)
step (s, e, (AE (LitB o) c), d)          = (VInt o : s, e, c, d)
step (Clo  b e' : s2 : ss, e, Call, d) = (ss, e' ++ [s2], AE b Ret, d)
step (s, e, (AE (AppB op arg) Ret), d) = (s, e, (AE arg $ AE op $ Call), d)
step (s, e, (AE (AppB op arg) c), d) = ([], e, (AE arg $ AE op $ Call), Dump s e c d)
--
step (          v1 : ss, e, (Prim1 (P1 _ f) c), d) = (f v1       : ss, e, c, d)
step (     v2 : v1 : ss, e, (Prim2 (P2 _ f) c), d) = (f v1 v2    : ss, e, c, d)
step (v3 : v2 : v1 : ss, e, (Prim3 (P3 _ f) c), d) = (f v1 v2 v3 : ss, e, c, d)
step (s, e, (AE (PlusB  a1 a2) c), d) = (s, e, (AE a1 $ AE a2 $ Prim2 (P2 "+" f) c), d) where f (VInt a) (VInt b) = VInt $ a + b
step (s, e, (AE (TimesB a1 a2) c), d) = (s, e, (AE a1 $ AE a2 $ Prim2 (P2 "*" f) c), d) where f (VInt a) (VInt b) = VInt $ a * b

step (s, e, (AE (ArticB a) c), d) = (s, e, (AE a c), d)
--
step (s, e, (AE (PairB a1 a2) c), d) = (s, e, (AE a1 $ AE a2 $ Prim2 (P2 "(,)" VPair) c), d)
step (s, e, (AE (ProjLB ab) c), d) = (s, e, (AE ab $ Prim1 (P1 ".L" f) c), d) where f (VPair a b) = a
step (s, e, (AE (ProjRB ab) c), d) = (s, e, (AE ab $ Prim1 (P1 ".R" f) c), d) where f (VPair a b) = b
step (s, e, (AE (InjLB a) c), d) = (s, e, (AE a $ Prim1 (P1 "<" VLeft ) c), d)
step (s, e, (AE (InjRB a) c), d) = (s, e, (AE a $ Prim1 (P1 ">" VRight) c), d)
step (s, e, (AE (CaseB a t f) c), d) = (s, e, (AE a $ CCase t f c), d)
step (VLeft  a : s, e, (CCase t _ c), d) = (s, e ++ [a], (AE t c), d)
step (VRight a : s, e, (CCase _ f c), d) = (s, e ++ [a], (AE f c), d)
--
step (s, e, (AE (FixB b) c), d) = (FClo b e : s, e, c, d)
--
step (s, e, (AE (UnitB) c), d) = (VUnit : s, e, c, d)


step (s, e, c, d) = error "crash"


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
