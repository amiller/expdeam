{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances, DeriveFunctor #-}
module Lambda where
import Control.Monad
import Control.Applicative
import Control.Monad.Identity

{--- Yield and Suspended are a monad ---}
data Yield r = Yield { unY :: (forall a. (r -> Suspended a) -> Suspended a) }
instance Show (Yield r) where
    show _ = "Yield"
yield :: Yield ()
yield = Yield $ \k -> (Susp k)
run :: Yield r -> Suspended r
run (Yield e) = e Done

next :: Suspended a -> Suspended a
next (Done a) = (Done a)
next (Susp a) = a ()

force :: Suspended a -> a
force (Done a) = a
force (Susp a) = force $ next $ a ()

collect :: Suspended a -> [Suspended a]
collect (Done a) = [Done a]
collect (Susp f) = (Susp f) : collect (f ())


fromLeft (Left a) = a
fromRight (Right a) = a

liftSusp :: Suspended a -> Suspended (Yield a)
liftSusp (Done a) = Done (return a)
liftSusp (Susp a) = Susp (liftSusp . a)

lowerSusp :: Suspended (Yield a) -> Suspended a
lowerSusp (Done a) = run a
lowerSusp (Susp a) = Susp (lowerSusp . a)

data Suspended a = Done {result :: a} | Susp (() -> Suspended a)
instance Show a => Show (Suspended a) where
    show (Done r) = "Result: " ++ show r
    show (Susp _) = "Susp"

deriving instance Functor Yield
instance Applicative Yield where
    pure = return
    (<*>) = ap

instance Monad Yield where
    return e = Yield ( \k -> k e )
    ( Yield e ) >>= f = Yield ( \ k -> e ( \ v -> ( unY ( f v ) ) k ) )


-- Simply typed lambda, in PHOAS style
-- Good for denotational semantics in Hask
-- Easier to write terms correctly
data Term v t where
    App :: Term v (a -> v b) -> Term v a -> Term v b
    Var :: v t -> Term v t
    Abs :: (v a -> Term v b) -> Term v (a -> v b)
    Lit :: Int -> Term v Int
    --
    Unit :: Term v ()
    --
    Plus  :: Term v Int -> Term v Int -> Term v Int
    Times :: Term v Int -> Term v Int -> Term v Int
    --
    Tick :: Term v t -> Term v t
    Div :: Term v t -> Term v (Suspended t)
    Step :: Term v (Suspended t) -> Term v (Either t (Suspended t))

-- Denotational semantics for (non-suspendable fragment of) Term
newtype Id t = Id {unId :: t} deriving Show
denote :: Term Id t -> t
denote (Lit v) = v
denote (Var (Id v)) = v
denote (Abs f) = Id . denote .f . Id
denote (App f x) = (unId . denote f) (denote x)
denote (Plus x y) = denote x + denote y
denote (Times x y) = denote x * denote y
denote (Tick e) = denote e
-- The only way for this semantics to finish is to always finish in one step... not what's intended
denote (Div e) = Done $ denote e
denote (Step e) = let (Done e') = denote e in Left e'

-- Parametric Monadic semantics
denoteM :: Term Yield t -> Yield t
--denoteM (Div e) = let e' = (denoteM''' $ denoteM'' e) in return undefined --let e' = denoteM'' e in undefined
denoteM (Lit v) = return v
denoteM (Var v) = v
denoteM (Abs f) = return $ denoteM . f . return
denoteM (App f x) = do { f' <- denoteM f; denoteM x >>= f' }
denoteM (Plus x y) = do { x' <- denoteM x; y' <- denoteM y; return $ x' + y' }
denoteM (Times x y) = do { x' <- denoteM x; y' <- denoteM y; return $ x' * y' }
denoteM (Tick e) = yield >> denoteM e
denoteM (Div e) = return $ run $ denoteM e
denoteM (Step e) = do
  x <- denoteM e
  case x of
    Done a -> return $ Left a
    Susp a -> return $ Right (a ())


-- Untyped lambda with De Bruijn indices
-- Easy to provide an abstract machine, hard to write terms
data TermB where
    AppB :: TermB -> TermB -> TermB
    VarB :: Int -> TermB
    AbsB :: TermB -> TermB
    LitB :: Int -> TermB
    PlusB :: TermB -> TermB -> TermB
    TimesB :: TermB -> TermB -> TermB


--deriving instance Show (TermB)
instance Show (TermB) where
    show (AppB f e) = "(" ++ show f ++ ")(" ++ show e ++ ")"
    show (VarB n) = "#" ++ show n
    show (AbsB e) = "Λ." ++ show e
    show (LitB n) = show n
    show (PlusB a b) = show a ++ "+" ++ show b
    show (TimesB a b) = show a ++ "*" ++ show b

-- Compiler from TermT to Term
newtype K k a = K {unK :: k}
debruijnize t = debruijnize' t (-1)
debruijnize' :: Term (K Int) a -> Int -> TermB
debruijnize' (Lit n) _ = LitB n
debruijnize' (Var (K n)) _ = VarB n
debruijnize' (App f x) off = AppB (debruijnize' f off) (debruijnize' x off)
debruijnize' (Abs f) off = AbsB (debruijnize' (f (K $ off + 1)) (off+1))
debruijnize' (Plus x y) off = PlusB (debruijnize' x off) (debruijnize' y off)
debruijnize' (Times x y) off = TimesB (debruijnize' x off) (debruijnize' y off)

-- Example terms in Term
tDouble = Abs (\x -> Times (Lit 2) (Var x))
tSquare = Abs (\x -> Times (Var x) (Var x))
tApplyTwice = Abs $ \f -> Abs $ \x -> App (Var f) (App (Var f) (Var x))

--denoteTest = denote (App (App tApplyTwice tDouble) (Lit 3))

tNoBin = App (Abs $ \x -> Var x) (Lit 3)
tRedunant = Plus (App tSquare (Lit 3)) (App tSquare (Lit 3))

tDivTest = Step $ App (Abs (\x -> Div (Tick $ Tick $ Tick $ Tick $ Var x))) (Lit 3)

--undenote :: Either (Yield a) (Yield (Suspended (Yield a))) -> Suspended a
--undenote (Left a) = run a
--undenote (Right a) = lowerSusp (run a)
