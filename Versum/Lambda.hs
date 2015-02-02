{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Lambda where

newtype Mu f = Mu {unMu :: f (Mu f)} 
deriving instance Show (f (Mu f)) => Show (Mu f)

instance Iso (f (Mu f)) (Mu f) where
    fwd = Mu
    rev = unMu

-- Incrementalized
newtype Incr a = IncrT (Either (() -> Incr a) a)

newtype Auth a = AuthT a
type Artic a = a
--instance Show a => Show (Artic a) where show (ArticT a) = "!(" ++ show a ++ ")"

class Iso a b | a -> b where
    fwd :: a -> b
    rev :: b -> a

--instance (Iso a b, Iso b c) => Iso a c where
--    fwd = fwd . fwd
--    rev = rev . rev

-- Simply typed lambda, in PHOAS style
-- Good for denotational semantics in Hask
-- Easier to write terms correctly
data Term v t where
    App :: Term v (a -> b) -> Term v a -> Term v b
    Var :: v t -> Term v t
    Abs :: (v a -> Term v b) -> Term v (a -> b)
    Lit :: Int -> Term v Int
    --
    Unit :: Term v ()
    --
    Plus  :: Term v Int -> Term v Int -> Term v Int
    Times :: Term v Int -> Term v Int -> Term v Int
    --
    --Auth :: Term v t -> Term v (Auth t)
    --UnAuth :: Term v (Auth t) -> Term v t
    Artic :: Term v t -> Term v (Artic t)
    --
    Fix :: (v t -> Term v t) -> Term v t
    --
    Fwd :: Iso a b => Term v a -> Term v b
    Rev :: Iso a b => Term v b -> Term v a
    --
    Case :: Term v (Either a b) -> (v a -> Term v t) -> (v b -> Term v t) -> Term v t
    InjL :: Term v a -> Term v (Either a b)
    InjR :: Term v b -> Term v (Either a b)
    --
    Pair :: Term v a -> Term v b -> Term v (a,b)
    ProjL :: Term v (a,b) -> Term v a
    ProjR :: Term v (a,b) -> Term v b
    --
    Tick :: Term v t -> Term v t
    Incr :: Term v t -> Term v (Incr t)
    Step :: Term v (Incr t) -> Term v (Either (Incr t) t)

-- Denotational semantics for Term
newtype Id t = Id {unId :: t}
denote :: Term Id t -> t
denote (Lit v) = v
denote (Var (Id v)) = v
denote (Abs f) = denote .f . Id
denote (App f x) = (denote f) (denote x)
denote (Plus x y) = denote x + denote y
denote (Times x y) = denote x * denote y
--
denote (Artic a) = denote a
--
--denote (Fix f) = denote f (denote (Fix f))
denote (Fix f) = denote (f (Id . denote $ Fix f))
--
denote (Fwd x) = fwd $ denote x
denote (Rev x) = rev $ denote x
--
denote (InjL a) = Left  (denote a)
denote (InjR b) = Right (denote b)
denote (Case x f g) = case denote x of 
                        Left  a -> denote (f $ Id a)
                        Right b -> denote (g $ Id b)
denote (Unit) = ()
--
denote (Pair a b) = (denote a, denote b)
denote (ProjL ab) = fst $ denote ab
denote (ProjR ab) = snd $ denote ab

-- Untyped lambda with De Bruijn indices
-- Easy to provide an abstract machine, hard to write terms
data TermB where
    AppB :: TermB -> TermB -> TermB
    VarB :: Int -> TermB
    AbsB :: TermB -> TermB
    LitB :: Int -> TermB
    PlusB :: TermB -> TermB -> TermB
    TimesB :: TermB -> TermB -> TermB
    --
    AuthB :: TermB -> TermB
    UnauthB :: TermB -> TermB
    -- 
    ArticB :: TermB -> TermB
    --
    FixB :: TermB -> TermB
    --
    UnitB :: TermB
    CaseB :: TermB -> TermB -> TermB -> TermB
    InjLB :: TermB -> TermB
    InjRB :: TermB -> TermB
    PairB :: TermB -> TermB -> TermB
    ProjLB :: TermB -> TermB
    ProjRB :: TermB -> TermB
    --


--deriving instance Show (TermB)
instance Show (TermB) where
    show (AppB f e) = "(" ++ show f ++ ")(" ++ show e ++ ")"
    show (VarB n) = "#" ++ show n
    show (AbsB e) = "Λ." ++ show e
    show (LitB n) = show n
    show (PlusB a b) = show a ++ "+" ++ show b
    show (TimesB a b) = show a ++ "*" ++ show b
    show (AuthB a) = "A(" ++ show a ++ ")"
    show (UnauthB a) = "U(" ++ show a ++ ")"
    show (ArticB a) = "!(" ++ show a ++ ")"
    show (CaseB x t f) = "(" ++ show x ++ ")?(" ++ show t ++ "):(" ++ show f ++ ")"
    show (InjLB a) = "<" ++ show a
    show (InjRB a) = ">" ++ show a
    show (PairB a b) = "(" ++ show a ++ "," ++ show b ++ ")"
    show (ProjLB a) = show a ++ ".L"
    show (ProjRB a) = show a ++ ".R"
    show (FixB f) = "Λrec." ++ show f
    show (UnitB) = "()"

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
-- Articulation point
debruijnize' (Artic x) off = ArticB (debruijnize' x off)
--
debruijnize' (Fix f) off = FixB (debruijnize' (f (K $ off + 1)) (off + 1))
--
debruijnize' (Case x a b) off = CaseB (debruijnize' x off) (debruijnize' (a $ K $ off + 1) (off+1)) (debruijnize' (b $ K $ off + 1) (off+1))
debruijnize' (InjL a) off = InjLB $ debruijnize' a off
debruijnize' (InjR b) off = InjRB $ debruijnize' b off
debruijnize' (Pair a b) off = PairB (debruijnize' a off) (debruijnize' b off)
debruijnize' (ProjL ab) off = ProjLB (debruijnize' ab off)
debruijnize' (ProjR ab) off = ProjRB (debruijnize' ab off)
debruijnize' (Fwd a) off = debruijnize' a off
debruijnize' (Rev a) off = debruijnize' a off
debruijnize' (Unit) off = UnitB

-- Example terms in Term

tDouble = Abs (\x -> Times (Lit 2) (Var x))
tSquare = Abs (\x -> Times (Var x) (Var x))
tApplyTwice = Abs $ \f -> Abs $ \x -> App (Var f) (App (Var f) (Var x))

--denoteTest = denote (App (App tApplyTwice tDouble) (Lit 3))

tNoBin = App (Abs $ \x -> Var x) (Lit 3)
tRedunant = Plus (App tSquare (Lit 3)) (App tSquare (Lit 3))

-- Terms with Art
tSquareArt = Abs (\x -> Artic $ Times (Var x) (Var x))
tRedunantArt = Plus (Artic $ App tSquareArt (Lit 3)) (Artic $ App tSquareArt (Lit 3))

newtype TList' a r = TList' {unT :: Either () (a, r)} deriving Show
type TList a = Mu (TList' a)
instance Iso (Either () (a, TList a)) (TList a) where
    fwd = Mu . TList'
    rev = unT . unMu

tNil :: Term v (TList a)
tNil = Fwd $ (InjL Unit :: forall v a. Term v (Either () (a, TList a)))

tCons' :: Term v a -> Term v (TList a) -> Term v (Either () (a, TList a))
tCons' a as = InjR $ Pair a as

tCons :: Term v a -> Term v (TList a) -> Term v (TList a)
tCons a as = Fwd $ tCons' a as

tInts :: [Int] -> Term v (TList Int)
tInts = foldr tCons tNil . map Lit


tProd :: Term v (TList Int -> Int)
tProd = Fix $ \f -> Abs $ \as -> 
        Case (Rev $ Var as)
                 ((\_ -> Lit 1) :: forall v. v () -> Term v Int) $
                 \as' -> Times (ProjL (Var as')) (App (Var f) (ProjR (Var as')))

-- denote $ App tProd (tInts [1..10])
