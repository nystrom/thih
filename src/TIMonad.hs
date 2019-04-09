-----------------------------------------------------------------------------
-- TIMonad:     Type inference monad
-- 
-- Part of `Typing Haskell in Haskell', version of November 23, 2000
-- Copyright (c) Mark P Jones and the Oregon Graduate Institute
-- of Science and Technology, 1999-2000
-- 
-- This program is distributed as Free Software under the terms
-- in the file "License" that is included in the distribution
-- of this software, copies of which may be obtained from:
--             http://www.cse.ogi.edu/~mpj/thih/
-- 
-----------------------------------------------------------------------------

module TIMonad where
import Id
import Kind
import Type
import Subst
import Unify
import Pred
import Scheme
import Control.Monad.State

type TI a = State (Subst, Int) a

runTI       :: TI a -> a
runTI f = x where (x, (s,n)) = runState f (nullSubst, 0)

getSubst   :: TI Subst
getSubst    = do { (s,n) <- get; return s }

unify      :: Type -> Type -> TI ()
unify t1 t2 = do s <- getSubst
                 u <- mgu (apply s t1) (apply s t2)
                 extSubst u

extSubst   :: Subst -> TI ()
extSubst s' = do
  (s, n) <- get
  put (s'@@s, n)

trim       :: [Tyvar] -> TI ()
trim vs     = do
  (s, n) <- get
  let s' = [ (v,t) | (v,t) <- s, v `elem` vs ]
      force = length (tv (map snd s'))
  force `seq` (put (s', n))

newTVar    :: Kind -> TI Type
newTVar k   = do
  (s, n) <- get
  let v = Tyvar (enumId n) k
  put (s, n+1)
  return (TVar v)

freshInst               :: Scheme -> TI (Qual Type)
freshInst (Forall ks qt) = do ts <- mapM newTVar ks
                              return (inst ts qt)

class Instantiate t where
  inst  :: [Type] -> t -> t
instance Instantiate Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen n)  = ts !! n
  inst ts t         = t
instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
instance Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t
instance Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)

-----------------------------------------------------------------------------
