-- This module is an excerpt of the module Data.Comp.Multi.Derive from the datacomp package.

{-# LANGUAGE TemplateHaskell #-}

module Derive where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad
import Data.Maybe
import HFixpoint
import NFunctor
import Language.Haskell.TH.ExpandSyns
import qualified Prelude as P
import Prelude
import Data.Monoid
import Data.Foldable (fold)
import Control.Applicative
import Data.Traversable (traverse)

{-| Helper function for generating a list of instances for a list of named
 signatures. For example, in order to derive instances 'Functor' and
 'ShowF' for a signature @Exp@, use derive as follows (requires Template
 Haskell):

 > $(derive [makeFunctor, makeShowF] [''Exp])
 -}
derive :: [Name -> Q [Dec]] -> [Name] -> Q [Dec]
derive ders names = liftM concat $ sequence [der name | der <- ders, name <- names]


containsType :: Type -> Type -> Bool
containsType s t
             | s == t = True
             | otherwise = case s of
                             ForallT _ _ s' -> containsType s' t
                             AppT s1 s2 -> containsType s1 t || containsType s2 t
                             SigT s' _ -> containsType s' t
                             _ -> False

containsType' :: Type -> Type -> [Int]
containsType' = run 0
    where run n s t
             | s == t = [n]
             | otherwise = case s of
                             ForallT _ _ s' -> run n s' t
                             -- only going through the right-hand side counts!
                             AppT s1 s2 -> run n s1 t ++ run (n+1) s2 t
                             SigT s' _ -> run n s' t
                             _ -> []


{-|
  This function returns the name of a bound type variable
-}
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _) = n


{-|
  This function provides a list (of the given length) of new names based
  on the given string.
-}
newNames :: Int -> String -> Q [Name]
newNames n name = replicateM n (newName name)


{-|
  This is the @Q@-lifted version of 'abstractNewtypeQ.
-}
abstractNewtypeQ :: Q Info -> Q Info
abstractNewtypeQ = liftM abstractNewtype

{-|
  This function abstracts away @newtype@ declaration, it turns them into
  @data@ declarations.
-}
abstractNewtype :: Info -> Info
abstractNewtype (TyConI (NewtypeD cxt name args constr derive))
    = TyConI (DataD cxt name args [constr] derive)
abstractNewtype owise = owise


{-|
  This function provides the name and the arity of the given data constructor.
-}
normalCon :: Con -> (Name,[StrictType])
normalCon (NormalC constr args) = (constr, args)
normalCon (RecC constr args) = (constr, map (\(_,s,t) -> (s,t)) args)
normalCon (InfixC a constr b) = (constr, [a,b])
normalCon (ForallC _ _ constr) = normalCon constr


normalCon' :: Con -> (Name,[Type])
normalCon' = fmap (map snd) . normalCon 


-- | Same as normalCon' but expands type synonyms.
normalConExp :: Con -> Q (Name,[Type])
normalConExp c = do 
  let (n,ts) = normalCon' c
  ts' <- mapM expandSyns ts
  return (n, ts')

iter 0 _ e = e
iter n f e = iter (n-1) f (f `appE` e)

iter' n f e = run n f e
    where run 0 _ e = e
          run m f e = let f' = iter (m-1) [|fmap|] f
                      in run (m-1) f (f' `appE` e)


prefix :: Int -> [a] -> [a]
prefix n l = take (length l - n) l

{-| Derive an instance of 'HFunctor' for a type constructor of any higher-order
  kind taking at least two arguments. -}
makeHFunctor :: Name -> Q [Dec]
makeHFunctor fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = init args
      fArg = VarT . tyVarBndrName $ last args'
      argNames = map (VarT . tyVarBndrName) (init args')
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''HFunctor) complType
  constrs' <- mapM (mkPatAndVars . isFarg fArg <=< normalConExp) constrs
  hfmapDecl <- funD 'hfmap (map hfmapClause constrs')
  return [InstanceD [] classType [hfmapDecl]]
      where isFarg fArg (constr, args) = (constr, map (`containsType'` fArg) args)
            filterVar _ nonFarg [] x  = nonFarg x
            filterVar farg _ [depth] x = farg depth x
            filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat = VarP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           \ f g -> filterVars args varNs (\ d x -> f d (varE x)) (g . varE),
                           any (not . null) args, map varE varNs, catMaybes $ filterVars args varNs (curry Just) (const Nothing))
            hfmapClause (con, pat,vars',hasFargs,_,_) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       vars = vars' (\d x -> iter d [|fmap|] f `appE` x) id
                   body <- foldl appE con vars
                   return $ Clause [fp, pat] (NormalB body) []


{-| Derive an instance of 'NFunctor' for a type constructor of any higher-order
  kind taking at least two arguments. -}
makeNFunctor :: Name -> Q [Dec]
makeNFunctor fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = prefix 4 args
      fArg = VarT . tyVarBndrName $ last args'
      argNames = map (VarT . tyVarBndrName) (init args')
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''NFunctor) complType
  constrs' <- mapM (mkPatAndVars . isFarg fArg <=< normalConExp) constrs
  nfmapDecl <- funD 'nfmap (map nfmapClause constrs')
  return [InstanceD [] classType [nfmapDecl]]
      where isFarg fArg (constr, args) = (constr, map (`containsType'` fArg) args)
            filterVar _ nonFarg [] x  = nonFarg x
            filterVar farg _ [depth] x = farg depth x
            filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat = VarP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           \ f g -> filterVars args varNs (\ d x -> f d (varE x)) (g . varE),
                           any (not . null) args, map varE varNs, catMaybes $ filterVars args varNs (curry Just) (const Nothing))
            nfmapClause (con, pat,vars',hasFargs,_,_) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       vars = vars' (\d x -> iter d [|fmap|] f `appE` x) id
                   body <- foldl appE con vars
                   return $ Clause [fp, pat] (NormalB body) []

{-| Derive an instance of 'HFoldable' for a type constructor of any higher-order
  kind taking at least two arguments. -}
makeNFoldable :: Name -> Q [Dec]
makeNFoldable fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = prefix 4 args
      fArg = VarT . tyVarBndrName $ last args'
      argNames = map (VarT . tyVarBndrName) (init args')
      complType = P.foldl AppT (ConT name) argNames
      classType = AppT (ConT ''NFoldable) complType
  constrs' <- mapM (mkPatAndVars . isFarg fArg <=< normalConExp) constrs
  foldrDecl <- funD 'nfoldr (map foldrClause constrs')
  return [InstanceD [] classType [foldrDecl]]
      where isFarg fArg (constr, args) = (constr, map (`containsType'` fArg) args)
            filterVar [] _ = Nothing
            filterVar [d] x =Just (d, varE x)
            filterVar _ _ =  error "functor variable occurring twice in argument type"
            filterVars args varNs = catMaybes $ zipWith filterVar args varNs
            mkCPat constr args varNs = ConP constr $ zipWith mkPat args varNs
            mkPat [] _ = WildP
            mkPat _ x = VarP x
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (mkCPat constr args varNs, filterVars args varNs)
            foldrClause (pat,vars) =
                do fn <- newName "f"
                   en <- newName "e"
                   let f = varE fn
                       e = varE en
                       fp = if null vars then WildP else VarP fn
                       ep = VarP en
                       conApp (0,x) y = [|$f $x $y|]
                       conApp (1,x) y = [|foldr $f $y $x |]
                       conApp (d,x) y = let hidEndo = iter (d-1) [|fmap|] [|Endo . flip (foldr $f)|] `appE` x
                                            endo = iter' (d-1) [|fold|] hidEndo
                                        in [| appEndo $endo $y|]
                   body <- P.foldr conApp e vars
                   return $ Clause [fp, ep, pat] (NormalB body) []

makeNTraversable :: Name -> Q [Dec]
makeNTraversable fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = prefix 4 args
      fArg = VarT . tyVarBndrName $ last args'
      argNames = map (VarT . tyVarBndrName) (init args')
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''NTraversable) complType
  constrs' <- P.mapM (mkPatAndVars . isFarg fArg <=< normalConExp) constrs
  traverseDecl <- funD 'ntraverse (map traverseClause constrs')
  mapMDecl <- funD 'nmapM (map mapMClause constrs')
  return [InstanceD [] classType [traverseDecl, mapMDecl]]
      where isFarg fArg (constr, args) = (constr, map (`containsType'` fArg) args)
            filterVar _ nonFarg [] x  = nonFarg x
            filterVar farg _ [depth] x = farg depth x
            filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat = VarP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           \f g -> filterVars args varNs (\ d x -> f d (varE x)) (g . varE),
                           any (not . null) args, map varE varNs, catMaybes $ filterVars args varNs (curry Just) (const Nothing))
            traverseClause (con, pat,vars',hasFargs,_,_) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       vars = vars' (\d x -> iter d [|traverse|] f `appE` x) (\x -> [|pure $x|])
                   body <- P.foldl (\ x y -> [|$x <*> $y|]) [|pure $con|] vars
                   return $ Clause [fp, pat] (NormalB body) []
            -- Note: the monadic versions are not defined
            -- applicatively, as this results in a considerable
            -- performance penalty (by factor 2)!
            mapMClause (con, pat,_,hasFargs,allVars, fvars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       conAp = P.foldl appE con allVars
                       conBind (d,x) y = [| $(iter d [|mapM|] f) $(varE x)  >>= $(lamE [varP x] y)|]
                   body <- P.foldr conBind [|return $conAp|] fvars
                   return $ Clause [fp, pat] (NormalB body) []
