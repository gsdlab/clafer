{-# LANGUAGE NamedFieldPuns #-}

module Language.Clafer.Generator.Choco (genCModule) where

import Language.Clafer.Intermediate.ScopeAnalyzer
import Control.Monad
import Control.Monad.Writer
import Data.List
import Data.Maybe
import Prelude hiding (exp)
import System.Process
import Language.Clafer.ClaferArgs
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Debug.Trace


genCModule :: ClaferArgs -> (IModule, GEnv) -> Result
genCModule _ (imodule@IModule{mDecls}, _) =
    (genConcreteClafer =<< concreteClafers)
    ++ (genAbstractClafer =<< abstractClafers)
    -- "Prints the solution.
    ++ "function solution() {\n"
    ++ "    solution__root(1, \"\");\n"
    ++ "}\n"
    ++ "\n"
    ++ (genToString =<< concreteClafers)
    where
    root :: IClafer
    root = IClafer noSpan False Nothing "root" "root" (ISuper False [PExp Nothing "" noSpan $ IClaferId "clafer" "clafer" True]) (Just (1, 1)) (0, 0) mDecls
    
    toplevelClafers = mapMaybe iclafer mDecls
    abstractClafers = filter isAbstract toplevelClafers
    parentChildMap = childClafers root
    clafers = root : map snd parentChildMap
    concreteClafers = filter (not . isAbstract) clafers
    minusRoot = filter ((/= "root") . uid)
    
    claferWithUid u = fromMaybe (error $ "claferWithUid: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . uid) clafers
    
    -- All abstract clafers u inherits
    supersOf u =
        case super $ claferWithUid u of
            ISuper False [PExp{exp = IClaferId{sident}}]
                | sident == "clafer" -> []
                | otherwise          -> sident : supersOf sident
            _ -> []
    -- All concrete clafers that inherit u
    subsOf u = [uid | IClafer{uid} <- concreteClafers, u `elem` supersOf uid]
    subClafersOf = map claferWithUid . subsOf

    parentOf u = fst $ fromMaybe (error $ "parentOf: \"" ++ u ++ "\" is not a clafer") $ find ((== u) . uid . snd) parentChildMap
    parentClaferOf = claferWithUid . parentOf
    -- Direct childrens
    childrenOf = map uid . childrenClaferOf
    childrenClaferOf u = [c | (p, c) <- parentChildMap, p == u]
    
    -- Indirect childrens
    indirectChildrenOf u = childrenOf =<< supersOf u
    indirectChildrenClaferOf u = childrenClaferOf =<< supersOf u
    
    genConcreteClafer :: IClafer -> Result
    genConcreteClafer IClafer{uid} =
        do
            IClafer{isAbstract, uid = cuid, card}  <- childrenClaferOf uid
            guard $ not isAbstract
            let scope = scopeOf uid
            let cScope = scopeOf cuid
            let name = "__" ++ cuid
            cuid ++ " = set(\"" ++ cuid ++ "\", 1, " ++ show cScope ++ ");\n"
                ++ genClafer' uid scope name cScope card
                ++ "partition(" ++ cuid ++ ", " ++ name ++ ");\n"
                ++ "\n"
    genAbstractClafer :: IClafer -> Result
    genAbstractClafer IClafer{uid} =
        do
            IClafer{isAbstract, uid = cuid, card}  <- childrenClaferOf uid
            let subs = subsOf uid
            let sScopes = map scopeOf subs
            let cScope = scopeOf cuid
            let names = ["__" ++ cuid ++ "__" ++ sub | sub <- subs]
            cuid ++ " = set(\"" ++ cuid ++ "\", 1, " ++ show cScope ++ ");\n"
                ++ concat [genClafer' suid sScope name cScope card | (suid, sScope, name) <- zip3 subs sScopes names]
                ++ "partition(" ++ cuid ++ ", " ++ concatArrays names ++ ");\n"
                ++ "\n"
        where
        concatArrays [x] = x
        concatArrays (x : xs) = x ++ ".concat(" ++ intercalate ", " xs ++ ")"
    genClafer' parent parentScope uid scope card =
        uid ++ " = setArray(\"" ++ uid ++ "\", " ++ show parentScope ++ ", 1, " ++ show scope ++ ");\n"
        ++ "for (var i = 0; i < " ++ uid ++ ".length; i++) {\n"
        ++
            case card of
                Just (low, -1)   ->
                    "    addConstraint(implies(member(i + 1 , " ++ parent ++ "), geqCard(" ++ uid ++ "[i], " ++ show low ++ ")));\n"
                Just (low, high)
                    | low == high ->
                        "    addConstraint(implies(member(i + 1, " ++ parent ++ "), eqCard(" ++ uid ++ "[i], " ++ show low ++ ")));\n"
                    | otherwise   ->
                        "    addConstraint(implies(member(i + 1, " ++ parent ++ "), and(geqCard(" ++ uid ++ "[i], " ++ show low ++ "), leqCard(" ++ uid ++ "[i], " ++ show high ++ "))));\n"
        ++ "    addConstraint(implies(notMember(i + 1, " ++ parent ++ "), eqCard(" ++ uid ++ "[i], 0)));\n"
        ++ "}\n"


    genToString :: IClafer -> Result
    genToString c@IClafer{ident, uid = puid, elements} =
        "function solution__" ++ puid ++ "(parent, indent) {\n"
        ++ "    var i = getVar(" ++ name ++ "[parent - 1]).getValue();\n"
        ++ "    for (var j in i) {\n"
        ++ "        var k = i[j];\n"
        ++ "        println(indent + \"" ++ ident ++ "\" + k);\n"
        ++ concat ["        solution__" ++ cuid ++ "(k, \"    \" + indent);\n" | IClafer{uid = cuid} <- children]
        ++ concat [
            "        __" ++ cuid ++ " = __" ++ cuid ++ "__" ++ puid ++ ";\n"
            ++ "        solution__" ++ cuid ++ "(k, \"    \" + indent);\n"
            | IClafer{uid = cuid} <- indirectChildren]
        ++ "    }\n"
        ++ "}\n"
        ++ "\n"
        where
        name = "__" ++ puid
        children = filter isNotAbstract $ childrenClaferOf puid
        indirectChildren = filter isNotAbstract $ indirectChildrenClaferOf puid
                
    scopeOf i = fromMaybe 1 $ lookup i scopes
    scopes = scopeAnalysis imodule


isNotAbstract :: IClafer -> Bool
isNotAbstract = not . isAbstract

iclafer :: IElement -> Maybe IClafer
iclafer (IEClafer c) = Just c
iclafer _ = Nothing

childClafers :: IClafer -> [(String, IClafer)]
childClafers IClafer{uid, elements} =
    childClafers' uid =<< mapMaybe iclafer elements
    where
    childClafers' parent c@IClafer{uid, elements} = (parent, c) : (childClafers' uid  =<< mapMaybe iclafer elements)

implies :: MonadPlus m => Bool -> m a -> m a
implies cond result = if cond then result else mzero
