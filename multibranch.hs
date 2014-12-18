module Main where

import Prelude

import qualified Postructures as PS
import qualified Forging as FR
import qualified Data.ConfigFile as CF
import Data.Either.Utils

import Constants as Const

int2nat = FR.int2nat

sys0 = \tfdepth -> \nFixAccounts -> FR.sys tfdepth nFixAccounts (int2nat 0)

showsList :: Show a => (PS.List a) -> String -> String
showsList (PS.Nil) s = "[" ++ s ++ "]"
showsList (PS.Cons a l') s = Main.showsList l' (s ++ show a ++ ";")

showsTree :: Show a => (PS.LTree a) -> String -> String
showsTree (PS.Tgen x) s = "<" ++ show x ++ ">" ++ s
showsTree (PS.Tcons x t) s =  Main.showsTree t ("#" ++ show x ++ s) 
showsTree (PS.Tfork (PS.Tbranch t'') t') s = Main.showsTree t' ("@(" ++ (Main.showsTree t'' "") ++ ")" ++ s) 

instance Show a => Show (PS.List a) where
   showsPrec _ x = Main.showsList x

instance Show a => Show (PS.LTree a) where
   showsPrec _ x = Main.showsTree x
   
instance Show (PS.Nat) where   
  show n = Prelude.show (FR.nat2bn n)
  
deriving instance Prelude.Show (PS.Mhex)  
deriving instance Prelude.Show (PS.Hex)  
deriving instance Prelude.Show (PS.Bool)  

instance (Show a, Show b) => Show (PS.Prod a b) where   
  show (PS.Pair n m) = "(" ++ (show n) ++ "," ++ (show m) ++ ")" 
   
listout :: Show a => String -> PS.List a  -> IO()   
listout _ (PS.Nil) = return ()
listout filename (PS.Cons a l')  = do 
                           appendFile filename ((show a)++"\n")
                           listout filename l'
                           
printNode:: FR.Block -> Integer -> FR.System -> IO()
printNode gb0 n s = do
                  let sgl = FR.sysigns s
                  let sgn = PS.nth (int2nat n) sgl (PS.Tgen PS.N0)    
                  let len = FR.nat2bn (PS.ltreelen sgn)
                  let ltblocks = FR.sysblocks s
                  let blocksn = PS.nth (int2nat n) ltblocks (PS.Tgen gb0)     
                  --let dtimes = PS.fold1 ((-)) (PS.ltree_list_map PS.btimestamp blocks0)
                  let gens = FR.generators s
                  let gensn = PS.nth (int2nat n) gens (PS.Nil)    
                  let bt = PS.baseTarget (PS.lastnode blocksn) 
                  putStrLn (show gens)    
                  putStrLn (show sgn)
                  putStrLn (show len)
                  putStrLn (show bt)
                  putStrLn (show (PS.isMarkFollowing (PS.nth (int2nat n) (PS.sysaccs s) (PS.generator gb0))))
                  putStrLn (show (PS.isMarkUnfollowing (PS.nth (int2nat n) (PS.sysaccs s) (PS.generator gb0))))
                

simulate ::  FR.Block -> String -> FR.System -> Integer -> IO()
simulate gb0 outFile s' 0 =  do                
                  putStrLn ("----------------" ++ "Rebalanced:" ++ "----------------")                  
                  let s = FR.rebalance_sys s'
                  putStrLn ("Node 1:")
                  printNode gb0 0 s
                  putStrLn ("Node 2:")
                  printNode gb0 1 s
                  
                  let lblocks = FR.sysblocks s
                  let blocks0 = PS.nth (int2nat 0) lblocks (PS.Tgen gb0)                       
                  let dtimes = PS.fold1 ((-)) (PS.ltree_list_map PS.btimestamp blocks0)                      
                  writeFile outFile "" 
                  listout outFile dtimes
                  
                  putStrLn (show (PS.map PS.showblock (PS.ltree2list blocks0)))
                  {--| let sgl = FR.sysigns s
                  -let sg0 = PS.nth (int2nat 0) sgl (PS.Tgen PS.H0)    
                  let len = FR.nat2bn (PS.ltreelen sg0)
                  let lblocks = FR.sysblocks s
                  let blocks0 = PS.nth (int2nat 0) lblocks (PS.Tgen gb0)     
                  let dtimes = PS.fold1 ((-)) (PS.ltree_list_map PS.btimestamp blocks0)
                  writeFile outFile "" 
                  listout outFile dtimes
                  let gens = FR.generators s
                  let gens0 = PS.nth (int2nat 0) gens (PS.Nil)    
                  let bt = PS.baseTarget (PS.lastnode blocks0) 
                  putStrLn (show gens)    
                  putStrLn (show sg0)
                  putStrLn (show len)
                  putStrLn (show bt) --}
                  
simulate  gb0 outFile s n =  do 
                  putStrLn ("----------------" ++ show n ++ "----------------")                  
                  putStrLn ("Node 1:")
                  printNode gb0 0 s
                  putStrLn ("Node 2:")
                  printNode gb0 1 s
                  simulate gb0 outFile (FR.systemTransform s (int2nat 1)) (n-1)
   
readParam cp sec par = forceEither $ CF.get cp sec par

readAccounts:: CF.ConfigParser -> Integer -> Integer -> (PS.List
               (PS.Prod (PS.Prod (PS.Prod (PS.Prod FR.BN PS.Bool) PS.Bool) PS.Bool) (PS.Option PS.Nat)))
--               (PS.List (PS.Prod (PS.Prod FR.BN PS.Bool) (PS.Option PS.Nat)))
readAccounts _ 0 _ = PS.Nil
readAccounts cp n k = let isPublishing = FR.bool2bool (readParam cp ("Account " ++ show k) "isPublishing") in 
                      let bUseTFDepth = readParam cp ("Account " ++ show k) "bUseTFDepth" in
                      let nTFDepth = readParam cp ("Account " ++ show k) "nTFDepth" in
                      let tfdepth = if bUseTFDepth then PS.Some (int2nat nTFDepth) else PS.None in  
                      let nBalanceWeight = readParam cp ("Account " ++ show k) "nBalanceWeight" in
                      let isMarkable = FR.bool2bool (readParam cp ("Account " ++ show k) "isMarkable") in
                      let isMarkFollowing = FR.bool2bool (readParam cp ("Account " ++ show k) "isMarkFollowing") in
                      let accp = PS.Pair (PS.Pair (PS.Pair (PS.Pair nBalanceWeight isPublishing) isMarkable) isMarkFollowing) tfdepth in  
                      PS.Cons accp (readAccounts cp (n-1) (k+1)) 

main = do
     putStrLn "Reading configuration..."
     val <- CF.readfile CF.emptyCP Const.cfgfile
     let cp' = forceEither val
     let cp = cp' {CF.optionxform = id}    
     let nFixAccounts = readParam cp "Network" "nFixAccounts"
     let accountParams = readAccounts cp nFixAccounts 1
     let strTimesFileName = readParam cp "DEFAULT" "strTimesFileName"     
     let genesisState = FR.genesisState (int2nat nFixAccounts) accountParams    
         
     putStrLn "Enter the length of simulation in ticks:"
     str <- getLine
     let num = read str
     putStrLn "Starting cryptocurrency simulation..."
     simulate FR.genesisBlock strTimesFileName genesisState num
     putStrLn "Cryptocurrency simulation has been finished"


