module Main where

import Prelude

import qualified Postructures as PS
import qualified Forging as FR
import qualified Data.ConfigFile as CF
import Data.Either.Utils

import Constants as Const

int2nat :: Integer -> PS.Nat
int2nat 0 = PS.O
int2nat m = PS.S (int2nat (m-1))

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
  
deriving instance Prelude.Show (PS.Hex)  
  
instance (Show a, Show b) => Show (PS.Prod a b) where   
  show (PS.Pair n m) = "(" ++ (show n) ++ "," ++ (show m) ++ ")" 
   
listout :: Show a => String -> PS.List a  -> IO()   
listout _ (PS.Nil) = return ()
listout filename (PS.Cons a l')  = do 
                           appendFile filename ((show a)++"\n")
                           listout filename l'

simulate :: PS.Option PS.Nat -> PS.Nat -> String ->  Integer -> FR.System -> IO()
simulate tfdepth nFixAccounts outFile 0 s' =  do                
                  putStrLn ("----------------" ++ "Rebalanced:" ++ "----------------")                  
                  let s = FR.rebalance_sys s'
                  let sgl = FR.sysigns s
                  let sg0 = PS.nth (int2nat 0) sgl (PS.Tgen PS.H0)    
                  let len = FR.nat2bn (PS.ltreelen sg0)
                  let lblocks = FR.sysblocks s
                  let blocks0 = PS.nth (int2nat 0) lblocks (PS.Tgen (FR.genesisBlock nFixAccounts))     
                  let dtimes = PS.fold1 ((-)) (PS.ltree_list_map PS.btimestamp blocks0)
                  writeFile outFile "" 
                  listout outFile dtimes
                  let gens = FR.generators s
                  let gens0 = PS.nth (int2nat 0) gens (PS.Nil)    
                  let bt = PS.baseTarget (PS.lastnode blocks0) 
                  putStrLn (show gens)    
                  putStrLn (show sg0)
                  putStrLn (show len)
                  putStrLn (show bt)
                  
simulate tfdepth nFixAccounts outFile n s =  do 
                  putStrLn ("----------------" ++ show n ++ "----------------")                  
                  let sgl = FR.sysigns s
                  let sg0 = PS.nth (int2nat 0) sgl (PS.Tgen PS.H0)    
                  let len = FR.nat2bn (PS.ltreelen sg0)
                  let lblocks = FR.sysblocks s
                  let blocks0 = PS.nth (int2nat 0) lblocks (PS.Tgen (FR.genesisBlock nFixAccounts))     
                  let dtimes = PS.fold1 ((-)) (PS.ltree_list_map PS.btimestamp blocks0)
                  let gens = FR.generators s
                  let gens0 = PS.nth (int2nat 0) gens (PS.Nil)    
                  let bt = PS.baseTarget (PS.lastnode blocks0) 
                  putStrLn (show gens)    
                  putStrLn (show sg0)
                  putStrLn (show len)
                  putStrLn (show bt)
                  simulate tfdepth nFixAccounts outFile (n-1) (FR.systemTransform tfdepth s (int2nat 1))
   
readParam cp sec par = forceEither $ CF.get cp sec par

main = do
     putStrLn "Reading configuration..."
     val <- CF.readfile CF.emptyCP Const.cfgfile
     let cp' = forceEither val
     let cp = cp' {CF.optionxform = id}    
     let bUseTFDepth = readParam cp "Forging" "bUseTFDepth"
     let nTFDepth = readParam cp "Forging" "nTFDepth"
     let nFixAccounts = readParam cp "Network" "nFixAccounts"
     let tfdepth = if bUseTFDepth then PS.Some (int2nat nTFDepth) else PS.None  
     let strTimesFileName = readParam cp "DEFAULT" "strTimesFileName"
         
     putStrLn "Enter the length of simulation in ticks:"
     str <- getLine
     let num = read str
     putStrLn "Starting cryptocurrency simulation..."
     simulate tfdepth (int2nat nFixAccounts) strTimesFileName num (FR.genesisState (int2nat nFixAccounts))
     putStrLn "Cryptocurrency simulation has been finished"


