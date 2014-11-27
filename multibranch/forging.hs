module Forging where

import Prelude
import qualified Postructures as PS
import qualified Constants as Const

data Stream a =
   Cons0 a (Stream a)

hd :: (Stream a1) -> a1
hd x =
  case x of {
   Cons0 a s -> a}

tl :: (Stream a1) -> Stream a1
tl x =
  case x of {
   Cons0 a s -> s}

str_nth_tl :: Integer -> (Stream a1) -> Stream a1
str_nth_tl 0 s = s 
str_nth_tl m s = str_nth_tl (m-1) (tl s)

str_nth :: Integer -> (Stream a1) -> a1
str_nth n s =
  hd (str_nth_tl n s)

type BN = Integer
type Digest = PS.HexN
dig2string = id
hashfun = id
modN = mod
multN = (*) 
divN = div
doubleN = (*) 2 
succN = (+) 1

nat2bn :: PS.Nat -> Integer
nat2bn PS.O = 0
nat2bn (PS.S n') = 1 + (nat2bn n')

bN0 = 0

bool2bool :: Prelude.Bool -> PS.Bool
bool2bool True = PS.True
bool2bool False = PS.False

geN :: BN -> BN -> PS.Bool
geN x y = bool2bool (x>=y)

plusN = (+)

rand :: Integer -> Integer -> Integer -> Stream Integer
rand seed n1 n2 =  let seed' = modN seed n2 in 
                       Cons0 seed' (rand (seed' * n1) n1 n2)
                                              
randStream :: Integer -> Stream Integer 
randStream n = rand n Const.iterRand Const.maxRand

type Block = PS.Block0 BN
type Account = PS.Account0 BN
type Timestamp = PS.Timestamp BN
type Transaction = PS.Transaction0 BN
type Currency = PS.Currency BN
type System = PS.System0 BN

validate :: Transaction -> PS.Bool
validate _ = PS.True

initialBaseTarget = PS.initialBaseTarget multN divN doubleN Const.systemBalance Const.goalBlockTime Const.maxRand
maxBaseTarget = PS.maxBaseTarget multN divN doubleN Const.systemBalance Const.goalBlockTime Const.maxRand

calcGenerationSignature = PS.calcGenerationSignature dig2string hashfun


formBlock_orig :: Block -> Account -> Timestamp -> PS.List Transaction -> PS.HexSPK -> Block
formBlock_orig pb acc ts txs pk =
  let pbt = PS.baseTarget pb in
  let vtxs = PS.filter validate txs in
  let maxTarget = min (2*pbt) maxBaseTarget in
  let minTarget = max (div pbt 2) 1 in
  let candidate = div (pbt*(ts-(PS.btimestamp  pb))) Const.goalBlockTime in
  let bt = min (max minTarget candidate) maxTarget in
  let gs = calcGenerationSignature pb acc in
  PS.Block  vtxs bt acc gs ts

 
mthcl_gamma = 0.1 
mthcl_invbeta = 1.0-mthcl_gamma/2.0
  
formBlock_mthcl :: Block -> Account -> Timestamp -> PS.List Transaction -> PS.HexSPK -> Block
formBlock_mthcl pb acc ts txs pk =
  let pbt = PS.baseTarget pb in
  let vtxs = PS.filter validate txs in
  let dt = fromInteger (ts-(PS.btimestamp  pb)) / (fromInteger Const.goalBlockTime) in
  let kbt = if dt >= 2.0 then 2.0 else if dt > 1.0 then dt else if dt>0.5 then (1.0-mthcl_gamma*(1.0-dt)) else mthcl_invbeta in
  let bt = max 100 (truncate (kbt*(fromInteger pbt))) in
  let gs = calcGenerationSignature pb acc in
  PS.Block  vtxs bt acc gs ts  


formBlock  = formBlock_orig

block_difficulty = \ _ -> 1

-- block_difficulty = PS.baseTarget

minRand = div Const.maxRand 3

calculateHit_orig :: Account -> Block -> BN
calculateHit_orig acc pb = 
   str_nth (PS.btimestamp pb + 1) (randStream (nat2bn (PS.hex2nat (PS.publicKey acc))))

calculateHit_mthcl :: Account -> Block -> BN
calculateHit_mthcl acc pb = 
                       let pp = str_nth (PS.btimestamp pb + 1) (randStream (nat2bn (PS.hex2nat (PS.publicKey acc)))) in
                       let ppd = fromInteger pp in
                       let lpd = (log ((fromInteger Const.maxRand)/ ppd))*1000000000000000 in
                       let hitd = min (truncate lpd) (2*Const.maxRand) in
                       hitd

calculateHit = calculateHit_orig

verifyHit :: BN -> Block -> Timestamp -> Currency -> PS.Bool 
verifyHit hit pb ts effpb =  let eta = (ts - (PS.btimestamp pb)) in
                             let effbt = effpb*(PS.baseTarget pb) in
                             let target = effbt*eta in
                             bool2bool ((0 < eta) && (hit < target))
        
type Node = PS.Node0 BN

canforge :: Node -> Timestamp -> Block -> PS.Bool
canforge n ts pb = verifyHit (calculateHit (PS.node_account n) pb) pb ts (PS.effectiveBalance (PS.node_account n))
                    
-- succN dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge tfdepth sys0 count                   
systemTransform = PS.systemTransform 
                   succN dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge

genesisBlock = \nFixAccounts -> PS.genesisBlock multN divN doubleN nat2bn 0 nFixAccounts Const.systemBalance Const.goalBlockTime Const.maxRand
genesisState = \nFixAccounts -> PS.genesisState multN divN doubleN nat2bn 0 nFixAccounts Const.systemBalance Const.goalBlockTime Const.maxRand 

sys = \tfdepth -> \nFixAccounts -> PS.sys  
   multN divN doubleN succN nat2bn dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge tfdepth nFixAccounts 
   Const.systemBalance Const.goalBlockTime Const.maxRand 
                    
signs =  \tfdepth -> \nFixAccounts -> PS.signs  
   multN divN doubleN succN nat2bn dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge tfdepth nFixAccounts 
   Const.systemBalance Const.goalBlockTime Const.maxRand   
              
        
rebalance_sys = PS.rebalance_sys block_difficulty bN0 geN plusN                      
 
sysigns = PS.sysigns

sysblocks = PS.sysblocks

generators = PS.generators