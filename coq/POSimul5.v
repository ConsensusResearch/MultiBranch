Require Export POStructures.
Require Export NArith.
Local Open Scope N_scope.
Require Export Coq.Lists.Streams.

Let BN := N.
Let Digest := HexN.
Let dig2string := @id HexN.
Let hashfun := @id HexN.
Let modN := Nmod.
Let multN := Nmult. 
Let divN := Ndiv.
Let doubleN := multN 2%N.
Let succN := Nplus 1%N.
Let nat2bn := N.of_nat.
Let BN0 := 0%N.
Let geN x y := negb (N.ltb x y).
Let plusN := Nplus.
Let MaxRand := 99194853094755497%N.

CoFixpoint rand (seed n1 n2 : N) : Stream N :=
    let seed' := Nmod seed n2 in Cons seed' (rand (seed' * n1) n1 n2).

Let RandStream n := rand n 3093215881333057%N MaxRand.

Let systemBalance := 1000000000%N.
Let goalBlockTime := 10%N.

Print genesisBlock.
Print genesisState.

Let nFixAccounts := 10%nat.

Let genesisBlock := genesisBlock BN multN divN doubleN nat2bn 0 nFixAccounts systemBalance goalBlockTime MaxRand.
Let genesisState := genesisState BN multN divN doubleN nat2bn 0 nFixAccounts systemBalance goalBlockTime MaxRand.
Let Block:= Block BN.
Let Account := Account BN.
Let Timestamp := Timestamp BN.
Let Transaction := Transaction BN.
Definition validate  (t: Transaction) : bool := true.
Let initialBaseTarget := initialBaseTarget BN multN divN doubleN systemBalance goalBlockTime MaxRand.
Let maxBaseTarget := maxBaseTarget BN multN divN doubleN systemBalance goalBlockTime MaxRand.

Print calcGenerationSignature.

Let calcGenerationSignature := calcGenerationSignature BN Digest dig2string hashfun.
Check block.

Definition formBlock (pb: Block) (acc: Account) (ts: Timestamp) (txs: list Transaction) 
                                                (pk: HexSPK) : Block :=
  let pbt := baseTarget BN pb in
  let vtxs := filter validate txs in
  let maxTarget := N.min (2*pbt) maxBaseTarget in
  let minTarget := N.max (pbt/2) 1 in
  let candidate := (pbt*(ts-(btimestamp BN pb)))/goalBlockTime in
  let bt := N.min (N.max minTarget candidate) maxTarget in
  let gs := calcGenerationSignature pb acc in
  block BN vtxs bt acc gs ts.

Let block_difficulty:= baseTarget BN.

Print systemTransform.

Definition calculateHit (acc: Account) (pb: Block) := 
   Str_nth (N.to_nat (btimestamp BN pb + 1)) (RandStream (hex2N (publicKey BN acc))).

Definition verifyHit (hit: BN) (pb: Block) (ts: Timestamp) (effpb: Currency BN)  := 
let eta := ts - btimestamp BN pb in
let effbt := effpb*(baseTarget BN pb) in
let target := effbt*eta in
    andb (0 <? eta) (hit <? target).

Let canforge n ts pb := verifyHit (calculateHit (node_account BN n) pb) pb ts (effectiveBalance BN (node_account BN n)).
 
Print systemTransform.

Let tfdepth := Some 10%nat.

Let systemTransform := systemTransform BN succN Digest dig2string hashfun formBlock block_difficulty BN0 geN plusN canforge tfdepth.
 
Print sys.

Let sys := sys BN multN divN doubleN succN nat2bn Digest dig2string 
                        hashfun formBlock block_difficulty BN0 geN plusN 
                        canforge tfdepth nFixAccounts systemBalance goalBlockTime MaxRand.
Print signs.

Let signs := signs BN multN divN doubleN succN nat2bn Digest dig2string hashfun formBlock 
                     block_difficulty BN0 geN plusN canforge tfdepth nFixAccounts systemBalance goalBlockTime MaxRand.
 
Print sysigns.

Let sysigns := sysigns BN.

Print sysblocks.

Compute (signs 0).
Compute (signs 10).
Compute (signs 20).




