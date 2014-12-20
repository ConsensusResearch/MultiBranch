Require Export Coq.Lists.List.
Require Export Hex.
Require Export LTree2.
Require Export HashTable.

Import ListNotations.
Local Open Scope list_scope.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition is_nilb {X} (l: list X) := 
match l with
| [] => true
| _::_ => false
end.

Section Structures.

Variable BN : Type.
Variable modN : BN -> BN -> BN.
Variable multN : BN -> BN -> BN. 
Variable divN : BN -> BN -> BN.
Variable doubleN : BN -> BN.
Variable plusN : BN -> BN -> BN.

Definition Timestamp := BN.
Definition Currency := BN.
Definition HexSPK := hex.
Variable succN : BN -> BN.
Variable nat2bn : nat -> BN.

Record Account := account {
 balance_weight: BN;
 balance: Currency;
 isForging: bool;
 isPublishing: bool;
 isMarkable: bool;
 isMarkFollowing: bool;
 isMarkUnfollowing: bool;
 tfdepth:  option nat;
 publicKey: HexSPK
}.

Record Transaction := transaction {
sender : Account;
recipient: Account;
amount: Currency;
fee: Currency;
ttimestamp: Timestamp
}.

Definition BS := HexN.

Record Block := block {
transactions: list Transaction;
nMarked: nat;
baseTarget: BN;
totalDifficulty: BN;
generator: Account;
generationSignature: BS;
btimestamp: Timestamp
}.

Definition eqb_block (b1 b2: Block) :=
 eqb_hexs (generationSignature b1) (generationSignature b2).

Variable Digest : Type.
Variable dig2string : Digest -> BS.
Variable hashfun : HexN -> Digest.

Definition calcGenerationSignature (pb: Block) (acc: Account) : BS :=
  dig2string (hashfun ((generationSignature pb) ++ [publicKey acc])).

(*implemenation goes to Simulation*)
Variable formBlock : Block -> Account -> Timestamp -> list Transaction -> HexSPK -> Block.

Record Blockchain := blocktree { 
 blocks : LTree Block
}.

Check Blockchain.

Definition lastblocks (bc: Blockchain) : list Block := 
match bc with 
 | blocktree bs => [lastnode bs]
end.

Definition lastblock (bc: Blockchain) :  Block := 
match bc with 
 | blocktree bs => lastnode bs
end.

Variable block_difficulty: Block -> BN.
(*zero*)
Variable BN0 : BN.
(*unit*)
Variable BN1 : BN.
(*greater-equal*)
Variable geN : BN -> BN -> bool.


Definition pushBlock (pb: Block) (bc: Blockchain) (b: Block) :=
match bc with
| blocktree bs =>  let (parb, newbs) :=  ltree_grow2 pb b eqb_block bs in
                                         (parb, blocktree newbs)
end.

Definition markBlock (n:nat) (b: Block) :=
block (transactions b) (S n) (baseTarget b) (totalDifficulty b) (generator b) (generationSignature b) (btimestamp b).

(*
Definition adjustTotalDifficulty (pb b: Block) :=
block (transactions b) true (baseTarget b) (plusN (totalDifficulty pb) (block_difficulty b)) (generator b) (generationSignature b) (btimestamp b).
*)

Variable markTimestamp : Timestamp.


Definition isnatpos (n:nat) :=
match n with
| O => false
| S _ => true
end.

Definition generateBlock (bc: Blockchain) (pb: Block) (acc: Account) (ts: Timestamp) 
                         (txs: list Transaction) (pk: HexSPK) : Block * option Block * Blockchain :=
match bc with
| blocktree bs => let newblock' := formBlock pb acc ts txs pk in
                  let bMark := isnatpos (nMarked pb) in
                  let bTimeMore := geN ts markTimestamp in
                  let bBlockOld := negb (geN (btimestamp pb) markTimestamp) in        
                  let newblock := if orb bMark (andb (isMarkable acc) (andb bTimeMore bBlockOld)) then 
                                     markBlock (nMarked pb) newblock' else newblock' in                  
                  let (parb, newbc) := pushBlock pb bc newblock in
                  (newblock, parb, newbc)
end.

Record Node := node {
 nodechain: Blockchain;
 changedBlock: option Block;
 unconfirmedTxs: list Transaction;
 pending_blocks: list (Block*Block);
 open_blocks: list Block;
 (*pending_open_blocks: list Block;*)
 node_account: Account
}.

Variable canforge:  Node -> Timestamp -> Block -> bool.

Definition effectiveBalance := balance.

(*Fixpoint addSortedBlock (b: Block) (lb: list Block) :=
match lb with
| [] => [b]
| b'::bs => if negb (geN (baseTarget b) (baseTarget b')) then 
               b::lb
            else b'::(addSortedBlock b bs)
end.*)

(*
Fixpoint addSortedBlock (b: Block) (lb: list Block) :=
match lb with
| [] => [b]
| b'::bs => if (geN (btimestamp b) (btimestamp b')) then 
               b::lb
            else b'::(addSortedBlock b bs)
end.*)

Fixpoint addSortedBlock (b: Block) (lb: list Block) :=
match lb with
| [] => [b]
| b'::bs => if (geN (totalDifficulty b) (totalDifficulty b')) then 
               b::lb
            else b'::(addSortedBlock b bs)
end.


Definition earlierBlock (mb1 mb2: option Block) := 
match (mb1, mb2) with
| (Some b1, Some b2) => if (geN (btimestamp b1) (btimestamp b2)) then mb2 else mb1
| (Some b1, None) => Some b1
| (None, Some b2) => Some b2
| (None, None) => None
end. 


(*
 balance_weight: BN;
 balance: Currency;
 isForging: bool;
 isPublishing: bool;
 isMarkable: bool;
 isMarkFollowing: bool;
 tfdepth:  option nat;
 publicKey: HexSPK
*)

(* nodechain: Blockchain;
 changedBlock: option Block;
 unconfirmedTxs: list Transaction;
 pending_blocks: list (Block*Block);
 open_blocks: list Block;
 node_account: Account*)


Definition forge_block  (nd: Node) (ts: Timestamp) (pb: Block) : Node := 
let txs := unconfirmedTxs nd in 
let acct := node_account nd in
let bc := nodechain nd in
let pk := publicKey acct in
let effb := effectiveBalance acct in
let canf := canforge nd ts pb in
let pendb := pending_blocks nd in
let openb := open_blocks nd in
(*let popenb := pending_open_blocks nd in*)
let chb := changedBlock nd in 
match canf with
 | true => let (newbp, newbc) := generateBlock bc pb acct ts txs pk in
           let (newb, parb) := newbp in 
             node newbc (earlierBlock chb parb) [] ((pb,newb)::pendb) (addSortedBlock newb openb) acct
 | false =>  node bc    chb                     [] pendb              (addSortedBlock pb openb)  acct 
end.

Fixpoint splitn {X} (n: nat) (l: list X) :=
match n with
| O => ([], l)
| S n' => match l with
          | [] => ([], [])
          | x::xs => let (l1, l2) := splitn n' xs in
                               (x::l1, l2)
          end
end.

(*Variable tfdepth : option nat.*)

Check List.fold_left.

Fixpoint blt_nat (n m : nat) : bool :=
  match n with
  | O => 
    match m with
      | O => false
      | S _ => true
      end 
  | S n' =>
      match m with
      | O => false
      | S m' => blt_nat n' m'
      end
  end.

Variable lengthConfirmation : nat.

Definition markedBlocks (b: Block) :=
andb (blt_nat (nMarked b) lengthConfirmation) (blt_nat 0 (nMarked b)).

Definition unmarkedBlocks (b: Block) :=
negb (isnatpos (nMarked b)).

(*List.fold_left (fun l => fun b => addSortedBlock b l) (pending_open_blocks newn) splobt*)

Definition splitBlocks (tfdepth: option nat) (opb: list Block) (defl: list Block):=
match tfdepth with
      | None => (opb, nil)
      | Some tfd => match tfd with
                     | O => (defl, nil)
                     | S _ => splitn tfd opb
                    end
end.


(*
Record Account := account {
 balance_weight: BN;
 balance: Currency;
 isForging: bool;
 isPublishing: bool;
 isMarkable: bool;
 isMarkFollowing: bool;
 isMarkUnfollowing: bool;
 tfdepth:  option nat;
 publicKey: HexSPK
}.
*)

Definition forge_blocks (nd: Node) (ts: Timestamp) : Node :=
           let acc := (node_account nd) in
        
           let bc := nodechain nd in
           let opb := open_blocks nd in
           let (blocks', rb') := splitBlocks (tfdepth acc) opb (lastblocks bc) in
           let (blocks, rb) := if (isMarkFollowing acc) then
                               let (l,l') := List.partition markedBlocks blocks' in (l, l'++rb')
                               else if (isMarkUnfollowing acc) then 
                               let (l,l') := List.partition unmarkedBlocks blocks' in (l, l'++rb')
                               else (blocks', rb') in
           let bConfirmed := match opb with
                             | [] => false
                             | b::_ => blt_nat lengthConfirmation (nMarked b)
                             end in          
           let acc' :=  account (balance_weight acc) (balance acc) (isForging acc) (isPublishing acc) (isMarkable acc)
                        (andb (isMarkFollowing acc) (negb bConfirmed)) (orb (isMarkUnfollowing acc) (andb bConfirmed (isMarkFollowing acc)))
                        (tfdepth acc)  (publicKey acc) in                              
           let nd' := node (nodechain nd) (changedBlock nd) (unconfirmedTxs nd) (pending_blocks nd) rb acc' in
           let newn := List.fold_left (fun n => fun pb => forge_block n ts pb) blocks nd' in newn. 

(* 
 balance_weight: BN;
 balance: Currency;
 isForging: bool;
 isPublishing: bool;
 tfdepth:  option nat;
 publicKey: HexSPK
*)

Definition defaultAccount pk := 
account BN1 BN0 true true false false false (Some 0) pk.

Fixpoint xseries {X} (n:nat) (x:X) (succX : X -> X) := 
match n with
| O => []
| S n' => x :: (xseries n' (succX x) succX)
end.

Variable nFixAccounts : nat.
Variable accountParams: list (BN*bool*bool*bool*option nat).

Compute (fst (1,2,3)).

Fixpoint fixAccounts (h: HexSPK) (n: nat) (l: list (BN*bool*bool*bool*option nat)) : list Account :=
match n with
| O => []
| S n' => match l with
          | [] => (defaultAccount h) :: (fixAccounts (succH h) n' l)
          | ap :: l' => let (f1,tfd)  := ap in
                        let (f2, iMF) := f1 in
                        let (f3, iMA) := f2 in
                        let (w, iP) := f3 in
                        (account w BN0 true iP iMA iMF false tfd h) :: (fixAccounts (succH h) n' l')
          end
end.

Variable systemBalance: Currency.

Definition sysAccounts := 
 let accs0 := fixAccounts H1 nFixAccounts accountParams in
 let w := List.fold_left plusN (List.map balance_weight accs0) BN0 in
 List.map (fun acc => account (balance_weight acc) 
                                         (divN (multN (balance_weight acc) systemBalance) w) 
                                         (isForging acc) (isPublishing acc) (isMarkable acc) (isMarkFollowing acc) (isMarkUnfollowing acc) (tfdepth acc) (publicKey acc)) accs0.

Record Connection := connection {
 from_node: Node;
 to_node: Node
}.

Inductive System := system {
 nodes: list Node;
 connections: list Connection;
 accounts: list Account;
 timestamp: Timestamp
}.

Definition godAccount := account BN0 BN0 false false false false false None H0.


Variable goalBlockTime : BN.
Variable MaxRand : BN.

Definition initialBaseTarget : BN := divN MaxRand (doubleN (multN systemBalance goalBlockTime)).
Definition maxBaseTarget : BN := multN initialBaseTarget systemBalance.

Check List.fold_left.

(* 
 balance_weight: BN;
 balance: Currency;
 isForging: bool;
 isPublishing: bool;
 tfdepth:  option nat;
 publicKey: HexSPK
*)


Definition genesisBlock := block [] 0 initialBaseTarget initialBaseTarget godAccount [H0] BN0.
  
Definition genesisState :=
let accs := sysAccounts in
let chain := blocktree (tgen genesisBlock) in                                        
let nodes := List.map (fun acc => node chain None [] [] [genesisBlock] acc) accs in
    system nodes [] (godAccount::accs) BN0.


Definition sendBlock (sender receiver: Node) (bseq: Block*Block): Node :=
let (prevb, newb) := bseq in 
let rcvr_bc := nodechain receiver in
let gen := node_account sender in
let gs := calcGenerationSignature prevb gen in
let chb := changedBlock receiver in
if (eqb_hexs gs (generationSignature newb)) then 
    let (parb, newbc) := pushBlock prevb rcvr_bc newb in
    node newbc (earlierBlock chb parb) (unconfirmedTxs receiver) 
                (pending_blocks receiver) (addSortedBlock newb (open_blocks receiver)) (node_account receiver)
else receiver.

Definition eqbAccounts a1 a2:= eqb_hex (publicKey a1) (publicKey a2).

Definition sendBlocks (sender receiver: Node): Node :=
match andb (negb (eqbAccounts (node_account sender) (node_account receiver))) (isPublishing (node_account sender)) with
| false => receiver
| true => List.fold_left (fun n => fun pbb => sendBlock sender n pbb) (pending_blocks sender) receiver
end.

Print rebalanceS_till.

(*rebalanceS_till {X S: Type} (x:X) (w: X -> S) (eqX: X -> X -> bool) (s0: S) (geS: S-> S -> bool) (plusS: S -> S -> S) 
                                           (s: S) (t: LTree X) *)
Definition postforge (n: Node) := 
let bc := nodechain n in
let txs := unconfirmedTxs n in
let acc := node_account n in 
let chb := changedBlock n in
let newbc := match (tfdepth acc) with
             | None => bc
             | Some tfd => match tfd with 
                           | O =>  match bc with
                                    | blocktree bs => match chb with
                                                       | Some chb' => blocktree (rebalanceS_till chb' block_difficulty eqb_block BN0 geN plusN BN0 bs)
                                                       | None => bc
                                                      end
                                   end
                           | S _ => bc
                           end
            end in
node newbc None txs [] (open_blocks n) acc.  

Definition rebalance_chain (n: Node) := 
let bc := nodechain n in
let txs := unconfirmedTxs n in
let acc := node_account n in
let chb := changedBlock n in 
let newbc := match bc with
 | blocktree bs => blocktree (snd (rebalanceS block_difficulty eqb_block BN0 geN plusN BN0 bs (None, [])))
end in 
    node newbc None txs [] (open_blocks n) acc.  

Definition rebalance_sys (s: System) :=
system (List.map rebalance_chain (nodes s)) (connections s) (accounts s) (timestamp s).

Definition systemEvents (ts: Timestamp) (sys: System) : System := 
let nodes' := List.map (fun n => forge_blocks n ts) (nodes sys) in
let (nonForgers, forgers) := partition (fun n => is_nilb (pending_blocks n)) nodes' in 
let alteredNodes := 
List.map (fun n_to => List.fold_left (fun n_to' => fun n_from => sendBlocks n_from n_to') forgers n_to) nodes' in
  system (List.map postforge alteredNodes) (connections sys) (accounts sys) ts.

(*
nodes: list Node;
 connections: list Connection;
 accounts: list Account;
 timestamp: Timestamp*)

Fixpoint systemTransform (sys: System) (count: nat): System :=
let t:=timestamp sys in
match count with
| O => sys
| S c' =>  systemTransform (systemEvents (succN t) sys) c'
end.

Definition sys n := systemTransform genesisState n.
Definition sysblocks s := List.map blocks (List.map nodechain (nodes s)).

Inductive mhex :=
| N0: mhex
| N1: mhex
| N2: mhex
| N3: mhex
| N4: mhex
| N5: mhex
| N6: mhex
| N7: mhex
| N8: mhex
| N9: mhex
| NA: mhex
| NB: mhex
| NC: mhex
| ND: mhex
| NE: mhex
| NF: mhex
| M0: mhex
| M1: mhex
| M2: mhex
| M3: mhex
| M4: mhex
| M5: mhex
| M6: mhex
| M7: mhex
| M8: mhex
| M9: mhex
| MA: mhex
| MB: mhex
| MC: mhex
| MD: mhex
| ME: mhex
| MF: mhex.

Definition hex2mhex (m:bool) (h:hex) :=
match m with
| false => match h with 
           | Hex.H0 => N0
           | Hex.H1 => N1
           | Hex.H2 => N2
           | Hex.H3 => N3
           | Hex.H4 => N4
           | Hex.H5 => N5
           | Hex.H6 => N6
           | Hex.H7 => N7
           | Hex.H8 => N8
           | Hex.H9 => N9
           | Hex.HA => NA
           | Hex.HB => NB
           | Hex.HC => NC
           | Hex.HD => ND
           | Hex.HE => NE
           | Hex.HF => NF
           end
| true =>  match h with 
           | Hex.H0 => M0
           | Hex.H1 => M1
           | Hex.H2 => M2
           | Hex.H3 => M3
           | Hex.H4 => M4
           | Hex.H5 => M5
           | Hex.H6 => M6
           | Hex.H7 => M7
           | Hex.H8 => M8
           | Hex.H9 => M9
           | Hex.HA => MA
           | Hex.HB => MB
           | Hex.HC => MC
           | Hex.HD => MD
           | Hex.HE => ME
           | Hex.HF => MF
           end
end. 
         

Definition showblock (b: Block) := hex2mhex (isnatpos (nMarked b)) (publicKey (generator b)).

Definition signs n := List.map (fun tb => ltree_map (fun b => showblock b) tb) (List.map blocks (List.map nodechain (nodes (sys n)))).
Definition sysigns s := List.map (fun tb => ltree_map (fun b => showblock b) tb) (sysblocks s).
Definition sysaccs s := List.map (node_account) (nodes s).

Definition addsucc (ht: nattable nat) (k: nat) :=
match (search_table k ht) with
| None => (k, 1) :: ht
| Some v => modify_key k (v+1) ht
end.

Definition generators s := List.map (fun tb => ltree_foldl (fun ht => fun b => addsucc ht (hex2nat (publicKey (generator b)))) tb []) (sysblocks s).

End Structures.

Extraction Language Haskell.
Extraction "postructures" ltree2list ltreelen systemTransform sys sysigns signs 
       maxBaseTarget baseTarget List.filter btimestamp publicKey 
       effectiveBalance List.nth ltree_list_map fold1 sysblocks generators lastnode lastnodes rebalance_sys sysaccs. 

