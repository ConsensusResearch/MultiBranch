Require Export Coq.Lists.List.
Require Export Hex.
Require Export LTree2.
Require Export HashTable.

Import ListNotations.
Local Open Scope list_scope.

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

Definition Timestamp := BN.
Definition Currency := BN.
Definition HexSPK := hex.
Variable succN : BN -> BN.
Variable nat2bn : nat -> BN.

Record Account := account {
 balance: Currency;
 isForging: bool;
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
baseTarget: BN;
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
(*greater-equal*)
Variable geN : BN -> BN -> bool.
(*adding*)
Variable plusN : BN -> BN -> BN.

Definition pushBlock (pb: Block) (bc: Blockchain) (b: Block) :=
match bc with
| blocktree bs =>  let (parb, newbs) :=  ltree_grow2 pb b eqb_block bs in
                                         (parb, blocktree newbs)
end.

Definition generateBlock (bc: Blockchain) (pb: Block) (acc: Account) (ts: Timestamp) 
                         (txs: list Transaction) (pk: HexSPK) : Block * option Block * Blockchain :=
match bc with
| blocktree bs => let newblock := formBlock pb acc ts txs pk in 
                  let (parb, newbc) := pushBlock pb bc newblock in
                  (newblock, parb, newbc)
end.

Record Node := node {
 nodechain: Blockchain;
 changedBlock: option Block;
 unconfirmedTxs: list Transaction;
 pending_blocks: list (Block*Block);
 open_blocks: list Block;
 pending_open_blocks: list Block;
 node_account: Account
}.

Variable canforge:  Node -> Timestamp -> Block -> bool.

Definition effectiveBalance := balance.

Fixpoint addSortedBlock (b: Block) (lb: list Block) :=
match lb with
| [] => [b]
| b'::bs => if (geN (baseTarget b) (baseTarget b')) then 
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

Definition forge_block  (nd: Node) (ts: Timestamp) (pb: Block) : Node := 
let txs := unconfirmedTxs nd in 
let acct := node_account nd in
let bc := nodechain nd in
let pk := publicKey acct in
let effb := effectiveBalance acct in
let canf := canforge nd ts pb in
let pendb := pending_blocks nd in
let openb := open_blocks nd in
let popenb := pending_open_blocks nd in
let chb := changedBlock nd in 
match canf with
 | true => let (newbp, newbc) := generateBlock bc pb acct ts txs pk in
           let (newb, parb) := newbp in 
             node newbc (earlierBlock chb parb) [] ((pb,newb)::pendb) openb (addSortedBlock newb popenb) acct 
 | false => node bc chb [] pendb openb (addSortedBlock pb popenb) acct 
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

Variable tfdepth : option nat.

Check List.fold_left.

(*List.fold_left (fun l => fun b => addSortedBlock b l) (pending_open_blocks newn) splobt*)
Definition forge_blocks (nd: Node) (ts: Timestamp) : Node :=
           let bc := nodechain nd in
           let blocks := match tfdepth with
                          | None => open_blocks nd
                          | Some tfd => match tfd with
                                      | O => lastblocks bc
                                      | S _ => fst (splitn tfd (open_blocks nd))
                                      end
                         end in
           let newn := List.fold_left (fun n => fun pb => forge_block n ts pb) blocks nd in
           node (nodechain newn) (changedBlock newn) (unconfirmedTxs newn) (pending_blocks newn) 
                             (pending_open_blocks newn) [] (node_account newn). 


Definition accountByPK pk := account BN0 true pk.

Fixpoint xseries {X} (n:nat) (x:X) (succX : X -> X) := 
match n with
| O => []
| S n' => x :: (xseries n' (succX x) succX)
end.

Variable nFixAccounts : nat.

Definition fixAccounts := 
let pks := xseries nFixAccounts H1 succH in 
           List.map accountByPK pks.

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

Definition godAccount := account BN0 false H0.

Variable systemBalance: Currency.
Variable goalBlockTime : BN.
Variable MaxRand : BN.

Definition initialBaseTarget : BN := divN MaxRand (doubleN (multN systemBalance goalBlockTime)).
Definition maxBaseTarget : BN := multN initialBaseTarget systemBalance.

Definition genesisBlock := 
let invsc := nat2bn (length fixAccounts) in
let invs := List.map (fun acc => account (divN systemBalance invsc) (isForging acc) (publicKey acc)) fixAccounts in
let genesisTxs := [] in 
    block genesisTxs initialBaseTarget godAccount [H0] BN0.
  
Definition genesisState :=
let invsc := nat2bn (length fixAccounts) in
let invs := List.map (fun acc => account (divN systemBalance invsc) (isForging acc) (publicKey acc)) fixAccounts in
let chain := blocktree (tgen genesisBlock) in                                        
let nodes := List.map (fun acc => node chain None  [] [] [genesisBlock] [] acc) invs in
    system nodes [] (godAccount::fixAccounts) BN0.


Definition sendBlock (sender receiver: Node) (bseq: Block*Block): Node :=
let (prevb, newb) := bseq in 
let rcvr_bc := nodechain receiver in
let gen := node_account sender in
let gs := calcGenerationSignature prevb gen in
let chb := changedBlock receiver in
if (eqb_hexs gs (generationSignature newb)) then 
    let (parb, newbc) := pushBlock prevb rcvr_bc newb in
    node newbc (earlierBlock chb parb) (unconfirmedTxs receiver) 
                (pending_blocks receiver) (addSortedBlock newb (open_blocks receiver)) (pending_open_blocks receiver) (node_account receiver)
else receiver.

Definition sendBlocks (sender receiver: Node): Node :=
match eqb_hex (publicKey (node_account sender)) (publicKey (node_account receiver)) with
| true => receiver
| false => List.fold_left (fun n => fun pbb => sendBlock sender n pbb) (pending_blocks sender) receiver
end.

Print rebalanceS_till.

(*rebalanceS_till {X S: Type} (x:X) (w: X -> S) (eqX: X -> X -> bool) (s0: S) (geS: S-> S -> bool) (plusS: S -> S -> S) 
                                           (s: S) (t: LTree X) *)
Definition postforge (n: Node) := 
let bc := nodechain n in
let txs := unconfirmedTxs n in
let acc := node_account n in 
let chb := changedBlock n in
let newbc := match tfdepth with
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
node newbc None txs [] (open_blocks n) [] acc.  

Definition rebalance_chain (n: Node) := 
let bc := nodechain n in
let txs := unconfirmedTxs n in
let acc := node_account n in
let chb := changedBlock n in 
let newbc := match bc with
 | blocktree bs => blocktree (snd (rebalanceS block_difficulty eqb_block BN0 geN plusN BN0 bs (None, [])))
end in 
    node newbc None txs [] (open_blocks n) [] acc.  

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
Definition signs n := List.map (fun tb => ltree_map (fun b => publicKey (generator b)) tb) (List.map blocks (List.map nodechain (nodes (sys n)))).
Definition sysigns s := List.map (fun tb => ltree_map (fun b => publicKey (generator b)) tb) (sysblocks s).

Definition addsucc (ht: nattable nat) (k: nat) :=
match (search_table k ht) with
| None => (k, 1) :: ht
| Some v => modify_key k (v+1) ht
end.

Definition generators s := List.map (fun tb => ltree_foldl (fun ht => fun b => addsucc ht (hex2nat (publicKey (generator b)))) tb []) (sysblocks s).

End Structures.

Extraction Language Haskell.
Extraction "postructures" ltreelen systemTransform sys sysigns signs 
       maxBaseTarget baseTarget List.filter btimestamp publicKey 
       effectiveBalance List.nth ltree_list_map fold1 sysblocks generators lastnode lastnodes rebalance_sys. 

