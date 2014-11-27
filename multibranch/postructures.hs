module Postructures where

import qualified Prelude

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x y -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair x y -> y}

data List a =
   Nil
 | Cons a (List a)

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons y l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

tl :: (List a1) -> List a1
tl l =
  case l of {
   Nil -> Nil;
   Cons a m -> m}

nth :: Nat -> (List a1) -> a1 -> a1
nth n l default0 =
  case n of {
   O ->
    case l of {
     Nil -> default0;
     Cons x l' -> x};
   S m ->
    case l of {
     Nil -> default0;
     Cons x t -> nth m t default0}}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (List a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   Nil -> a0;
   Cons b t -> fold_left f t (f a0 b)}

filter :: (a1 -> Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     True -> Cons x (filter f l0);
     False -> filter f l0}}

partition :: (a1 -> Bool) -> (List a1) -> Prod (List a1) (List a1)
partition f l =
  case l of {
   Nil -> Pair Nil Nil;
   Cons x tl0 ->
    case partition f tl0 of {
     Pair g d ->
      case f x of {
       True -> Pair (Cons x g) d;
       False -> Pair g (Cons x d)}}}

combine :: (List a1) -> (List a2) -> List (Prod a1 a2)
combine l l' =
  case l of {
   Nil -> Nil;
   Cons x tl0 ->
    case l' of {
     Nil -> Nil;
     Cons y tl' -> Cons (Pair x y) (combine tl0 tl')}}

beq_nat :: Nat -> Nat -> Bool
beq_nat n m =
  case n of {
   O ->
    case m of {
     O -> True;
     S n0 -> False};
   S n1 ->
    case m of {
     O -> False;
     S m1 -> beq_nat n1 m1}}

data Hex =
   H0
 | H1
 | H2
 | H3
 | H4
 | H5
 | H6
 | H7
 | H8
 | H9
 | HA
 | HB
 | HC
 | HD
 | HE
 | HF

hex2nat :: Hex -> Nat
hex2nat h =
  case h of {
   H0 -> O;
   H1 -> S O;
   H2 -> S (S O);
   H3 -> S (S (S O));
   H4 -> S (S (S (S O)));
   H5 -> S (S (S (S (S O))));
   H6 -> S (S (S (S (S (S O)))));
   H7 -> S (S (S (S (S (S (S O))))));
   H8 -> S (S (S (S (S (S (S (S O)))))));
   H9 -> S (S (S (S (S (S (S (S (S O))))))));
   HA -> S (S (S (S (S (S (S (S (S (S O)))))))));
   HB -> S (S (S (S (S (S (S (S (S (S (S O))))))))));
   HC -> S (S (S (S (S (S (S (S (S (S (S (S O)))))))))));
   HD -> S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))));
   HE -> S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))));
   HF -> S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))}

succH :: Hex -> Hex
succH h =
  case h of {
   H0 -> H1;
   H1 -> H2;
   H2 -> H3;
   H3 -> H4;
   H4 -> H5;
   H5 -> H6;
   H6 -> H7;
   H7 -> H8;
   H8 -> H9;
   H9 -> HA;
   HA -> HB;
   HB -> HC;
   HC -> HD;
   HD -> HE;
   HE -> HF;
   HF -> H0}

type HexN = List Hex

eqb_hex :: Hex -> Hex -> Bool
eqb_hex h1 h2 =
  beq_nat (hex2nat h1) (hex2nat h2)

eqb_hexs :: HexN -> HexN -> Bool
eqb_hexs bs1 bs2 =
  case bs1 of {
   Nil ->
    case bs2 of {
     Nil -> True;
     Cons h l -> False};
   Cons x xs ->
    case bs2 of {
     Nil -> False;
     Cons y ys ->
      case eqb_hex x y of {
       True -> eqb_hexs xs ys;
       False -> False}}}

data LTree x =
   Tgen x
 | Tcons x (LTree x)
 | Tfork (LBranch x) (LTree x)
data LBranch x =
   Tbranch (LTree x)

lastnode :: (LTree a1) -> a1
lastnode t =
  case t of {
   Tgen a -> a;
   Tcons a l -> a;
   Tfork l t1 -> lastnode t1}

lastforknodes :: (LTree a1) -> List a1
lastforknodes t =
  case t of {
   Tgen x -> Nil;
   Tcons x l -> lastforknodes l;
   Tfork l t1 ->
    case l of {
     Tbranch t2 -> app (lastforknodes t1) (lastnodes t2)}}

lastnodes :: (LTree a1) -> List a1
lastnodes t =
  case t of {
   Tgen x -> Cons x Nil;
   Tcons x l -> Cons x (lastforknodes l);
   Tfork l t1 ->
    case l of {
     Tbranch t2 -> app (lastnodes t1) (lastnodes t2)}}

ltree_map :: (a1 -> a2) -> (LTree a1) -> LTree a2
ltree_map f t =
  case t of {
   Tgen a -> Tgen (f a);
   Tcons a l -> Tcons (f a) (ltree_map f l);
   Tfork l l' ->
    case l of {
     Tbranch l'' -> Tfork (Tbranch (ltree_map f l'')) (ltree_map f l')}}

ltree_list_map :: (a1 -> a2) -> (LTree a1) -> List a2
ltree_list_map f t =
  case t of {
   Tgen a -> Cons (f a) Nil;
   Tcons a l -> app (ltree_list_map f l) (Cons (f a) Nil);
   Tfork l t1 -> ltree_list_map f t1}

ltree_foldl :: (a2 -> a1 -> a2) -> (LTree a1) -> a2 -> a2
ltree_foldl f t y0 =
  case t of {
   Tgen a -> f y0 a;
   Tcons a l -> ltree_foldl f l (f y0 a);
   Tfork l t1 -> ltree_foldl f t1 y0}

fold1 :: (a1 -> a1 -> a1) -> (List a1) -> List a1
fold1 f l =
  let {tl0 = tl l} in
  let {cmbl = combine tl0 l} in
  map (\z ->
    case z of {
     Pair x y -> f x y}) cmbl

ltreelen :: (LTree a1) -> Nat
ltreelen t =
  case t of {
   Tgen x -> S O;
   Tcons x t' -> S (ltreelen t');
   Tfork l t' -> ltreelen t'}

forks :: (List (LTree a1)) -> (LTree a1) -> LTree a1
forks ff t =
  case ff of {
   Nil -> t;
   Cons fx fs -> Tfork (Tbranch fx) (forks fs t)}

ltree_grow20 :: a1 -> a1 -> (a1 -> a1 -> Bool) -> (LTree a1) -> Bool -> (List
                (LTree a1)) -> Prod (Option a1) (LTree a1)
ltree_grow20 x y eqX t bfork lbr =
  case t of {
   Tgen a ->
    case eqX x a of {
     True ->
      case bfork of {
       True -> Pair (Some a) (forks (Cons (Tgen y) lbr) t);
       False -> Pair (Some a) (Tcons y (forks lbr t))};
     False -> Pair None (forks lbr t)};
   Tcons a l ->
    case eqX x a of {
     True ->
      let {r = Some a} in
      case bfork of {
       True -> Pair r (forks (Cons (Tgen y) lbr) (Tcons a l));
       False -> Pair r (Tcons y (forks lbr (Tcons a l)))};
     False ->
      case ltree_grow20 x y eqX l True Nil of {
       Pair mx l' -> Pair mx (forks lbr (Tcons a l'))}};
   Tfork l t' ->
    case l of {
     Tbranch t'' ->
      case ltree_grow20 x y eqX t'' False Nil of {
       Pair mx'' l'' ->
        case mx'' of {
         Some x'' -> Pair (Some (lastnode t')) (forks (Cons l'' lbr) t');
         None -> ltree_grow20 x y eqX t' bfork (Cons l'' lbr)}}}}

ltree_grow2 :: a1 -> a1 -> (a1 -> a1 -> Bool) -> (LTree a1) -> Prod
               (Option a1) (LTree a1)
ltree_grow2 x y eqX t =
  ltree_grow20 x y eqX t False Nil

merge_trees :: (LTree a1) -> (LTree a1) -> LTree a1
merge_trees t1 t2 =
  case t2 of {
   Tgen a2 -> Tcons a2 t1;
   Tcons a2 l2 -> Tcons a2 (merge_trees t1 l2);
   Tfork l l2' -> Tfork l (merge_trees t1 l2')}

merge_node_forks2 :: a1 -> a1 -> (a1 -> a1 -> Bool) -> (LTree a1) -> (Prod
                     (Option (LTree a1)) (List (LTree a1))) -> Bool -> (List
                     (LTree a1)) -> Prod Bool (LTree a1)
merge_node_forks2 x y eqX t lbt bfork lbr =
  case t of {
   Tgen a ->
    case lbt of {
     Pair o lb ->
      case o of {
       Some lt ->
        case eqX x a of {
         True ->
          case bfork of {
           True -> Pair True
            (forks (Cons (merge_trees (forks lb (Tgen y)) lt) lbr) t);
           False -> Pair True
            (merge_trees (forks lb (Tcons y (forks lbr t))) lt)};
         False -> Pair False (forks lbr t)};
       None ->
        case eqX x a of {
         True ->
          case bfork of {
           True -> Pair True (forks (Cons (forks lb (Tgen y)) lbr) t);
           False -> Pair True (forks lb (Tcons y (forks lbr t)))};
         False -> Pair False (forks lbr t)}}};
   Tcons a l ->
    case merge_node_forks2 x y eqX l lbt True Nil of {
     Pair b l' ->
      case lbt of {
       Pair o lb ->
        case o of {
         Some lt ->
          case eqX x a of {
           True ->
            case bfork of {
             True -> Pair True
              (forks (Cons (merge_trees (forks lb (Tgen y)) lt) lbr) (Tcons a
                l));
             False -> Pair True
              (merge_trees (forks lb (Tcons y (forks lbr (Tcons a l)))) lt)};
           False -> Pair b (forks lbr (Tcons a l'))};
         None ->
          case eqX x a of {
           True ->
            case bfork of {
             True -> Pair True
              (forks (Cons (forks lb (Tgen y)) lbr) (Tcons a l));
             False -> Pair True (forks lb (Tcons y (forks lbr (Tcons a l))))};
           False -> Pair b (forks lbr (Tcons a l'))}}}};
   Tfork l t' ->
    case l of {
     Tbranch t'' ->
      case merge_node_forks2 x y eqX t'' lbt False Nil of {
       Pair b l'' ->
        case b of {
         True -> Pair True (forks (Cons l'' lbr) t');
         False -> merge_node_forks2 x y eqX t' lbt bfork (Cons l'' lbr)}}}}

rebalanceS :: (a1 -> a2) -> (a1 -> a1 -> Bool) -> a2 -> (a2 -> a2 -> Bool) ->
              (a2 -> a2 -> a2) -> a2 -> (LTree a1) -> (Prod
              (Option (LTree a1)) (List (LTree a1))) -> Prod (Prod a2 a1)
              (LTree a1)
rebalanceS w eqX s0 geS plusS s t lbr =
  case t of {
   Tgen a ->
    case lbr of {
     Pair o lb ->
      case o of {
       Some lt -> Pair (Pair (plusS s (w a)) a) (merge_trees (forks lb t) lt);
       None -> Pair (Pair (plusS s (w a)) a) (forks lb t)}};
   Tcons a t' ->
    case rebalanceS w eqX s0 geS plusS (plusS s (w a)) t' (Pair None Nil) of {
     Pair mx t'b ->
      case mx of {
       Pair m x -> Pair (Pair m a)
        (snd (merge_node_forks2 x a eqX t'b lbr False Nil))}};
   Tfork l t' ->
    case l of {
     Tbranch t'' ->
      case rebalanceS w eqX s0 geS plusS s0 t'' (Pair None Nil) of {
       Pair px'' t''b ->
        case px'' of {
         Pair p'' x'' ->
          case geS s p'' of {
           True ->
            case lbr of {
             Pair o lb ->
              rebalanceS w eqX s0 geS plusS s t' (Pair o (Cons t''b lb))};
           False ->
            case lbr of {
             Pair o lb ->
              case o of {
               Some lt ->
                rebalanceS w eqX s0 geS plusS p'' t' (Pair (Some t''b) (Cons
                  lt lb));
               None ->
                rebalanceS w eqX s0 geS plusS p'' t' (Pair (Some t''b) lb)}}}}}}}

ltree_split_till :: a1 -> (a1 -> a1 -> Bool) -> (LTree a1) -> Prod
                    (Option (LTree a1)) (Option (LTree a1))
ltree_split_till x eqX t =
  case t of {
   Tgen a ->
    case eqX a x of {
     True -> Pair None (Some (Tgen a));
     False -> Pair (Some (Tgen a)) None};
   Tcons a l ->
    case eqX a x of {
     True -> Pair (Some l) (Some (Tgen a));
     False ->
      case ltree_split_till x eqX l of {
       Pair o o0 ->
        case o of {
         Some l1 ->
          case o0 of {
           Some l2 -> Pair (Some l1) (Some (Tcons a l2));
           None -> Pair (Some (Tcons a l1)) None};
         None ->
          case o0 of {
           Some l2 -> Pair None (Some (Tcons a l2));
           None -> Pair None None}}}};
   Tfork l t1 ->
    case ltree_split_till x eqX t1 of {
     Pair o o0 ->
      case o of {
       Some l1 ->
        case o0 of {
         Some l2 -> Pair (Some l1) (Some (Tfork l l2));
         None -> Pair (Some (Tfork l l1)) None};
       None ->
        case o0 of {
         Some l2 -> Pair None (Some (Tfork l l2));
         None -> Pair None None}}}}

rebalanceS_till :: a1 -> (a1 -> a2) -> (a1 -> a1 -> Bool) -> a2 -> (a2 -> a2
                   -> Bool) -> (a2 -> a2 -> a2) -> a2 -> (LTree a1) -> LTree
                   a1
rebalanceS_till x w eqX s0 geS plusS s t =
  case ltree_split_till x eqX t of {
   Pair t1 t2 ->
    case t1 of {
     Some t3 ->
      case t2 of {
       Some t4 ->
        merge_trees t3
          (snd (rebalanceS w eqX s0 geS plusS s t4 (Pair None Nil)));
       None -> t3};
     None ->
      case t2 of {
       Some t3 -> snd (rebalanceS w eqX s0 geS plusS s t3 (Pair None Nil));
       None -> t}}}

beq_nat0 :: Nat -> Nat -> Bool
beq_nat0 n m =
  case n of {
   O ->
    case m of {
     O -> True;
     S m' -> False};
   S n' ->
    case m of {
     O -> False;
     S m' -> beq_nat0 n' m'}}

type Nattable v = List (Prod Nat v)

search_table :: Nat -> (Nattable a1) -> Option a1
search_table k t =
  case t of {
   Nil -> None;
   Cons p t' ->
    case p of {
     Pair k' v ->
      case beq_nat0 k k' of {
       True -> Some v;
       False -> search_table k t'}}}

search_place_table0 :: Nat -> (Nattable a1) -> (Nattable a1) -> Option
                       (Prod a1 (Nattable a1))
search_place_table0 k t t' =
  case t of {
   Nil -> None;
   Cons p t'' ->
    case p of {
     Pair k' v ->
      case beq_nat0 k k' of {
       True -> Some (Pair v (app t' t''));
       False -> search_place_table0 k t'' (app t' (Cons (Pair k' v) Nil))}}}

search_place_table :: Nat -> (Nattable a1) -> Option (Prod a1 (Nattable a1))
search_place_table k t =
  search_place_table0 k t Nil

modify_key :: Nat -> a1 -> (Nattable a1) -> Nattable a1
modify_key k v t =
  case search_place_table k t of {
   Some p ->
    case p of {
     Pair v0 tb -> Cons (Pair k v) tb};
   None -> t}

is_nilb :: (List a1) -> Bool
is_nilb l =
  case l of {
   Nil -> True;
   Cons x l0 -> False}

type Timestamp bN = bN

type Currency bN = bN

type HexSPK = Hex

data Account0 bN =
   Account (Currency bN) Bool HexSPK

balance :: (Account0 a1) -> Currency a1
balance a =
  case a of {
   Account balance0 isForging0 publicKey0 -> balance0}

isForging :: (Account0 a1) -> Bool
isForging a =
  case a of {
   Account balance0 isForging0 publicKey0 -> isForging0}

publicKey :: (Account0 a1) -> HexSPK
publicKey a =
  case a of {
   Account balance0 isForging0 publicKey0 -> publicKey0}

data Transaction0 bN =
   Transaction (Account0 bN) (Account0 bN) (Currency bN) (Currency bN) 
 (Timestamp bN)

type BS = HexN

data Block0 bN =
   Block (List (Transaction0 bN)) bN (Account0 bN) BS (Timestamp bN)

baseTarget :: (Block0 a1) -> a1
baseTarget b =
  case b of {
   Block transactions baseTarget0 generator0 generationSignature0
    btimestamp0 -> baseTarget0}

generator :: (Block0 a1) -> Account0 a1
generator b =
  case b of {
   Block transactions baseTarget0 generator0 generationSignature0
    btimestamp0 -> generator0}

generationSignature :: (Block0 a1) -> BS
generationSignature b =
  case b of {
   Block transactions baseTarget0 generator0 generationSignature0
    btimestamp0 -> generationSignature0}

btimestamp :: (Block0 a1) -> Timestamp a1
btimestamp b =
  case b of {
   Block transactions baseTarget0 generator0 generationSignature0
    btimestamp0 -> btimestamp0}

eqb_block :: (Block0 a1) -> (Block0 a1) -> Bool
eqb_block b1 b2 =
  eqb_hexs (generationSignature b1) (generationSignature b2)

calcGenerationSignature :: (a2 -> BS) -> (HexN -> a2) -> (Block0 a1) ->
                           (Account0 a1) -> BS
calcGenerationSignature dig2string hashfun pb acc =
  dig2string
    (hashfun (app (generationSignature pb) (Cons (publicKey acc) Nil)))

type Blockchain bN =
  LTree (Block0 bN)
  -- singleton inductive, whose constructor was blocktree
  
blocks :: (Blockchain a1) -> LTree (Block0 a1)
blocks b =
  b

lastblocks :: (Blockchain a1) -> List (Block0 a1)
lastblocks bc =
  Cons (lastnode bc) Nil

pushBlock :: (Block0 a1) -> (Blockchain a1) -> (Block0 a1) -> Prod
             (Option (Block0 a1)) (Blockchain a1)
pushBlock pb bc b =
  case ltree_grow2 pb b eqb_block bc of {
   Pair parb newbs -> Pair parb newbs}

generateBlock :: ((Block0 a1) -> (Account0 a1) -> (Timestamp a1) -> (List
                 (Transaction0 a1)) -> HexSPK -> Block0 a1) -> (Blockchain
                 a1) -> (Block0 a1) -> (Account0 a1) -> (Timestamp a1) ->
                 (List (Transaction0 a1)) -> HexSPK -> Prod
                 (Prod (Block0 a1) (Option (Block0 a1))) (Blockchain a1)
generateBlock formBlock bc pb acc ts txs pk =
  let {newblock = formBlock pb acc ts txs pk} in
  case pushBlock pb bc newblock of {
   Pair parb newbc -> Pair (Pair newblock parb) newbc}

data Node0 bN =
   Node (Blockchain bN) (Option (Block0 bN)) (List (Transaction0 bN)) 
 (List (Prod (Block0 bN) (Block0 bN))) (List (Block0 bN)) (List (Block0 bN)) 
 (Account0 bN)

nodechain :: (Node0 a1) -> Blockchain a1
nodechain n =
  case n of {
   Node nodechain0 changedBlock0 unconfirmedTxs0 pending_blocks0 open_blocks0
    pending_open_blocks0 node_account0 -> nodechain0}

changedBlock :: (Node0 a1) -> Option (Block0 a1)
changedBlock n =
  case n of {
   Node nodechain0 changedBlock0 unconfirmedTxs0 pending_blocks0 open_blocks0
    pending_open_blocks0 node_account0 -> changedBlock0}

unconfirmedTxs :: (Node0 a1) -> List (Transaction0 a1)
unconfirmedTxs n =
  case n of {
   Node nodechain0 changedBlock0 unconfirmedTxs0 pending_blocks0 open_blocks0
    pending_open_blocks0 node_account0 -> unconfirmedTxs0}

pending_blocks :: (Node0 a1) -> List (Prod (Block0 a1) (Block0 a1))
pending_blocks n =
  case n of {
   Node nodechain0 changedBlock0 unconfirmedTxs0 pending_blocks0 open_blocks0
    pending_open_blocks0 node_account0 -> pending_blocks0}

open_blocks :: (Node0 a1) -> List (Block0 a1)
open_blocks n =
  case n of {
   Node nodechain0 changedBlock0 unconfirmedTxs0 pending_blocks0 open_blocks0
    pending_open_blocks0 node_account0 -> open_blocks0}

pending_open_blocks :: (Node0 a1) -> List (Block0 a1)
pending_open_blocks n =
  case n of {
   Node nodechain0 changedBlock0 unconfirmedTxs0 pending_blocks0 open_blocks0
    pending_open_blocks0 node_account0 -> pending_open_blocks0}

node_account :: (Node0 a1) -> Account0 a1
node_account n =
  case n of {
   Node nodechain0 changedBlock0 unconfirmedTxs0 pending_blocks0 open_blocks0
    pending_open_blocks0 node_account0 -> node_account0}

effectiveBalance :: (Account0 a1) -> Currency a1
effectiveBalance =
  balance

addSortedBlock :: (a1 -> a1 -> Bool) -> (Block0 a1) -> (List (Block0 a1)) ->
                  List (Block0 a1)
addSortedBlock geN b lb =
  case lb of {
   Nil -> Cons b Nil;
   Cons b' bs ->
    case geN (baseTarget b) (baseTarget b') of {
     True -> Cons b lb;
     False -> Cons b' (addSortedBlock geN b bs)}}

earlierBlock :: (a1 -> a1 -> Bool) -> (Option (Block0 a1)) -> (Option
                (Block0 a1)) -> Option (Block0 a1)
earlierBlock geN mb1 mb2 =
  case mb1 of {
   Some b1 ->
    case mb2 of {
     Some b2 ->
      case geN (btimestamp b1) (btimestamp b2) of {
       True -> mb2;
       False -> mb1};
     None -> Some b1};
   None -> mb2}

forge_block :: ((Block0 a1) -> (Account0 a1) -> (Timestamp a1) -> (List
               (Transaction0 a1)) -> HexSPK -> Block0 a1) -> (a1 -> a1 ->
               Bool) -> ((Node0 a1) -> (Timestamp a1) -> (Block0 a1) -> Bool)
               -> (Node0 a1) -> (Timestamp a1) -> (Block0 a1) -> Node0 
               a1
forge_block formBlock geN canforge nd ts pb =
  let {txs = unconfirmedTxs nd} in
  let {acct = node_account nd} in
  let {bc = nodechain nd} in
  let {pk = publicKey acct} in
  let {canf = canforge nd ts pb} in
  let {pendb = pending_blocks nd} in
  let {openb = open_blocks nd} in
  let {popenb = pending_open_blocks nd} in
  let {chb = changedBlock nd} in
  case canf of {
   True ->
    case generateBlock formBlock bc pb acct ts txs pk of {
     Pair newbp newbc ->
      case newbp of {
       Pair newb parb -> Node newbc (earlierBlock geN chb parb) Nil (Cons
        (Pair pb newb) pendb) openb (addSortedBlock geN newb popenb) acct}};
   False -> Node bc chb Nil pendb openb (addSortedBlock geN pb popenb) acct}

splitn :: Nat -> (List a1) -> Prod (List a1) (List a1)
splitn n l =
  case n of {
   O -> Pair Nil l;
   S n' ->
    case l of {
     Nil -> Pair Nil Nil;
     Cons x xs ->
      case splitn n' xs of {
       Pair l1 l2 -> Pair (Cons x l1) l2}}}

forge_blocks :: ((Block0 a1) -> (Account0 a1) -> (Timestamp a1) -> (List
                (Transaction0 a1)) -> HexSPK -> Block0 a1) -> (a1 -> a1 ->
                Bool) -> ((Node0 a1) -> (Timestamp a1) -> (Block0 a1) ->
                Bool) -> (Option Nat) -> (Node0 a1) -> (Timestamp a1) ->
                Node0 a1
forge_blocks formBlock geN canforge tfdepth nd ts =
  let {bc = nodechain nd} in
  let {
   blocks0 = case tfdepth of {
              Some tfd ->
               case tfd of {
                O -> lastblocks bc;
                S n -> fst (splitn tfd (open_blocks nd))};
              None -> open_blocks nd}}
  in
  let {
   newn = fold_left (\n pb -> forge_block formBlock geN canforge n ts pb)
            blocks0 nd}
  in
  Node (nodechain newn) (changedBlock newn) (unconfirmedTxs newn)
  (pending_blocks newn) (pending_open_blocks newn) Nil (node_account newn)

accountByPK :: a1 -> HexSPK -> Account0 a1
accountByPK bN0 pk =
  Account bN0 True pk

xseries :: Nat -> a1 -> (a1 -> a1) -> List a1
xseries n x succX =
  case n of {
   O -> Nil;
   S n' -> Cons x (xseries n' (succX x) succX)}

fixAccounts :: a1 -> Nat -> List (Account0 a1)
fixAccounts bN0 nFixAccounts =
  let {pks = xseries nFixAccounts H1 succH} in map (accountByPK bN0) pks

data Connection0 bN =
   Connection (Node0 bN) (Node0 bN)

data System0 bN =
   System (List (Node0 bN)) (List (Connection0 bN)) (List (Account0 bN)) 
 (Timestamp bN)

nodes :: (System0 a1) -> List (Node0 a1)
nodes s =
  case s of {
   System nodes0 connections0 accounts0 timestamp0 -> nodes0}

connections :: (System0 a1) -> List (Connection0 a1)
connections s =
  case s of {
   System nodes0 connections0 accounts0 timestamp0 -> connections0}

accounts :: (System0 a1) -> List (Account0 a1)
accounts s =
  case s of {
   System nodes0 connections0 accounts0 timestamp0 -> accounts0}

timestamp :: (System0 a1) -> Timestamp a1
timestamp s =
  case s of {
   System nodes0 connections0 accounts0 timestamp0 -> timestamp0}

godAccount :: a1 -> Account0 a1
godAccount bN0 =
  Account bN0 False H0

initialBaseTarget :: (a1 -> a1 -> a1) -> (a1 -> a1 -> a1) -> (a1 -> a1) ->
                     (Currency a1) -> a1 -> a1 -> a1
initialBaseTarget multN divN doubleN systemBalance goalBlockTime maxRand =
  divN maxRand (doubleN (multN systemBalance goalBlockTime))

maxBaseTarget :: (a1 -> a1 -> a1) -> (a1 -> a1 -> a1) -> (a1 -> a1) ->
                 (Currency a1) -> a1 -> a1 -> a1
maxBaseTarget multN divN doubleN systemBalance goalBlockTime maxRand =
  multN
    (initialBaseTarget multN divN doubleN systemBalance goalBlockTime
      maxRand) systemBalance

genesisBlock :: (a1 -> a1 -> a1) -> (a1 -> a1 -> a1) -> (a1 -> a1) -> (Nat ->
                a1) -> a1 -> Nat -> (Currency a1) -> a1 -> a1 -> Block0 
                a1
genesisBlock multN divN doubleN nat2bn bN0 nFixAccounts systemBalance goalBlockTime maxRand =
  let {genesisTxs = Nil} in
  Block genesisTxs
  (initialBaseTarget multN divN doubleN systemBalance goalBlockTime maxRand)
  (godAccount bN0) (Cons H0 Nil) bN0

genesisState :: (a1 -> a1 -> a1) -> (a1 -> a1 -> a1) -> (a1 -> a1) -> (Nat ->
                a1) -> a1 -> Nat -> (Currency a1) -> a1 -> a1 -> System0 
                a1
genesisState multN divN doubleN nat2bn bN0 nFixAccounts systemBalance goalBlockTime maxRand =
  let {invsc = nat2bn (length (fixAccounts bN0 nFixAccounts))} in
  let {
   invs = map (\acc -> Account (divN systemBalance invsc) (isForging acc)
            (publicKey acc)) (fixAccounts bN0 nFixAccounts)}
  in
  let {
   chain = Tgen
    (genesisBlock multN divN doubleN nat2bn bN0 nFixAccounts systemBalance
      goalBlockTime maxRand)}
  in
  let {
   nodes0 = map (\acc -> Node chain None Nil Nil (Cons
              (genesisBlock multN divN doubleN nat2bn bN0 nFixAccounts
                systemBalance goalBlockTime maxRand) Nil) Nil acc) invs}
  in
  System nodes0 Nil (Cons (godAccount bN0) (fixAccounts bN0 nFixAccounts))
  bN0

sendBlock :: (a2 -> BS) -> (HexN -> a2) -> (a1 -> a1 -> Bool) -> (Node0 
             a1) -> (Node0 a1) -> (Prod (Block0 a1) (Block0 a1)) -> Node0 
             a1
sendBlock dig2string hashfun geN sender receiver bseq =
  case bseq of {
   Pair prevb newb ->
    let {rcvr_bc = nodechain receiver} in
    let {gen = node_account sender} in
    let {gs = calcGenerationSignature dig2string hashfun prevb gen} in
    let {chb = changedBlock receiver} in
    case eqb_hexs gs (generationSignature newb) of {
     True ->
      case pushBlock prevb rcvr_bc newb of {
       Pair parb newbc -> Node newbc (earlierBlock geN chb parb)
        (unconfirmedTxs receiver) (pending_blocks receiver)
        (addSortedBlock geN newb (open_blocks receiver))
        (pending_open_blocks receiver) (node_account receiver)};
     False -> receiver}}

sendBlocks :: (a2 -> BS) -> (HexN -> a2) -> (a1 -> a1 -> Bool) -> (Node0 
              a1) -> (Node0 a1) -> Node0 a1
sendBlocks dig2string hashfun geN sender receiver =
  case eqb_hex (publicKey (node_account sender))
         (publicKey (node_account receiver)) of {
   True -> receiver;
   False ->
    fold_left (\n pbb -> sendBlock dig2string hashfun geN sender n pbb)
      (pending_blocks sender) receiver}

postforge :: ((Block0 a1) -> a1) -> a1 -> (a1 -> a1 -> Bool) -> (a1 -> a1 ->
             a1) -> (Option Nat) -> (Node0 a1) -> Node0 a1
postforge block_difficulty bN0 geN plusN tfdepth n =
  let {bc = nodechain n} in
  let {txs = unconfirmedTxs n} in
  let {acc = node_account n} in
  let {chb = changedBlock n} in
  let {
   newbc = case tfdepth of {
            Some tfd ->
             case tfd of {
              O ->
               case chb of {
                Some chb' ->
                 rebalanceS_till chb' block_difficulty eqb_block bN0 geN
                   plusN bN0 bc;
                None -> bc};
              S n0 -> bc};
            None -> bc}}
  in
  Node newbc None txs Nil (open_blocks n) Nil acc

rebalance_chain :: ((Block0 a1) -> a1) -> a1 -> (a1 -> a1 -> Bool) -> (a1 ->
                   a1 -> a1) -> (Node0 a1) -> Node0 a1
rebalance_chain block_difficulty bN0 geN plusN n =
  let {bc = nodechain n} in
  let {txs = unconfirmedTxs n} in
  let {acc = node_account n} in
  let {
   newbc = snd
             (rebalanceS block_difficulty eqb_block bN0 geN plusN bN0 bc
               (Pair None Nil))}
  in
  Node newbc None txs Nil (open_blocks n) Nil acc

rebalance_sys :: ((Block0 a1) -> a1) -> a1 -> (a1 -> a1 -> Bool) -> (a1 -> a1
                 -> a1) -> (System0 a1) -> System0 a1
rebalance_sys block_difficulty bN0 geN plusN s =
  System (map (rebalance_chain block_difficulty bN0 geN plusN) (nodes s))
    (connections s) (accounts s) (timestamp s)

systemEvents :: (a2 -> BS) -> (HexN -> a2) -> ((Block0 a1) -> (Account0 
                a1) -> (Timestamp a1) -> (List (Transaction0 a1)) -> HexSPK
                -> Block0 a1) -> ((Block0 a1) -> a1) -> a1 -> (a1 -> a1 ->
                Bool) -> (a1 -> a1 -> a1) -> ((Node0 a1) -> (Timestamp 
                a1) -> (Block0 a1) -> Bool) -> (Option Nat) -> (Timestamp 
                a1) -> (System0 a1) -> System0 a1
systemEvents dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge tfdepth ts sys0 =
  let {
   nodes' = map (\n -> forge_blocks formBlock geN canforge tfdepth n ts)
              (nodes sys0)}
  in
  case partition (\n -> is_nilb (pending_blocks n)) nodes' of {
   Pair nonForgers forgers ->
    let {
     alteredNodes = map (\n_to ->
                      fold_left (\n_to' n_from ->
                        sendBlocks dig2string hashfun geN n_from n_to')
                        forgers n_to) nodes'}
    in
    System
    (map (postforge block_difficulty bN0 geN plusN tfdepth) alteredNodes)
    (connections sys0) (accounts sys0) ts}

systemTransform :: (a1 -> a1) -> (a2 -> BS) -> (HexN -> a2) -> ((Block0 
                   a1) -> (Account0 a1) -> (Timestamp a1) -> (List
                   (Transaction0 a1)) -> HexSPK -> Block0 a1) -> ((Block0 
                   a1) -> a1) -> a1 -> (a1 -> a1 -> Bool) -> (a1 -> a1 -> a1)
                   -> ((Node0 a1) -> (Timestamp a1) -> (Block0 a1) -> Bool)
                   -> (Option Nat) -> (System0 a1) -> Nat -> System0 
                   a1
systemTransform succN dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge tfdepth sys0 count =
  let {t = timestamp sys0} in
  case count of {
   O -> sys0;
   S c' ->
    systemTransform succN dig2string hashfun formBlock block_difficulty bN0
      geN plusN canforge tfdepth
      (systemEvents dig2string hashfun formBlock block_difficulty bN0 geN
        plusN canforge tfdepth (succN t) sys0) c'}

sys :: (a1 -> a1 -> a1) -> (a1 -> a1 -> a1) -> (a1 -> a1) -> (a1 -> a1) ->
       (Nat -> a1) -> (a2 -> BS) -> (HexN -> a2) -> ((Block0 a1) -> (Account0
       a1) -> (Timestamp a1) -> (List (Transaction0 a1)) -> HexSPK -> Block0
       a1) -> ((Block0 a1) -> a1) -> a1 -> (a1 -> a1 -> Bool) -> (a1 -> a1 ->
       a1) -> ((Node0 a1) -> (Timestamp a1) -> (Block0 a1) -> Bool) ->
       (Option Nat) -> Nat -> (Currency a1) -> a1 -> a1 -> Nat -> System0 
       a1
sys multN divN doubleN succN nat2bn dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge tfdepth nFixAccounts systemBalance goalBlockTime maxRand n =
  systemTransform succN dig2string hashfun formBlock block_difficulty bN0 geN
    plusN canforge tfdepth
    (genesisState multN divN doubleN nat2bn bN0 nFixAccounts systemBalance
      goalBlockTime maxRand) n

sysblocks :: (System0 a1) -> List (LTree (Block0 a1))
sysblocks s =
  map blocks (map nodechain (nodes s))

signs :: (a1 -> a1 -> a1) -> (a1 -> a1 -> a1) -> (a1 -> a1) -> (a1 -> a1) ->
         (Nat -> a1) -> (a2 -> BS) -> (HexN -> a2) -> ((Block0 a1) ->
         (Account0 a1) -> (Timestamp a1) -> (List (Transaction0 a1)) ->
         HexSPK -> Block0 a1) -> ((Block0 a1) -> a1) -> a1 -> (a1 -> a1 ->
         Bool) -> (a1 -> a1 -> a1) -> ((Node0 a1) -> (Timestamp a1) ->
         (Block0 a1) -> Bool) -> (Option Nat) -> Nat -> (Currency a1) -> a1
         -> a1 -> Nat -> List (LTree HexSPK)
signs multN divN doubleN succN nat2bn dig2string hashfun formBlock block_difficulty bN0 geN plusN canforge tfdepth nFixAccounts systemBalance goalBlockTime maxRand n =
  map (\tb -> ltree_map (\b -> publicKey (generator b)) tb)
    (map blocks
      (map nodechain
        (nodes
          (sys multN divN doubleN succN nat2bn dig2string hashfun formBlock
            block_difficulty bN0 geN plusN canforge tfdepth nFixAccounts
            systemBalance goalBlockTime maxRand n))))

sysigns :: (System0 a1) -> List (LTree HexSPK)
sysigns s =
  map (\tb -> ltree_map (\b -> publicKey (generator b)) tb) (sysblocks s)

addsucc :: (Nattable Nat) -> Nat -> Nattable Nat
addsucc ht k =
  case search_table k ht of {
   Some v -> modify_key k (plus v (S O)) ht;
   None -> Cons (Pair k (S O)) ht}

generators :: (System0 a1) -> List (Nattable Nat)
generators s =
  map (\tb ->
    ltree_foldl (\ht b -> addsucc ht (hex2nat (publicKey (generator b)))) tb
      Nil) (sysblocks s)

