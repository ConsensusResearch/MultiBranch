Require Export Coq.Lists.List.
Require Export Coq.Arith.EqNat.
Require Import omega.Omega.

(*The basic tree structure for Blocktree construction *)

Import ListNotations.
Local Open Scope list_scope.

Notation "[ ]" := nil.
Notation "[ y ]" := (cons y nil).
Notation "[ x ; .. ; y ]" := (cons x .. ( [ y ] ) ..).

(*helper datatype for induction principle*)
Inductive LTree' (X: Type) : Type :=
| tgen' : X -> LTree' X
| tcons' : X -> LTree' X -> LTree' X
| tfork' : LTree' X -> LTree' X -> LTree' X.

(*the main LTree datatype*)
Inductive LTree (X: Type) : Type :=
| tgen : X -> LTree X
| tcons : X -> LTree X -> LTree X
| tfork : LBranch X -> LTree X -> LTree X  with 
  LBranch (X: Type) : Type := 
  | tbranch : LTree X -> LBranch X.

Implicit Arguments tgen [X].
Implicit Arguments tcons [X].
Implicit Arguments tfork [X].
Implicit Arguments tbranch [X].

Implicit Arguments tgen' [X].
Implicit Arguments tcons' [X].
Implicit Arguments tfork' [X].

Notation "t # a" := (tcons a t) 
                     (left associativity, at level 1).
Notation "tl @ tb" := (tfork (tbranch tb) tl) 
                     (left associativity, at level 1).
Notation "< x >" := (tgen x).

(* last node in the main truck *)
Fixpoint lastnode {X} (t: LTree X) := 
   match t with
   | tgen a => a
   | _ # a => a
   | t1 @ _ => lastnode t1
   end.

(* previous to the last node *)
Fixpoint prev_lastnode {X} (t: LTree X) := 
   match t with
   | tgen a => a
   | l # _ => lastnode l
   | t1 @ _ => prev_lastnode t1
   end.

(* list with ending (hanging) nodes *)

Fixpoint lastforknodes {X} (t: LTree X) :=
match t with
 | tgen x => []
 | l # x => lastforknodes l
 | t1 @ t2 => (lastforknodes t1) ++ (lastnodes t2)
end with

lastnodes {X} (t: LTree X) :=
match t with
 | tgen x => [x]
 | l # x => x::(lastforknodes l)
 | t1 @ t2 => (lastnodes t1) ++ (lastnodes t2)
end.

Definition t73 := (tgen 0)  @ ((tgen 1) # 2) @ (((tgen 5) @ (tgen 100) ) # 6 # 7 @ (tgen 8)) @ (tgen 3) @ (tgen 4) # 13.
Compute (t73, lastnodes t73).

(*tree mapping function*)
Fixpoint ltree_map {X Y} (f:X -> Y) (t: LTree X) :=
match t with
| tgen a => tgen (f a)
| l # a => (ltree_map f l) # (f a)
| l' @ l'' => (ltree_map f l') @ (ltree_map f l'')
end.

(*mapping of the main truck only*)
Fixpoint ltree_list_map {X Y} (f:X -> Y) (t: LTree X) :=
match t with
| tgen a => [f a]
| l # a => (ltree_list_map f l) ++ [f a]
| t1 @ t2 => ltree_list_map f t1
end.

(*fold of the main truck*)
Fixpoint ltree_foldl {X Y} (f: Y -> X -> Y) (t: LTree X) (y0: Y) :=
match t with
| tgen a => f y0 a
| l # a => ltree_foldl f l (f y0 a)
| t1 @ _ => ltree_foldl f t1 y0
end.

(*pair-wise folding*)
Definition fold1 {X} (f: X -> X -> X) (l: list X) := 
let tl := List.tl l in
let cmbl := List.combine tl l in
List.map (fun (z:X*X) => let (x,y):=z in f x y) cmbl.

Check minus.

Compute (fold1 minus [1;2;3;5;9;78]).
Compute (fold1 minus (ltree_list_map (@id nat) (tgen 1)#3#4#5#7#9@(tgen 77)#16)). 

(*embedding LTree->LTree'*)
Fixpoint t2t' {X} (t: LTree X): LTree' X :=
match t with
| tgen x => tgen' x
| tcons x t1 => tcons' x (t2t' t1)
| tfork (tbranch t1) t2 => tfork' (t2t' t1) (t2t' t2) 
end.

(*embedding LTree'->LTree*)
Fixpoint t'2t {X} (t': LTree' X): LTree X :=
match t' with
| tgen' x => tgen x
| tcons' x t1 => tcons x (t'2t t1)
| tfork' t1 t2 => tfork (tbranch (t'2t t1)) (t'2t t2) 
end. 

Check LTree_ind.

(*equivalence of double embedding and id*)

Lemma tt'_id: forall X (t: LTree X), t'2t (t2t' t) = t.
Proof.
 intros. remember (t2t' t) as t'.  generalize dependent t.
 induction t'; intros. destruct t. simpl in Heqt'.
 simpl. inversion Heqt'. auto.
 inversion Heqt'. inversion Heqt'. destruct l.
 inversion H0.  simpl. destruct t.
 inversion Heqt'. simpl in Heqt'.
 inversion Heqt'. assert (t' = t2t' t). apply H1. 
 apply IHt' in H1. rewrite <- H. rewrite <- H1. auto.
 simpl in Heqt'. destruct l. inversion Heqt'.
 destruct t. inversion Heqt'. inversion Heqt'.
 simpl in Heqt'. destruct l.
 simpl. inversion Heqt'. rewrite <- H0.
 rewrite <- H1. rewrite IHt'1 with (t:=l).
 rewrite IHt'2 with (t:=t). auto. auto. auto.
Qed.

Lemma t't_id: forall X (t': LTree' X), t2t' (t'2t t') = t'.
Proof.
 intros. remember (t'2t t') as t.  generalize dependent t.
 induction t'; intros. simpl in Heqt.
 rewrite Heqt. auto. simpl in Heqt. rewrite Heqt.
 simpl. rewrite IHt'. auto. auto.
 simpl in Heqt. rewrite Heqt.
 simpl. rewrite IHt'1. rewrite IHt'2.
 auto. auto. auto.
Qed.
  
(*propositions transform from LTree' to LTree*)
Lemma t'_prop: forall X P, (forall (t': LTree' X), P (t'2t t')) -> (forall t, P t).
Proof.
 intros. replace t with (t'2t (t2t' t)). apply X0.
 apply tt'_id.
Qed.

(*induction principle which eliminate LBranch influence*)
Lemma LTree_ind2: forall (X : Type) (P : LTree X -> Prop),
       (forall x : X, P (tgen x)) ->
       (forall (x : X) (l : LTree X), P l -> P (tcons x l)) ->
       (forall l : LTree X,
        P l -> forall l0 : LTree X, P l0 -> P (tfork (tbranch l) l0)) ->
       forall l : LTree X, P l.
Proof.
 intros. apply t'_prop. intros. induction t'.
 simpl. auto. simpl. auto.  simpl.
 auto.
Qed. 

(*length over the main truck*)
Fixpoint ltreelen {X: Type} (t: LTree X) : nat :=
match t with
| tgen _ => 1
| tcons _ t' => S (ltreelen t')
| tfork _ t' => ltreelen t'
end.

(*number of the tree elements*)
Fixpoint ltreecount {X:Type} (t: LTree X) : nat :=
match t with
| tgen _ =>  1
| tcons _ t' => S (ltreecount t')
| tfork (tbranch t'') t' => (ltreecount t'') + (ltreecount t')
end.


Compute ltreelen (tfork (tbranch (tcons 4 (tgen 3))) (tcons 2 (tgen 1)) ).
Compute ltreecount (tfork (tbranch (tcons 4 (tgen 3))) (tcons 2 (tgen 1)) ).

(*elementary movement*)
Inductive branchpos : Type := 
| mainbr : branchpos
| forkbr : nat -> branchpos.

(*LTree position*)
Definition LTreePos := list branchpos.

(*search function with accumulators*)
Fixpoint search_ltree0 {X} (x: X) (t: LTree X) (eqX: X -> X -> bool) (pos: LTreePos) (f: nat): option LTreePos :=
match t with
| tgen y => if (eqX x y) then Some (pos++[mainbr]) else None
| tcons y t' => if (eqX x y) then Some (pos++[mainbr]) else search_ltree0 x t' eqX (pos++[mainbr]) 0
| tfork (tbranch t'') t' => match search_ltree0 x t'' eqX (pos++[forkbr f]) 0 with
                            | Some p => Some p
                            | None => search_ltree0 x t' eqX pos (f+1)
                            end
end.

(*final search function*)
Definition search_ltree {X} (x: X) (t: LTree X) (eqX: X -> X -> bool) : option LTreePos :=
           search_ltree0 x t eqX [] 0.


(*Examples*)
Definition t1 :=  (tfork (tbranch (tcons 4 (tgen 3))) (tcons 2 (tgen 1)) ).
Compute t1.


Compute search_ltree 1 t1 beq_nat.
Compute search_ltree 2 t1 beq_nat.
Compute search_ltree 10 t1 beq_nat.
Compute search_ltree 3 t1 beq_nat.
Compute search_ltree 4 t1 beq_nat.

Definition b00 := tbranch (tgen 0).
Definition b01 := tbranch (tcons 3 (tcons 2 (tgen 1))).
Definition b02 := tbranch (tfork (tbranch (tgen 4)) (tgen 5)).
Definition t2 := tfork b00 (tfork b01 (tfork b02 (tcons 7 (tcons 8 (tgen 9))))).

Compute t2.

Compute search_ltree 0 t2 beq_nat.
Compute search_ltree 1 t2 beq_nat.
Compute search_ltree 2 t2 beq_nat.
Compute search_ltree 3 t2 beq_nat.
Compute search_ltree 4 t2 beq_nat.
Compute search_ltree 5 t2 beq_nat.
Compute search_ltree 6 t2 beq_nat.
Compute search_ltree 7 t2 beq_nat.
Compute search_ltree 8 t2 beq_nat.
Compute search_ltree 9 t2 beq_nat.

Definition t3 := (tcons 7 (tfork b00 (tfork b01 (tfork b02 (tcons 8 (tgen 9)))))).
Compute search_ltree 0 t3 beq_nat.
Compute search_ltree 1 t3 beq_nat.
Compute search_ltree 2 t3 beq_nat.
Compute search_ltree 3 t3 beq_nat.
Compute search_ltree 4 t3 beq_nat.
Compute search_ltree 5 t3 beq_nat.
Compute search_ltree 6 t3 beq_nat.
Compute search_ltree 7 t3 beq_nat.
Compute search_ltree 8 t3 beq_nat.
Compute search_ltree 9 t3 beq_nat.

(*return the node at the given position*)
Fixpoint getatpos {X:Type} (pos: LTreePos) (t: LTree X) : option X :=
match pos with
| [] => None
| p::ps => match p with
           | mainbr => match t with
                       | tgen x => match ps with
                                   | [] => Some x
                                   | _ => None
                                   end
                       | tcons x t' => match ps with
                                       | [] => Some x
                                       | _ => getatpos ps t'
                                       end
                       | tfork (tbranch t'') t' => getatpos pos t'
                       end
           | forkbr 0 =>  match t with
                          | tgen _ => None
                          | tcons _ _ => None
                          | tfork (tbranch t'') t' => getatpos ps t''
                          end
           | forkbr (S f) =>  match t with
                          | tgen _ => None
                          | tcons _ _ => None
                          | tfork (tbranch t'') t' => getatpos ((forkbr f) :: ps) t'
                          end 
           end                 
                               
end. 

(*Examples*)
Compute search_ltree 0 t3 beq_nat.
Compute getatpos ([mainbr; forkbr 0; mainbr]) t3.

Compute search_ltree 1 t3 beq_nat.
Compute getatpos (rev [mainbr; mainbr; mainbr; forkbr 1; mainbr]) t3.

Compute search_ltree 2 t3 beq_nat.
Compute getatpos (rev [mainbr; mainbr; forkbr 1; mainbr]) t3.

Compute search_ltree 3 t3 beq_nat.
Compute getatpos (rev [mainbr; forkbr 1; mainbr]) t3.

Compute search_ltree 4 t3 beq_nat.
Compute getatpos (rev [mainbr; forkbr 0; forkbr 2; mainbr]) t3.

Compute search_ltree 5 t3 beq_nat.
Compute getatpos (rev [mainbr; forkbr 2; mainbr]) t3.

Compute search_ltree 6 t3 beq_nat.

Compute search_ltree 7 t3 beq_nat.
Compute getatpos (rev [mainbr]) t3.

Compute search_ltree 8 t3 beq_nat.
Compute getatpos (rev  [mainbr; mainbr]) t3.

Compute search_ltree 9 t3 beq_nat.
Compute getatpos (rev [mainbr; mainbr; mainbr]) t3.

(*Type with eq function*)
Parameter CX: Type.
Parameter eqX : CX -> CX -> bool.

Hypothesis eqX_refl: forall y:CX, eqX y y = true.
Hypothesis eqX_ext: forall (Y: Type) (x y: CX) (f: CX -> Y), eqX x y = true -> f x = f y.
Hypothesis eqX_comm: forall (x y: CX), eqX x y = eqX y x.

(*helper lemmas*)

Lemma cons_not: forall X (x:X) l, x::l = l -> False.
Proof.
 intros. generalize dependent x. induction l. intros. inversion H.
 intros. inversion H. apply IHl in H2. auto.
Qed.
 
Lemma app_not: forall X (l l': list X), l'++l = l -> l' = [].
Proof.
 intros. generalize dependent l'. induction l; intros. 
 rewrite <- H. apply app_nil_end.
 replace (l'++a::l) with ((l'++[a])++l) in H.
 destruct l'. auto. inversion H.
 apply IHl in H2. destruct l'. inversion H2.
 inversion H2. rewrite app_ass. simpl. auto.
Qed. 

Lemma search_app_none: forall (x:CX) t p q f,
    search_ltree0 x t eqX p f = None -> 
    search_ltree0 x t eqX (q++p) f = None.
Proof.
 intros. generalize dependent q.
 generalize dependent f. generalize dependent p. generalize dependent t.
 Check LTree_ind2. intros t.
 apply LTree_ind2 with (X:=CX) (l:=t); intros.
 simpl. simpl in H. destruct (eqX x x0).
 inversion H. auto. simpl. simpl in H0.
 destruct (eqX x x0). inversion H0.
 rewrite app_ass. apply H. auto.
 simpl. simpl in H1. 
 remember (search_ltree0 x l eqX (p ++ [forkbr f]) 0) as S0.
 destruct S0. rewrite H1 in HeqS0. inversion H1.
 symmetry in HeqS0. apply H with (q:=q) in HeqS0 .
 rewrite app_ass. rewrite HeqS0.
 apply H0 with (q:=q) in H1. auto.
Qed.

Lemma search_none: forall (x:CX) t p q f g,
    search_ltree0 x t eqX p f = None -> 
    search_ltree0 x t eqX q g = None.
Proof.
 intros. generalize dependent q.
 generalize dependent f. generalize dependent p. generalize dependent g.
 Check LTree_ind2. 
 apply LTree_ind2 with (X:=CX) (l:=t); intros.
 simpl in H. simpl.
 destruct (eqX x x0). inversion H.
 auto. simpl in H0. simpl.
 destruct (eqX x x0). inversion H0. apply H with (f:=0) (p:=p++[mainbr]).
 auto. simpl in H1. simpl.
 remember (search_ltree0 x l eqX (p ++ [forkbr f]) 0) as S0.
 destruct S0. inversion H1. symmetry in HeqS0.
 apply H with (g:=0) (q:=q++[forkbr g]) in HeqS0.
 rewrite HeqS0. apply H0 with (p:=p) (f:=f+1). auto.
Qed.  
   
Lemma search_app: forall (x:CX) t p q r f,
    search_ltree0 x t eqX p f = Some r -> 
    search_ltree0 x t eqX (q++p) f = Some (q++r).
Proof.
 intros. generalize dependent q. generalize dependent r.
 generalize dependent f. generalize dependent p. generalize dependent t.
 Check LTree_ind2. intros t.
 apply LTree_ind2 with (X:=CX) (l:=t); intros.
 simpl. simpl in H. destruct (eqX x x0).
 inversion H. rewrite app_ass.
 auto. inversion H. simpl. simpl in H0.
 destruct (eqX x x0). inversion H0.
 rewrite app_ass. auto. rewrite app_ass.
 apply H. auto. simpl. simpl in H1.
 remember (search_ltree0 x l eqX (p ++ [forkbr f]) 0) as S0.
 destruct S0. symmetry in HeqS0. apply H  with (q:=q) in HeqS0.
 rewrite app_ass. rewrite HeqS0. inversion H1.
 auto. symmetry in HeqS0. apply search_app_none with (q:=q) in HeqS0.
 rewrite app_ass. rewrite HeqS0. apply H0.
 auto.
Qed.  

Lemma search_app2: forall (x:CX) t r p f,
    search_ltree0 x t eqX p f = Some r -> 
    exists q, search_ltree0 x t eqX [] f = Some q /\ r = p++q.
Proof.
 intros. remember (search_ltree0 x t eqX [] f) as S0.
 destruct S0. symmetry in HeqS0. apply search_app with (q:=p) in HeqS0.
 rewrite <- app_nil_end in HeqS0. rewrite H in HeqS0.
 inversion HeqS0. exists l. split.
 auto. auto. symmetry in HeqS0.
 apply search_app_none with (q:= p) in HeqS0.
 rewrite <- app_nil_end in HeqS0.
 rewrite H in HeqS0. inversion HeqS0.
Qed.

Lemma search_not_nil: forall (x:CX) t r p f,
    search_ltree0 x t eqX p f = Some r -> r<>[].
Proof.
 intros. generalize dependent r.
 generalize dependent f. generalize dependent p.
 apply LTree_ind2 with (X:=CX) (l:=t); intros; unfold not; intros. 
 simpl in H. destruct (eqX x x0).
 inversion H. rewrite H0 in H2. 
 destruct p. inversion H2. inversion H2. inversion H.
 simpl in H0. destruct (eqX x x0).
 inversion H0. rewrite H1 in H3.
 destruct p. inversion H3.
 inversion H3. apply H in H0.
 auto. simpl in H1. remember (search_ltree0 x l eqX (p ++ [forkbr f]) 0) as S0.
 destruct S0. symmetry in HeqS0. apply H in HeqS0.
 inversion H1. rewrite <-H4 in H2.  auto.
 apply H0 in H1. auto.
Qed.

Lemma search_f_nomatter: forall (x:CX) t f g r,
      search_ltree0 x t eqX [] f = Some (mainbr::r) -> 
      search_ltree0 x t eqX [] g = Some (mainbr::r).
Proof.
  intros. generalize dependent r.
  generalize dependent f. generalize dependent g.
  apply LTree_ind2 with (X:=CX) (l:=t); intros.
  simpl in H. simpl. auto.
  simpl in H0. simpl. auto.
  simpl in H1. simpl.
  remember (search_ltree0 x l eqX [forkbr f] 0) as S0.
  destruct S0. rewrite H1 in HeqS0.
  symmetry in HeqS0. assert (search_ltree0 x l eqX [forkbr f] 0 = Some (mainbr :: r)).
  auto. apply search_app2 in H2.
  inversion H2. inversion H3.
  clear H2. clear H3. apply search_app with (q:=[forkbr g]) in H4.
  rewrite <- app_nil_end in H4. rewrite H4.
  inversion H5. apply H0 with (g:=g+1) in H1.
  remember (search_ltree0 x l eqX [forkbr g] 0) as S1.
  destruct S1. symmetry in HeqS1. apply search_app2 in HeqS1.
  inversion HeqS1. inversion H2. apply search_app with (q:=[forkbr f]) in H3.
  rewrite <- app_nil_end in H3. rewrite <- HeqS0 in H3. inversion H3.
  auto.
Qed. 

Lemma search_f_nomatter2: forall (x:CX) t r n m,
      search_ltree0 x t eqX [] m = Some ((forkbr n)::r) ->
      n >= m.
Proof.
 intros. generalize dependent r.
  generalize dependent n. generalize dependent m.
  apply LTree_ind2 with (X:=CX) (l:=t); intros.
  simpl in H. destruct (eqX x x0).
 inversion H. inversion H. simpl in H0.
 destruct (eqX x x0). inversion H0. apply search_app2 in H0.
 inversion H0. inversion H1. inversion H3.
 simpl in H1. remember (search_ltree0 x l eqX [forkbr m] 0 ) as S0.
 destruct S0. rewrite H1 in HeqS0. symmetry in HeqS0.
 apply search_app2 in HeqS0. inversion HeqS0.
 inversion H2. inversion H4. omega. apply H0 in H1. omega.
Qed.

Lemma search_fork: forall (x:CX) t r n m,
      search_ltree0 x t eqX [] (S m) = Some ((forkbr (S n))::r) -> 
      search_ltree0 x t eqX [] m = Some ((forkbr n)::r).
Proof.
 intros. generalize dependent r.
  generalize dependent n. generalize dependent m.
  apply LTree_ind2 with (X:=CX) (l:=t); intros.
 simpl in H. simpl. destruct (eqX x x0).
 inversion H. inversion H.
 simpl in H0. simpl. destruct (eqX x x0).
 inversion H0. apply search_app2 in H0.
 inversion H0. inversion H1. inversion H3.
 simpl in H1. simpl. remember (search_ltree0 x l eqX [forkbr (S m)] 0) as S0.
 destruct S0. rewrite H1 in HeqS0. symmetry in HeqS0.
 apply search_app2 in HeqS0. inversion HeqS0.
 inversion H2. apply search_app with (q:=[forkbr m]) in H3.
 rewrite <- app_nil_end in H3. rewrite H3.
 inversion H4. auto. symmetry in HeqS0.
 apply search_none with (g:=0) (q:=[forkbr m]) in HeqS0.
 rewrite HeqS0. apply H0 in H1. auto.
Qed.
      
(*search and get are opposite, one way Theorem*)
Theorem search_get: forall t x pos, search_ltree x t eqX = Some pos -> 
                                  getatpos pos t = Some x.
Proof.
 intros. generalize dependent pos. 
 apply LTree_ind2 with (X:=CX) (l:=t); intros. compute.
 compute in H. remember (eqX x x0) as bx. destruct bx.
 inversion H. apply eqX_ext. rewrite eqX_comm. auto.
 inversion H. unfold search_ltree in H0. simpl in H0.
 simpl. remember (eqX x x0) as bx. destruct bx.
 inversion H0. apply eqX_ext. rewrite eqX_comm. auto.
 apply search_app2 in H0. inversion H0.
 inversion H1. clear H0. clear H1.
 rewrite H3. simpl. destruct x1.
 apply search_not_nil in H2. unfold not in H2.
 assert (False). apply H2. auto. inversion H0.
 apply H. apply H2. unfold search_ltree in H1.
 simpl in H1. remember (search_ltree0 x l eqX [forkbr 0] 0) as S0.
 destruct S0. symmetry in HeqS0. inversion H1.
 rewrite H3 in HeqS0. clear H1. clear H3.
 simpl. destruct pos.
 apply search_not_nil in HeqS0. unfold not in HeqS0.
 assert (False). apply HeqS0. auto. inversion H1.
 destruct b. apply search_app2 in HeqS0.
 inversion HeqS0. inversion H1.
 clear HeqS0. clear H1. inversion H3.
 apply search_app2 in HeqS0.
 inversion HeqS0. inversion H1.
 clear HeqS0. clear H1. inversion H3.
 apply H. apply H2.
 simpl. destruct pos.
 apply search_not_nil in H1. unfold not in H1.
 assert (False). apply H1. auto. inversion H2.
 destruct b. apply H0. apply search_f_nomatter with (g:=0) in H1.
 apply H1. destruct n. apply H.
 apply search_f_nomatter2 in H1.
 inversion H1. auto. compute.
 apply H0. apply search_fork in H1.
 apply H1.
Qed.


(*--------------------------------------------------------------------------------------------------------*)

(*hangs the given trees as forks*)
Fixpoint forks {X} (ff: list (LTree X)) t := 
match ff with
| [] => t
| fx :: fs => (forks fs t) @ fx
end.

(*grow tree with the one element y in every nodes with the specified value x*)
Fixpoint ltree_grow0 {X} (x y: X) (eqX: X -> X -> bool) t (bfork: bool) (lbr: list (LTree X)): LTree X :=
match t with
  | tgen a =>  if (eqX x a) then
                  if (bfork) then forks ((tgen y)::lbr) t
                             else (forks lbr t) # y
               else (forks lbr t)

  | l # a => let l' := ltree_grow0 x y eqX l true [] in
             if (eqX x a) then 
                 if (bfork) then forks ((tgen y)::lbr) (l' # a) 
                            else (forks lbr (l' # a)) # y 
             else (forks lbr (l' # a))
 
  | t' @ t'' => let l'' := ltree_grow0 x y eqX t'' false [] in
                    ltree_grow0 x y eqX t' bfork (l''::lbr)                   
end. 

(*grow tree with the one element y in the first found node with the specified value x*)
(*also returns the uncle in the main truck of the grown node*)
Fixpoint ltree_grow20 {X} (x y: X) (eqX: X -> X -> bool) t (bfork: bool) (lbr: list (LTree X)): (option X * LTree X) :=
match t with
  | tgen a =>  if (eqX x a) then
                  if (bfork) then (Some a, forks ((tgen y)::lbr) t)
                             else (Some a, (forks lbr t) # y)
               else (None, forks lbr t)

  | l # a => 
                             if (eqX x a) then 
                                 let r:= Some a in 
                                 if (bfork) then (r, forks ((tgen y)::lbr) (l # a))
                                            else (r, (forks lbr (l # a)) # y) 
                             else let (mx, l') := ltree_grow20 x y eqX l true [] in (mx, (forks lbr (l' # a)))
              
  | t' @ t'' => let (mx'', l'') := ltree_grow20 x y eqX t'' false [] in
                match mx'' with
                | None => ltree_grow20 x y eqX t' bfork (l''::lbr)
                | Some x'' => (Some (lastnode t'), forks (l''::lbr) t')
                end                   
end.

(*wrappers without accumulators*)
Definition ltree_grow {X} (x:X) y eqX t := ltree_grow0 x y eqX t false [].
Definition ltree_grow2 {X} (x:X) y eqX t := ltree_grow20 x y eqX t false [].


(*Examples*)

Definition t400 := (tgen 0) @ (tgen 1) @ (tgen 2).

Compute ltree_grow0 0 3 beq_nat t400 false [].

Definition t200 := (tgen 0) @ (tgen 4) @ ((tgen 5) # 0 #8) @ ((tgen 6) # 9).
Compute ltree_grow2 0 1 beq_nat t200.

Definition t201 :=(tgen 9) # 8 @ ((tgen 5) @ (tgen 4)) @ ((tgen 1) # 2 # 3) @ (tgen 0).
Compute ltree_grow2 8 7 beq_nat t201.

Definition t20 := tgen 9. 
Definition t21 := ltree_grow2 9 8 beq_nat t20.
Compute t21.
Definition t22 := ltree_grow2 8 7 beq_nat (snd t21).
Compute t22.
Definition t23 := ltree_grow2 8 5 beq_nat (snd t22).
Compute t23.
Definition t24 := ltree_grow2 5 4 beq_nat (snd t23).
Compute t24.
Definition t25 := ltree_grow2 8 1 beq_nat (snd t24).
Compute t25.
Definition t26 := ltree_grow2 1 2 beq_nat (snd t25).
Compute t26.
Definition t27 := ltree_grow2 2 3 beq_nat (snd t26).
Compute t27.
Definition t28 := ltree_grow2 8 0 beq_nat (snd t27).
Compute t28.
Definition t29 := ltree_grow2 2 10 beq_nat (snd t28).
Compute t29.
Definition t210 :=ltree_grow2 10 11 beq_nat (snd t29).
Compute t210.

(*All the forks have the only one ending element*)
Inductive well_balanced {X} : LTree X -> Prop :=
| gen_balanced : forall x, well_balanced (tgen x)
| cons_balanced: forall x t', well_balanced t' -> well_balanced (t' # x)
(*| consfork_balanced: forall x t' t'', well_balanced t'' -> well_balanced t' ->
                                well_balanced (t' @ t'' # x) *)
| forkcons_balanced: forall x t' t'', well_balanced t'' -> well_balanced (t' # x) ->
                                well_balanced (t' @ t'' # x).
  
Check well_balanced_ind.

(*helper lemmas*)

Lemma cons_bal: forall X (x:X) y t, well_balanced t#x -> well_balanced t#y.
Proof.
 intros. remember (t#x) as tx. generalize dependent t. generalize dependent x.
 generalize H.
 induction H; intros. inversion Heqtx. 
 inversion Heqtx. rewrite H3 in H. constructor. auto.
 inversion Heqtx. apply forkcons_balanced. auto.
 apply (IHwell_balanced2 H0 x0 t'). rewrite H3. auto.
Qed. 

Check Forall.

Lemma forks_balanced1: forall X (x:X) t lbr, Forall well_balanced lbr ->
                  well_balanced (t # x) -> well_balanced (forks lbr t) # x.
Proof.
 intros. generalize dependent t. induction lbr. intros.
 simpl. auto.
 intros. simpl. apply forkcons_balanced. inversion H. auto.
 apply IHlbr. inversion H. auto. auto.
Qed. 

Lemma forks_balanced2: forall X (x:X) t lbr, Forall well_balanced lbr ->
                  well_balanced t -> well_balanced (forks lbr t) # x.
Proof.
 intros. apply forks_balanced1.
 auto. constructor. auto.
Qed. 
 
(*as it reads:)*)
Definition cut_tail {X} (t:LTree X) :=
match t with
| tgen _ => t
| t' # a => t'
| _ @ _ => t
end.   

(*long lemma about grown trees which are well balanced*)
Lemma grown_balanced0: forall a x y b lbr t, well_balanced t -> 
                        Forall well_balanced lbr -> 
                        well_balanced (ltree_grow0 x y eqX t false []) /\
                        well_balanced ((ltree_grow0 x y eqX t b lbr) # a) /\
                        well_balanced ((ltree_grow0 x y eqX (cut_tail t) b lbr) # a).
Proof.
 intros. generalize dependent a. generalize dependent b. 
 generalize dependent lbr.  induction H.

 intros.  split.  simpl. destruct (eqX x x0); repeat constructor. split. 
 simpl. destruct (eqX x x0). destruct b. apply forkcons_balanced. constructor.
 apply forks_balanced1. auto. 
 repeat constructor.
 constructor. apply forks_balanced2.
 auto. constructor. apply forks_balanced2.
 auto. constructor. simpl. destruct (eqX x x0). destruct b.
 apply forkcons_balanced.
 constructor. apply forks_balanced1. auto.  repeat constructor.
 constructor. apply forks_balanced2. auto.
 constructor. apply forks_balanced2. auto.
 constructor. 

 intros. simpl.  destruct (eqX x x0). split.
 constructor. apply IHwell_balanced. auto. split. destruct b.
 apply forkcons_balanced. constructor. 
 apply forks_balanced1. auto.  constructor. apply IHwell_balanced. auto.
 constructor. apply forks_balanced2. auto. apply IHwell_balanced.
 auto. apply IHwell_balanced. auto. split. apply IHwell_balanced.
 auto. split. apply forks_balanced2. auto. apply IHwell_balanced. auto.
 apply IHwell_balanced. auto.

 intros. assert (well_balanced (ltree_grow0 x y eqX t'' false [])).
 assert (well_balanced (ltree_grow0 x y eqX t'' false []) /\
                   well_balanced (ltree_grow0 x y eqX t'' b lbr) # a /\
                   well_balanced
                     (ltree_grow0 x y eqX (cut_tail t'') b lbr) # a).
 apply IHwell_balanced1. auto. inversion H2. auto. 
 simpl. split. destruct (eqX x x0).
 constructor.
 apply IHwell_balanced2. constructor. auto.
 auto. apply IHwell_balanced2. constructor.
 auto. auto. destruct (eqX x x0). destruct b.
 split. apply forkcons_balanced. constructor. 
 apply forks_balanced1. auto. 
 constructor. apply IHwell_balanced2. constructor.
 auto. auto. apply IHwell_balanced2. constructor. auto.
 auto. split. constructor. apply forks_balanced2.
 auto. apply IHwell_balanced2. constructor. auto. auto.
 apply IHwell_balanced2. constructor. auto. auto.
 split. apply forks_balanced2. auto. apply IHwell_balanced2. 
 constructor. auto. auto. apply IHwell_balanced2. 
 constructor. auto. auto. 
Qed.

(*what we actually want from the previous lemma is this theorem*)
(*when the balanced tree is growing it is still balanced*)
Theorem grown_balanced: forall (x:CX) y (t: LTree CX), well_balanced t ->                       
                        well_balanced (ltree_grow0 x y eqX t false []).
Proof.
 intros. remember grown_balanced0 as GB.
 remember (GB x x y false [] t H (Forall_nil well_balanced)). inversion  a.
 auto.
Qed.
 
(*simply merge two trees*)
Fixpoint merge_trees {X} t1 t2: LTree X :=
match  t2 with 
| tgen a2 => t1 # a2
| l2 # a2 => (merge_trees t1 l2) # a2
| l2' @ l2'' => (merge_trees t1 l2') @ l2''
end.

(*helper lemma*)
Lemma merge_balanced: forall X (tr1: LTree X) tr2 lb,
      well_balanced tr1 -> Forall well_balanced lb ->
      well_balanced tr2 -> well_balanced (merge_trees (forks lb tr1) tr2).
Proof.
 intros. generalize dependent tr1. induction H1.
 
 intros. simpl. induction lb. simpl. constructor. auto.
 simpl. apply forkcons_balanced. inversion H0.
 auto. apply IHlb. inversion H0. auto.
 intros. simpl. constructor. apply IHwell_balanced.
 auto. intros. simpl.
 apply forkcons_balanced. auto. apply IHwell_balanced2.
 auto.
Qed.

(*like ltree_grow, it tries to add a node y but with forks to all nodes with the given value x*)
Fixpoint merge_node_forks {X} x y (eqX: X -> X -> bool) (t: LTree X) 
              (lbt: option (LTree X) * list (LTree X)) (bfork: bool) (lbr: list (LTree X)) : LTree X :=
match t with
  | tgen a =>  match lbt with
               | (None, lb) => 
                      if (eqX x a) then
                           if (bfork) then forks ((forks lb (tgen y))::lbr) t
                                      else forks lb ((forks lbr t) # y)
                      else forks lbr t
               | (Some lt, lb) => 
                      if (eqX x a) then
                           if (bfork) then forks ((merge_trees (forks lb (tgen y)) lt)::lbr) t
                                      else merge_trees (forks lb ((forks lbr t) # y)) lt
                      else forks lbr t
               end
               

  | l # a => let l' := merge_node_forks x y eqX l lbt true [] in
             match lbt with
               | (None, lb) =>                
                   if (eqX x a) then 
                           if (bfork) then forks ((forks lb (tgen y))::lbr) (l' # a) 
                                      else forks lb ((forks lbr (l' # a)) # y) 
                   else forks lbr (l' # a)
               | (Some lt, lb) =>
                    if (eqX x a) then 
                           if (bfork) then forks ((merge_trees (forks lb (tgen y)) lt)::lbr) (l' # a) 
                                      else merge_trees (forks lb ((forks lbr (l' # a)) # y)) lt
                   else forks lbr (l' # a)
             end 
 
  | t' @ t'' => let l'' := merge_node_forks x y eqX t'' lbt false [] in
                    merge_node_forks x y eqX t' lbt bfork (l''::lbr)                   
end.


(*the same but to the first found node with x, also returns success*)
Fixpoint merge_node_forks2 {X} x y (eqX: X -> X -> bool) (t: LTree X) 
              (lbt: option (LTree X) * list (LTree X)) (bfork: bool) (lbr: list (LTree X)) : bool*LTree X :=
match t with
  | tgen a =>  match lbt with
               | (None, lb) => 
                      if (eqX x a) then
                           if (bfork) then (true, forks ((forks lb (tgen y))::lbr) t)
                                      else (true, forks lb ((forks lbr t) # y))
                      else (false, forks lbr t)
               | (Some lt, lb) => 
                      if (eqX x a) then
                           if (bfork) then (true, forks ((merge_trees (forks lb (tgen y)) lt)::lbr) t)
                                      else (true, merge_trees (forks lb ((forks lbr t) # y)) lt)
                      else (false, forks lbr t)
               end
               

  | l # a => let (b, l') := merge_node_forks2 x y eqX l lbt true [] in
             match lbt with
               | (None, lb) =>                
                   if (eqX x a) then 
                           if (bfork) then (true, forks ((forks lb (tgen y))::lbr) (l # a)) 
                                      else (true, forks lb ((forks lbr (l # a)) # y)) 
                   else (b, forks lbr (l' # a))
               | (Some lt, lb) =>
                    if (eqX x a) then 
                           if (bfork) then (true, forks ((merge_trees (forks lb (tgen y)) lt)::lbr) (l # a)) 
                                      else (true, merge_trees (forks lb ((forks lbr (l # a)) # y)) lt)
                   else (b, forks lbr (l' # a))
             end 
 
  | t' @ t'' => let (b, l'') := merge_node_forks2 x y eqX t'' lbt false [] in
                if b then (true, forks (l''::lbr) t') else
                    merge_node_forks2 x y eqX t' lbt bfork (l''::lbr)                   
end.

Local Open Scope Z_scope.

(*rebalance the tree to have the main truck the largest with the cumulative measure w*)
Fixpoint rebalance {X} (w: X -> Z) (eqX: X -> X -> bool) (s: Z) (t: LTree X) 
                                   (lbr: option (LTree X) * list (LTree X)) : Z * X * LTree X :=
match t with
| tgen a => match lbr with
            | (None, lb) => (s + (w a), a, forks lb t)
            | (Some lt, lb) => (s + (w a), a,  merge_trees (forks lb t) lt)
            end

| t' # a => let (mx , t'b) := rebalance w eqX (s + (w a)) t' (None, []) in let (m, x) := mx in                             
                                    (m, a, merge_node_forks x a eqX t'b lbr false [])

| tfork (tbranch t'') t' => let (px'', t''b) := rebalance w eqX 0 t'' (None, []) in let (p'', x'') := px'' in
                            let (px', t'b) := if s >=? p'' then match lbr with 
                                          | (None, lb) => rebalance w eqX s t' (None, t''b :: lb)
                                          | (Some lt, lb) => rebalance w eqX s t' (Some lt, t''b :: lb)
                                         end
                                         else match lbr with 
                                          | (None, lb) => rebalance w eqX p'' t' (Some t''b, lb)
                                          | (Some lt, lb) => rebalance w eqX p'' t' (Some t''b, lt :: lb)
                                         end in (px', t'b)
end.

(*the same but for abstact type S*)
Fixpoint rebalanceS {X S: Type} (w: X -> S) (eqX: X -> X -> bool) (s0: S) (geS: S-> S -> bool) (plusS: S -> S -> S) 
                                           (s: S) (t: LTree X) 
                                           (lbr: option (LTree X) * list (LTree X)) : S * X * LTree X :=
match t with
| tgen a => match lbr with
            | (None, lb) => (plusS s (w a), a, forks lb t)
            | (Some lt, lb) => (plusS s (w a), a, merge_trees (forks lb t) lt)
            end

| t' # a => let (mx , t'b) := rebalanceS w eqX s0 geS plusS (plusS s (w a)) t' (None, []) in let (m, x) := mx in                             
                                    (m, a, snd (merge_node_forks2 x a eqX t'b lbr false []))

| tfork (tbranch t'') t' => let (px'', t''b) := rebalanceS w eqX s0 geS plusS s0 t'' (None, []) in let (p'', x'') := px'' in
                            let (px', t'b) := if (geS s p'') then match lbr with 
                                          | (None, lb) => rebalanceS w eqX s0 geS plusS s t' (None, t''b :: lb)
                                          | (Some lt, lb) => rebalanceS w eqX s0 geS plusS s t' (Some lt, t''b :: lb)
                                         end
                                         else match lbr with 
                                          | (None, lb) => rebalanceS w eqX s0 geS plusS p'' t' (Some t''b, lb)
                                          | (Some lt, lb) => rebalanceS w eqX s0 geS plusS p'' t' (Some t''b, lt :: lb)
                                         end in (px', t'b)
end.

(*split the tree by the x point, returns the pair*)
Fixpoint ltree_split_till {X} (x: X) (eqX: X->X->bool) (t: LTree X) :=
match t with
| tgen a => if (eqX a x) then (None, Some (tgen a)) else (Some (tgen a), None)
| l # a => if (eqX a x) then (Some l, Some (tgen a)) else 
           match (ltree_split_till x eqX l) with
           | (Some l1, Some l2) => (Some l1, Some (l2#a))
           | (Some l1, None) => (Some (l1#a), None)
           | (None, Some l2) => (None, Some (l2#a))
           | (None, None) => (None, None)
           end
| t1 @ t2 => match (ltree_split_till x eqX t1) with
             | (Some l1, Some l2) => (Some l1, Some (l2 @ t2))
             | (Some l1, None) => (Some (l1 @ t2), None)
             | (None, Some l2) => (None, Some (l2@t2))
             | (None, None) => (None, None)
             end
end.

Definition pairfun {X: Type} (f: X -> X -> X) (p: option X * option X) := 
match p with
| (Some x, Some y) => Some (f x y)
| (Some x, None) => Some x
| (None, Some y) => Some y
| (None, None) => None
end.

Lemma split_correct: forall (x:CX) t, pairfun merge_trees (ltree_split_till x eqX t) = Some t.
Proof.
 intros. apply LTree_ind2 with (X:=CX) (l:=t); intros.
 simpl. destruct (eqX x0 x). auto. auto.
 simpl. destruct (eqX x0 x). auto.
 remember (ltree_split_till x eqX l) as tsp.
 destruct tsp. destruct o. destruct o0.
 simpl in H. simpl. inversion H.
 auto. simpl. simpl in H. inversion H. auto.
 destruct o0. simpl. simpl in H. inversion H.
 auto. inversion H.
 simpl. remember (ltree_split_till x eqX l0) as tsp0.
 destruct tsp0. destruct o. destruct o0.
 simpl. simpl in H0. inversion H0. auto.
 simpl. simpl in H0. inversion H0.
 auto. destruct o0. simpl. simpl in H0.
 inversion H0. auto. inversion H0. 
Qed.

(*rebalance only tail*)
Definition rebalanceS_till {X S: Type} (x:X) (w: X -> S) (eqX: X -> X -> bool) (s0: S) (geS: S-> S -> bool) (plusS: S -> S -> S) 
                                           (s: S) (t: LTree X) :=
let (t1, t2):= ltree_split_till x eqX t in
match (t1, t2) with
| (Some t1, Some t2) => merge_trees t1 (snd (rebalanceS w eqX s0 geS plusS s t2 (None, [])))
| (None , Some t2) => snd (rebalanceS w eqX s0 geS plusS s t2 (None, []))
| (Some t1, None) => t1
| (None, None) => t
end.

Local Open Scope nat_scope.

(*Examples*)
Print t3.
Compute t3.
(* < 9 > # 8 @ (< 5 > @ < 4 >) @ (< 1 > # 2 # 3) @ < 0 > # 7 *) 

Compute rebalance (fun _ => 1%Z) (beq_nat) 0 t3 (None, []).

Definition t100 := (tgen 0)  @ ((tgen 1) # 2) @ (((tgen 5) @ (tgen 100) ) # 6 # 7 @ (tgen 8)) @ (tgen 3) @ (tgen 4) .
Compute t100.
(*< 0 > @ (< 1 > # 2) @ (< 5 > @ < 100 > # 6 # 7 @ < 8 >) @ < 3 > @
       < 4 >*)
Compute  rebalance (fun _ => 1%Z) (beq_nat) 0 t100 (None, []).
Compute ltree_grow 0 1 beq_nat ((tgen 0) @  (tgen 4)).


Definition t104 := (tgen 0) @ (tgen 1) @ (tgen 2).
Compute  rebalance (fun _ => 1%Z) (beq_nat) 0 t104 (None, []).


Lemma merge_grow: forall x y t b lbr, 
                 merge_node_forks x y eqX t (None,[]) b lbr =
                 ltree_grow0 x y eqX t b lbr.
Proof.
 intros. generalize dependent b.
 generalize dependent lbr. 
 apply LTree_ind2 with (X:=CX) (l:=t); intros.
 simpl. auto.
 simpl. destruct (eqX x x0); destruct b; rewrite H; auto.
 simpl. rewrite H. auto.
Qed.

Local Open Scope Z_scope.
Require Export Coq.ZArith.Zhints.
Require Export Coq.ZArith.BinInt.

Import Z.

Lemma rebalance1_morezero: forall (t: LTree CX) (n:Z) lt lb, 
    n >= 0 -> fst (fst (rebalance (fun _ => 1%Z) eqX n t (lt, lb))) >? 0 = true.
Proof.
 intros. generalize dependent n. generalize dependent lt0.
 generalize dependent lb.
 apply LTree_ind2 with (X:=CX) (l:=t0); intros.

 simpl. destruct lt0. simpl. rewrite -> gtb_lt. omega.
 simpl. rewrite -> gtb_lt. omega.
 simpl. remember (rebalance (fun _ : CX => 1) eqX (n + 1) l (None, [])) as rb.
 destruct rb. destruct p. simpl. replace z with (fst (fst (z,c,l0))).
 rewrite Heqrb. simpl. apply H. omega. auto.
 simpl. remember (rebalance (fun _ : CX => 1) eqX 0 l (None, [])) as rb.
 destruct rb. destruct p. remember (geb n z) as genz. destruct genz.
 destruct lt0. remember (rebalance (fun _ : CX => 1) eqX n l0 (Some l2, l1 :: lb)) as rb2.
 destruct rb2. rewrite Heqrb2. apply H0. auto.  
 remember (rebalance (fun _ : CX => 1) eqX n l0 (None, l1 :: lb)) as rb2.
 destruct rb2. rewrite Heqrb2. apply H0. auto.
 destruct lt0.  remember (rebalance (fun _ : CX => 1) eqX z l0 (Some l1, l2 :: lb) ) as rb2.
 destruct rb2. rewrite Heqrb2. apply H0. assert (lt 0 z). rewrite <- gtb_lt.
 replace z with (fst (fst (z,c,l1))).
 rewrite Heqrb. apply H. omega. auto. omega. 
 remember (rebalance (fun _ : CX => 1) eqX z l0 (Some l1, lb)) as rb2.
 destruct rb2. rewrite Heqrb2. apply H0.
 assert (lt 0 z). rewrite <- gtb_lt.
 replace z with (fst (fst (z,c,l1))).
 rewrite Heqrb. apply H. omega. auto. omega.
Qed.

Lemma merge_balanced20: forall x y z bf t lt lb lbr,
      well_balanced lt -> Forall well_balanced lb -> Forall well_balanced lbr ->
      well_balanced t ->
      well_balanced (merge_node_forks x y eqX t (Some lt, lb) false []) /\
      well_balanced (merge_node_forks x y eqX t (Some lt, lb) bf lbr) # z /\
      well_balanced (merge_node_forks x y eqX (cut_tail t) (Some lt, lb) bf lbr) # z.
Proof.
 intros. generalize dependent lt0. generalize dependent lbr.
 generalize dependent lb. generalize dependent z. generalize dependent bf. 
 
 induction H2; intros.
 
 split. simpl. destruct (eqX x x0). apply merge_balanced.
 repeat constructor. auto. auto. constructor.
 simpl. destruct (eqX x x0). destruct bf. split.
 apply forkcons_balanced. apply merge_balanced.
 constructor. auto. auto. apply forks_balanced2.
 auto. constructor. apply forkcons_balanced.
 apply merge_balanced. constructor. auto.
 auto. apply forks_balanced2. auto. constructor.
 split. constructor. apply merge_balanced.
 apply forks_balanced2. auto. constructor. auto.
 auto. constructor. apply merge_balanced. apply forks_balanced2.
 auto. constructor. auto. auto. split.
 apply forks_balanced2. auto. constructor.
 apply forks_balanced2. auto. constructor.

 split. simpl. destruct (eqX x x0).
 apply merge_balanced. constructor.
 apply IHwell_balanced. auto.
 auto. auto. auto. auto. apply IHwell_balanced.
 auto. auto. auto. split.
 simpl. destruct (eqX x x0). destruct bf.
 apply forkcons_balanced. apply merge_balanced.
 constructor. auto. auto. apply forks_balanced2.
 auto. apply IHwell_balanced. auto. auto. auto. 
 constructor. apply merge_balanced.
 apply forks_balanced2. auto. apply IHwell_balanced.
 auto. auto. auto. auto. auto. apply forks_balanced2.
 auto. apply IHwell_balanced. auto. auto. auto.
 simpl. apply IHwell_balanced. auto. auto.
 auto.

 split. simpl. destruct (eqX x x0).
 apply merge_balanced. constructor.
 apply IHwell_balanced2. auto. constructor.
 remember (IHwell_balanced1 bf z lb H0 lbr H1 lt0 H).
 inversion a. auto. auto. auto. auto. auto.
 apply IHwell_balanced2. auto. constructor.
 remember (IHwell_balanced1 bf z lb H0 lbr H1 lt0 H).
 inversion a. auto. auto. auto. split.
 simpl. destruct (eqX x x0). destruct bf.
 apply forkcons_balanced. apply merge_balanced.
 constructor. auto. auto. apply forks_balanced2.
 auto. apply IHwell_balanced2. auto. constructor.
 remember (IHwell_balanced1 false z lb H0 lbr H1 lt0 H).
 inversion a. auto. auto. auto. constructor.
 apply merge_balanced. apply forks_balanced2.
 auto. apply IHwell_balanced2. auto. constructor.
 remember (IHwell_balanced1 false z lb H0 lbr H1 lt0 H).
 inversion a. auto. auto. auto. auto. auto.
 apply forks_balanced2. auto. apply IHwell_balanced2.
 auto. constructor. remember (IHwell_balanced1 false z lb H0 lbr H1 lt0 H).
 inversion a. auto. auto. auto. simpl.
 apply IHwell_balanced2. auto. constructor.
 remember (IHwell_balanced1 false z lb H0 lbr H1 lt0 H).
 inversion a. auto. auto. auto.
Qed. 

Lemma merge_balanced2: forall x y t lt lb,
      well_balanced lt -> Forall well_balanced lb -> 
      well_balanced t ->
      well_balanced (merge_node_forks x y eqX t (Some lt, lb) false []).
Proof.
 intros. remember (merge_balanced20 x y x false t0 lt0 lb [] H H0 (Forall_nil well_balanced) H1).
 inversion a. auto.
Qed.

Lemma grownforks_balanced: forall x0 x lbt lbr,
      Forall well_balanced lbt -> Forall well_balanced lbr -> 
     well_balanced (ltree_grow0 x0 x eqX (forks lbt (tgen x0)) false lbr).
Proof.
 intros. generalize dependent lbr.  induction lbt.
 intros. simpl. rewrite eqX_refl. apply forks_balanced2.
 auto. constructor.
 intros. simpl. apply IHlbt. inversion H. auto.
 constructor. apply grown_balanced. inversion H. auto. auto.  
Qed.

Hypothesis reb_grow0: forall l2 n l0 lbt lbr lb x, Forall well_balanced lbt -> Forall well_balanced lbr ->
      l2 = rebalance (fun _ : CX => 1) eqX n l0 (None, lbt) ->
      well_balanced (merge_node_forks (snd (fst l2)) x eqX (snd l2) (None, lb) false lbr).

Hypothesis reb_grow1: forall l2 n l0 lbt lbr x, Forall well_balanced lbt -> Forall well_balanced lbr ->
      l2 = rebalance (fun _ : CX => 1) eqX n l0 (None, lbt) ->
      well_balanced (ltree_grow0 (snd (fst l2)) x eqX (snd l2) false lbr).

Hypothesis reb_grow2: forall l2 n l0 lbt lbr lb lt0 x, Forall well_balanced lbt -> Forall well_balanced lbr ->
      l2 = rebalance (fun _ : CX => 1) eqX n l0 (None, lbt) ->
      well_balanced (merge_node_forks (snd (fst l2)) x eqX (snd l2) (Some lt0, lb) false lbr).

(*PROVE  rebalance (rebalance t # x) = (rebalance t) # x*)

Theorem rebalanced: forall x t n lt lb,
    well_balanced lt -> Forall well_balanced lb ->   
    well_balanced (snd (rebalance (fun _ => 1%Z) eqX 0 t (None, []))) /\
    well_balanced (snd (rebalance (fun _ => 1%Z) eqX n (t#x) (None, []))) /\
    well_balanced (snd (rebalance (fun _ => 1%Z) eqX n t (Some lt, lb))) /\
    well_balanced (snd (rebalance (fun _ => 1%Z) eqX n (t#x) (Some lt, lb))).
Proof.
 intros. generalize dependent n. generalize dependent lt0.
 generalize dependent lb. generalize dependent x. 
 apply LTree_ind2 with (X:=CX) (l:=t0); intros.

 simpl. split. constructor. split. rewrite eqX_refl. 
 repeat constructor. split. apply merge_balanced. constructor. auto. auto.
 rewrite eqX_refl. apply merge_balanced. repeat constructor. auto. auto.

 split. simpl. remember (H x [] (Forall_nil well_balanced) lt0 H1 0%Z).
 inversion a.  inversion H3. simpl in H4. auto. 
 split. simpl. remember (H x [] (Forall_nil well_balanced) lt0 H1 (n+1)).
 inversion a. inversion H3. simpl in H4. 
 remember (rebalance (fun _ : CX => 1%Z) eqX (n + 1 + 1) l (None, [])) as rb.
 destruct rb. destruct p. simpl. 
 rewrite merge_grow. rewrite merge_grow. rewrite merge_grow in H4.
 apply grown_balanced. auto. auto.
 split. apply H. auto. auto. remember (l # x) as lx.
 simpl. remember (rebalance (fun _ : CX => 1) eqX (n + 1) lx (None, [])) as rb.
 destruct rb. destruct p. simpl. apply merge_balanced2.
 auto. auto. replace l0 with (snd (z, c, l0)).
 rewrite Heqrb. rewrite Heqlx. remember (H x lb H0 lt0 H1 (n+1)).
 inversion a. inversion H3.  auto. auto.
 
 split. simpl.  remember (rebalance (fun _ : CX => 1) eqX 0 l (None, [])) as rb.
 destruct rb. destruct p. remember (geb 0 z) as gez.
 destruct gez. symmetry in Heqgez. rewrite  geb_le in Heqgez.
 assert (gtb z 0 = true). replace z with (fst (fst ((z, c, l1)))).
 rewrite Heqrb. apply rebalance1_morezero. omega. auto. 
 rewrite gtb_lt in H3. omega.
 remember (rebalance (fun _ : CX => 1) eqX z l0 (Some l1, [])) as rb1.
 destruct rb1. rewrite Heqrb1. apply H0.
 apply x. auto. remember (H x [] (Forall_nil well_balanced) lt0 H2 0%Z).
 inversion a. auto. split.
 simpl. remember (rebalance (fun _ : CX => 1) eqX 0 l (None, [])) as rb1.
 destruct rb1. destruct p. remember (geb (n+1) z) as gez.
 destruct gez. remember (rebalance (fun _ : CX => 1) eqX (n + 1) l0 (None, [l1])) as rb2.
 destruct rb2. destruct p. simpl. rewrite merge_grow.
 replace c0 with (snd (fst (z0, c0, l2))).
 replace l2 with (snd (z0, c0, l2)).
 apply reb_grow1 with (n:=n+1) (l0:=l0) (lbt:=[l1]).
 constructor. remember (H x [] (Forall_nil well_balanced) lt0 H2 0%Z).
 inversion a. auto. auto. auto. auto. auto. auto.
 remember (rebalance (fun _ : CX => 1) eqX z l0 (Some l1, [])) as rb1.
 destruct rb1. destruct p. simpl.
 rewrite merge_grow. apply grown_balanced.
 replace l2 with (snd (z0, c0, l2)). rewrite Heqrb0.
 apply H0. apply c0. auto. remember (H x [] (Forall_nil well_balanced) lt0 H2 0%Z).
 inversion a. auto. auto. 
 split. simpl. remember (rebalance (fun _ : CX => 1) eqX 0 l (None, [])) as rb.
 destruct rb. destruct p. remember (geb n z) as gez.
 destruct gez. remember (rebalance (fun _ : CX => 1) eqX n l0 (Some lt0, l1 :: lb)) as rb1.
 destruct rb1. rewrite Heqrb1. apply H0. apply x.
 constructor. remember (H x [] (Forall_nil well_balanced) lt0 H2 0%Z).
 inversion a. auto. auto. auto. remember (rebalance (fun _ : CX => 1) eqX z l0 (Some l1, lt0 :: lb)) as rb1.
 destruct rb1. rewrite Heqrb1. apply H0.
 apply x. constructor. auto. auto. remember (H x [] (Forall_nil well_balanced) lt0 H2 0%Z).
 inversion a. auto. simpl. remember (rebalance (fun _ : CX => 1) eqX 0 l (None, [])) as rb.
 destruct rb. destruct p. remember (geb (n+1) z) as gez.
 destruct gez. remember (rebalance (fun _ : CX => 1) eqX (n + 1) l0 (None, [l1])) as rb1.
 destruct rb1. destruct p. simpl.  
 replace l2 with (snd (rebalance (fun _ : CX => 1) eqX (n + 1) l0 (None, [l1]))).
 replace c0 with (snd (fst (rebalance (fun _ : CX => 1) eqX (n + 1) l0 (None, [l1])))).
 apply reb_grow2 with (n:=n+1) (l0:=l0) (lbt:=[l1]).
 constructor. remember (H x [] (Forall_nil well_balanced) lt0 H2 0%Z).
 inversion a. auto. auto. auto. auto. rewrite <- Heqrb1.
 auto. rewrite <- Heqrb1. auto.
 remember (rebalance (fun _ : CX => 1) eqX z l0 (Some l1, [])) as rb1.
 destruct rb1. destruct p. simpl. apply merge_balanced2.
 auto. auto. replace l2 with (snd (z0, c0, l2)). rewrite Heqrb1.
 apply H0. apply c0. auto. remember (H x [] (Forall_nil well_balanced) lt0 H2 0%Z).
 inversion a. auto. auto.
Qed.




 
                                   
 














