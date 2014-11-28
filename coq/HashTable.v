Require Export Coq.Lists.List.
Require Export Coq.Arith.EqNat.
Require Import omega.Omega.

(*Primitive realization of tables of naturals to any type*)

Import ListNotations.
Local Open Scope list_scope.

Notation "[ ]" := nil.
Notation "[ y ]" := (cons y nil).
Notation "[ x ; .. ; y ]" := (cons x .. ( [ y ] ) ..).

Set Implicit Arguments.
Unset Strict Implicit.

Definition nattable (V: Type) : Type := list (nat * V).

Inductive in_table {V: Type} : nat -> nattable V -> Prop :=
| in_table_here: forall k t v', in_table k ((k, v')::t)
| in_table_later: forall k k' v' t, in_table k t -> in_table k ((k', v')::t).

Fixpoint search_table {V: Type} (k: nat) (t: nattable V): option V :=
match t with 
| [] => None
| (k', v) :: t' => if (beq_nat k k') then (Some v) else search_table k t'
end.

Inductive uniq_table {V: Type} : nattable V -> Prop :=
| uniqnil: uniq_table []
| uniqt: forall k v t, uniq_table t -> ~in_table k t -> uniq_table ((k, v)::t).

Definition add_uniqtable {V: Type} k v (t: nattable V) : nattable V :=
match (search_table k t) with
| None   => (k, v) :: t
| Some _ => t
end.

Check beq_nat_eq.

Lemma search_intable: forall (V:Type) k t, 
                         in_table k t <-> exists (v': V), search_table k t = Some v'.
Proof with auto.
 intros. split. intros. induction t. inversion H.
 inversion H. exists v'. simpl.
 rewrite <- beq_nat_refl...
 remember (beq_nat k k') as b. destruct b.
 exists v'. simpl. rewrite <- Heqb...
 apply IHt in H2. inversion H2. exists x.
 simpl. rewrite <- Heqb...
 intros. inversion H. clear H. generalize dependent x. induction t. intros. inversion H0.
 intros. destruct a. remember (beq_nat k n) as b. destruct b.
 symmetry in Heqb. symmetry in Heqb. apply beq_nat_eq in Heqb. rewrite Heqb. constructor.
 simpl in H0. rewrite <- Heqb in H0.  apply IHt in H0.
 constructor...
Qed.
 

Lemma add_uniqtable_uniq: forall (V: Type) (k: nat) (v:V) t, uniq_table t ->
                                             uniq_table (add_uniqtable k v t).
Proof.
 intros. induction t. unfold add_uniqtable.
 simpl. assert (~in_table k (@nil (nat*V))).
 intros. unfold not. intros. inversion H0. constructor; auto.
 unfold add_uniqtable.
 remember (search_table k (a :: t)) as vv.
 destruct vv; try constructor; auto.
 intros. unfold not. intros. apply search_intable in H0.
 inversion H0. rewrite H1 in Heqvv. inversion Heqvv.
Qed.

Fixpoint search_place_table0 {V: Type} (k: nat) (t: nattable V) (t': nattable V): option (V * nattable V) :=
match t with 
| [] => None
| (k', v) :: t'' => if (beq_nat k k') then (Some (v, t'++t'')) else
                                      search_place_table0 k t'' (t'++[(k',v)])
end.

Definition search_place_table {V: Type} (k: nat) (t: nattable V) := search_place_table0 k t [].

Definition modify_key {V: Type} k v (t: nattable V) : nattable V :=
match (search_place_table k t) with
| None => t
| Some (_, tb) => (k,v)::tb
end.

Lemma tail_nomatter: forall V k (t:nattable V) l l', 
                    search_place_table0 k t l = None -> search_place_table0 k t l' = None.
Proof.
 intros. generalize dependent l. generalize dependent l'. induction t.
 intros. auto. intros.
 simpl in H. destruct a. remember (beq_nat k n) as b. destruct b.
 inversion H. simpl. rewrite <- Heqb. apply IHt with (l:=(l++[(n,v)])).
 auto.
Qed.
 
 
Lemma none_place: forall (V: Type) k (t: nattable V), search_table k t = None <-> search_place_table k t = None.
Proof.
 intros. split. intros. induction t. unfold search_place_table. auto.
 simpl in H. destruct a. remember (beq_nat k n) as b. destruct b.
 inversion H. unfold search_place_table.  simpl.
 rewrite <- Heqb. apply IHt in H. apply tail_nomatter with (l:=[]).
 apply H. intros.
 induction t. auto.
 simpl. destruct a. remember (beq_nat k n) as b. destruct b.
 unfold search_place_table in H. simpl in H. rewrite <- Heqb in H.
 inversion H. apply IHt. unfold search_place_table in H. simpl in H.
 rewrite <- Heqb in H. apply tail_nomatter with (l:=[(n,v)]). auto.
Qed.

Lemma modify_search: forall V k (v:V) t, in_table k t -> search_table k (modify_key k v t) = Some v.
Proof.
 intros. induction t. inversion H.
 inversion H. unfold modify_key. unfold search_place_table.
 simpl. rewrite <- beq_nat_refl. simpl. rewrite <- beq_nat_refl. auto.
 unfold modify_key. unfold search_place_table.
 simpl. remember (beq_nat k k') as b.
 destruct b. simpl. rewrite <- beq_nat_refl. auto.
 remember (search_place_table0 k t [(k', v')]) as vv.
 destruct vv. destruct p. simpl. rewrite <- beq_nat_refl. auto.
 symmetry in Heqvv. simpl. rewrite <- Heqb.
 apply tail_nomatter with (l':=[]) in Heqvv.
 apply none_place in Heqvv. apply search_intable in H2.
 inversion H2. rewrite Heqvv in H4. inversion H4.
Qed.

Lemma search_inplace_some: forall X k t l1 l2 l' (v:X), search_place_table0 k t l1 = Some (v, l') -> 
                           search_place_table0 k t (l2++l1) = Some (v, l2++l').
Proof.
 intros. generalize dependent l1. generalize dependent l2.
 induction t. intros. simpl in H. inversion H.
 intros. simpl. destruct a. remember (beq_nat k n) as b.
 destruct b. simpl in H. rewrite <- Heqb in H.
 inversion H. rewrite app_ass. auto.
 simpl in H. rewrite <- Heqb in H.
 apply IHt with (l2:=l2) in H.
 rewrite app_ass. auto.
Qed. 

Lemma not_in_search: forall X n k t (v:X) l, ~in_table n t -> search_place_table k t = Some (v, l) -> ~in_table n l.
Proof.
 intros. generalize dependent v. generalize dependent l.
 induction t. intros. unfold search_place_table in H0.
 inversion H0. intros. unfold search_place_table in H0.
 simpl in H0. destruct a. remember (beq_nat k n0) as b.
 destruct b. unfold not in H.
 unfold not. intros. inversion H0. rewrite H4 in H. 
 assert (in_table n ((n0, x) :: l)). constructor. auto.
 apply H. auto. unfold not. intros.
 remember (search_place_table0 k t []) as vv.
 destruct vv. destruct p. symmetry in Heqvv.
 assert (search_place_table k t = Some (x0, n1)).
 unfold search_place_table. auto. apply search_inplace_some with (l2:=[(n0,x)]) in Heqvv.
 simpl in Heqvv. rewrite H0 in Heqvv. inversion Heqvv.
 apply IHt in H2. rewrite H5 in H1. inversion H1.
 assert  (in_table n ((n0, x) :: t)).
 rewrite H7. constructor. apply H. auto.
 apply H2. auto. unfold not. intros.
 assert (in_table n ((n0, x) :: t)). constructor. auto.
 apply H. auto. symmetry in Heqvv. apply tail_nomatter with (l':=[(n0, x)]) in Heqvv .
 rewrite Heqvv in H0. inversion H0.
Qed.

Lemma uniq_search_uniq: forall X k (v:X) l t, uniq_table t -> search_place_table k t = Some (v, l) -> 
                        uniq_table l.
Proof.
 intros. generalize dependent v. generalize dependent l. induction t. intros.
 unfold search_place_table in H0. inversion H0.
 intros. unfold search_place_table in H0.  simpl in H0.
 destruct a. remember (beq_nat k n) as b. destruct b.
 inversion H0. inversion H. rewrite <- H3. auto.
 remember (search_place_table0 k t []) as vv.
 destruct vv. destruct p. symmetry in Heqvv.  
 remember (Heqvv) as Heqvv'. 
 assert (search_place_table k t = Some (x0, n0)).
 unfold search_place_table.  auto.
 apply IHt in H1. clear HeqHeqvv'.
 apply search_inplace_some with (l2:=[(n,x)]) in Heqvv'.
 simpl in Heqvv'. rewrite H0 in Heqvv'.
 inversion Heqvv'. constructor.
 auto. apply not_in_search with (k:=k) (t:=t) (v:=x0).
 unfold not. intros. inversion H.
 apply H9. auto. unfold  search_place_table.  auto.
 inversion H. auto. symmetry in Heqvv.
 apply tail_nomatter with (l':=[(n, x)]) in Heqvv.
 rewrite H0 in Heqvv. inversion Heqvv.
Qed.
 

Lemma uniq_modify_uniq: forall X k (v:X) t, uniq_table t -> uniq_table (modify_key k v t).
Proof.
 intros. induction t. unfold modify_key.
 unfold search_place_table. simpl. auto.
 unfold modify_key. unfold search_place_table.
 simpl. destruct a. remember (beq_nat k n) as b. destruct b.
 symmetry in Heqb. symmetry in Heqb. apply beq_nat_eq in Heqb.
 rewrite Heqb. inversion H. constructor; auto.
 remember (search_place_table0 k t [(n, x)]) as vv.
 destruct vv. destruct p. symmetry in Heqvv.
 inversion H.  apply IHt in H2.
 unfold modify_key in H2. unfold search_place_table in H2.
 remember (search_place_table0 k t []) as vv'. destruct vv'.
 destruct p. symmetry in Heqvv'. assert (search_place_table k t = Some (x1, n1)).
 unfold  search_place_table. auto.
 apply search_inplace_some with (l2:=[(n,x)]) in Heqvv'.
 simpl in Heqvv'. rewrite Heqvv in Heqvv'.
 inversion Heqvv'. assert (~in_table n n1). apply not_in_search with (k:=k) (t:=t) (v:=x1).
 auto. auto. constructor. constructor. inversion H2.
 auto. auto. unfold not. intros.
 inversion H9. rewrite H12 in Heqb. rewrite <- beq_nat_refl in Heqb.
 inversion Heqb. inversion H2. apply H19. auto.
 symmetry in Heqvv'. apply tail_nomatter with (l':=[(n, x)]) in Heqvv' .
 rewrite Heqvv in Heqvv'. inversion Heqvv'.
 auto.
Qed.


 
 
 























                                


