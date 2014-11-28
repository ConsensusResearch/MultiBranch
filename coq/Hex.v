Require Export Coq.Lists.List.
Require Export NArith.
Require Export Coq.Arith.EqNat.
Import ListNotations.


Local Open Scope nat_scope.
Local Open Scope list_scope.

Inductive hex :=
| H0: hex
| H1: hex
| H2: hex
| H3: hex
| H4: hex
| H5: hex
| H6: hex
| H7: hex
| H8: hex
| H9: hex
| HA: hex
| HB: hex
| HC: hex
| HD: hex
| HE: hex
| HF: hex.

Definition hex2nat (h: hex) :=
match h with
| H0 => 0
| H1 => 1
| H2 => 2
| H3 => 3
| H4 => 4
| H5 => 5
| H6 => 6
| H7 => 7
| H8 => 8
| H9 => 9
| HA => 10
| HB => 11
| HC => 12
| HD => 13
| HE => 14
| HF => 15
end.

Definition succH (h: hex) :=
match h with
| H0 => H1
| H1 => H2
| H2 => H3
| H3 => H4
| H4 => H5
| H5 => H6
| H6 => H7
| H7 => H8
| H8 => H9
| H9 => HA
| HA => HB
| HB => HC
| HC => HD
| HD => HE
| HE => HF
| HF => H0
end.

Definition hex2N (h: hex) := N.of_nat (hex2nat h).

Definition HexN := list hex.

Local Open Scope N_scope.
Fixpoint hexN2N' (n:N) (hn: HexN) : N :=
match hn with
| [] => 0
| h::hs => ((hex2N h) * (16^n))+(hexN2N' (n+1) hs)
end. 

Definition hexN2N := hexN2N' 0.

Example hex1 : hexN2N [H0; H2; HF] = 3872.
Proof.
 unfold hexN2N. simpl. auto.
Qed.

Fixpoint pos2hexN (n:positive) := 
match n with
| 1%positive => [H1]
| 2%positive => [H2]
| 3%positive => [H3]
| 4%positive => [H4]
| 5%positive => [H5]
| 6%positive => [H6]
| 7%positive => [H7]
| 8%positive => [H8]
| 9%positive => [H9]
| 10%positive => [HA]
| 11%positive => [HB]
| 12%positive => [HC]
| 13%positive => [HD]
| 14%positive => [HE]
| 15%positive => [HF]
| (xO (xO (xO (xO n')))) => H0::(pos2hexN n')
| (xI (xO (xO (xO n')))) => H1::(pos2hexN n')
| (xO (xI (xO (xO n')))) => H2::(pos2hexN n')
| (xI (xI (xO (xO n')))) => H3::(pos2hexN n')
| (xO (xO (xI (xO n')))) => H4::(pos2hexN n')
| (xI (xO (xI (xO n')))) => H5::(pos2hexN n')
| (xO (xI (xI (xO n')))) => H6::(pos2hexN n')
| (xI (xI (xI (xO n')))) => H7::(pos2hexN n')
| (xO (xO (xO (xI n')))) => H8::(pos2hexN n')
| (xI (xO (xO (xI n')))) => H9::(pos2hexN n')
| (xO (xI (xO (xI n')))) => HA::(pos2hexN n')
| (xI (xI (xO (xI n')))) => HB::(pos2hexN n')
| (xO (xO (xI (xI n')))) => HC::(pos2hexN n')
| (xI (xO (xI (xI n')))) => HD::(pos2hexN n')
| (xO (xI (xI (xI n')))) => HE::(pos2hexN n')
| (xI (xI (xI (xI n')))) => HF::(pos2hexN n')
end.
 

Fixpoint N2hexN (n:N) := 
match n with
| N0 => [H0]
| Npos n' => pos2hexN n'
end.

Example hex2 : N2hexN 3872 = [H0; H2; HF].
Proof.
 simpl. auto.
Qed.

Check (beq_nat).

Definition eqb_hex (h1 h2: hex) : bool := beq_nat (hex2nat h1) (hex2nat h2).


Fixpoint eqb_hexs (bs1 bs2: HexN) : bool :=
match (bs1, bs2) with
| ([], []) => true
| ([], _) => false
| (_, []) => false
| (x::xs, y::ys) => match (eqb_hex x y) with
                    | true => eqb_hexs xs ys
                    | false => false
                    end
end.

