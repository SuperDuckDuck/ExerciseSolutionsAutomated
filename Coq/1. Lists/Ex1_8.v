Require Import List.
Import ListNotations.
Require Import Coq.Arith.Mult.
Require Import Omega.
Require Import Coq.Arith.PeanoNat.

Fixpoint ListSum (ls : list nat): nat :=
match ls with
| [] => 0
| x::xs => x + ListSum xs
end.

Eval compute in seq 2 1.

Lemma seq_top_extract (n : nat) : forall (m : nat), seq m (S n) = seq m n  ++ [m + n]. 
Proof.
  induction n.
  + destruct m.
    - reflexivity.
    - simpl. rewrite plus_0_r. reflexivity.
  + intro. simpl seq at 2. 
    rewrite <- app_comm_cons. rewrite <- plus_Snm_nSm. rewrite <- IHn. reflexivity.
Qed.

Lemma list_sum_app (xs ys : list nat): ListSum (xs ++ ys) = ListSum xs + ListSum ys.
Proof.
  induction xs.
  + reflexivity.
  + simpl. rewrite IHxs. intuition.
Qed.

Theorem gauss_sum (n : nat) : 2 * ListSum (seq 0 (n + 1)) = n * (n + 1).
Proof. 
  induction n.
  + reflexivity.
  + rewrite plus_Sn_m. rewrite seq_top_extract. rewrite list_sum_app.
    simpl ListSum at 2. rewrite mult_plus_distr_l. rewrite IHn. simpl.
    rewrite <- plus_Sn_m at 1. rewrite <- plus_Sn_m. rewrite mult_plus_distr_l.
    rewrite Nat.mul_1_r. rewrite mult_plus_distr_l. repeat rewrite plus_0_r.
    assert (S n = 1 + n).
    - auto.
    - rewrite H. rewrite mult_plus_distr_l. omega.
Qed.

Theorem list_sum_replicate (n a : nat) :  ListSum (repeat a n) = n * a.
Proof.
  induction n.
  + reflexivity.
  + simpl. auto.
Qed.

Fixpoint ListSumTAux (ls : list nat) (acc : nat) : nat :=
match ls with 
| [] => acc
| x::xs => ListSumTAux xs (acc + x)
end.

Definition ListSumT (ls : list nat) : nat := ListSumTAux ls 0.

Lemma ListSumTAdd (ls : list nat) : 
  forall (n : nat) , ListSumTAux ls n = n + ListSumTAux ls 0.
Proof.
  induction ls.
  + auto.
  + intro. simpl. rewrite IHls.  rewrite (IHls a). intuition.
Qed.

Theorem ListSumEqListSumT (ls : list nat) : 
  ListSum ls = ListSumT ls.
Proof.
  induction ls.
  + reflexivity.
  + simpl. unfold ListSumT. simpl. rewrite ListSumTAdd. rewrite IHls. reflexivity.
Qed.
