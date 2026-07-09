From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From lithium Require Export base.
From lithium Require Import simpl_classes pure_definitions.

(** This file provides the instances for the simplification
infrastructure for sideconditions and quantifers. *)

(** * SimplExist *)
Global Instance simpl_exist_unit Σ : @SimplExist Σ unit (λ P, P tt).
Proof. iIntros (?) "?". iExists _. iFrame. Qed.
Lemma simpl_exist_prod Σ A B : @SimplExist Σ (A * B) (λ P, ∃ x y, P (x, y))%I.
Proof. iIntros (?) "[%[% ?]]". iExists _. iFrame. Qed.
(* We only want syntactic products. *)
Global Hint Extern 2 (SimplExist (_ * _) _) =>
   (notypeclasses refine (simpl_exist_prod _ _ _)) : typeclass_instances.
Global Instance simpl_exist_sigT Σ A f : @SimplExist Σ (@sigT A f) (λ P, ∃ x y, P (existT x y))%I.
Proof. iIntros (?) "[%[% ?]]". iExists _. iFrame. Qed.
Global Instance simpl_exist_TCForall2 Σ A B (l1 : list A) (l2 : list B) P x : @SimplExist Σ (TCForall2 P l1 l2) (λ P, P x).
Proof. iIntros (?) "?". iExists _. iFrame. Qed.
Lemma simpl_exist_eq Σ A (x : A) : @SimplExist Σ (x = x) (λ P, P eq_refl).
Proof. iIntros (?) "?". iExists _. iFrame. Qed.
(* We only want syntactic equalities. *)
Global Hint Extern 2 (SimplExist (_ = _) _) =>
   (notypeclasses refine (simpl_exist_eq _ _ _)) : typeclass_instances.
Lemma simpl_exist_type Σ A : @SimplExist Σ Type (λ P, P A)%I.
Proof. iIntros (?) "?". iExists _. iFrame. Qed.
(* We only want syntactic Type. The [shelve] shelves the evar created
for the Type, which is necessary to make TC search succeed. *)
Global Hint Extern 2 (SimplExist Type _) =>
   (notypeclasses refine (simpl_exist_type _ _); shelve) : typeclass_instances.


(** * SimplImpl and SimplAnd *)
Local Open Scope Z_scope.

Global Instance simpl_or_false1 P1 P2 `{!CanSolve (¬ P2)}:
  SimplBoth (P1 ∨ P2) (P1).
Proof. unfold CanSolve in *. constructor; naive_solver. Qed.
Global Instance simpl_or_false2 P1 P2 `{!CanSolve (¬ P1)}:
  SimplBoth (P1 ∨ P2) (P2).
Proof. unfold CanSolve in *. constructor; naive_solver. Qed.

Global Instance simpl_double_neg_elim_dec P `{!Decision P} :
  SimplBoth (¬ ¬ P) P.
Proof. constructor. destruct (decide P); naive_solver. Qed.

Global Instance simpl_eq_pair_l A B (x : A) (y : B) (xy : A * B):
  SimplAnd ((x, y) = xy) (x = xy.1 ∧ y = xy.2).
Proof. destruct xy; constructor; naive_solver. Qed.

Global Instance simpl_eq_pair_r A B (xy : A * B) (x : A) (y : B):
  SimplAnd (xy = (x, y)) (xy.1 = x ∧ xy.2 = y).
Proof. destruct xy; constructor; naive_solver. Qed.

Global Instance simpl_to_cons_None A (l : list A) :
  SimplBoth (maybe2 cons l = None) (l = nil).
Proof. constructor. destruct l; naive_solver. Qed.
Definition simpl_to_cons_None_sym A l :=
  simpl_both_sym (=) (simpl_to_cons_None A l).
Global Existing Instance simpl_to_cons_None_sym | 5.

Global Instance simpl_to_cons_Some A (l : list A) x :
  SimplBoth (maybe2 cons l = Some x) (l = x.1 :: x.2).
Proof. split; destruct l, x; naive_solver. Qed.
Definition simpl_to_cons_Some_sym A l x :=
  simpl_both_sym (=) (simpl_to_cons_Some A l x).
Global Existing Instance simpl_to_cons_Some_sym | 5.

Global Instance simpl_ex_neq_nil A (l : list A) `{!IsEx l} :
  SimplBoth (l ≠ []) (∃ x l', l = x :: l').
Proof. split; destruct l; naive_solver. Qed.

Global Instance simpl_gt_0_neg n : SimplBoth (¬ (0 < n))%nat (n = 0%nat).
Proof. split; destruct n; naive_solver lia. Qed.

(* We want to do this for hyps (it allows simplification to take
place), but not in the goal (as it might lead to evars which we cannot
instantiate) *)
Global Instance simpl_gt_0_impl n : SimplImpl (0 < n)%nat (∃ n', n = S n').
Proof. split; destruct n; naive_solver lia. Qed.
Global Instance simpl_gt_0_and n : SimplBoth (0 < S n)%nat True.
Proof. split; naive_solver lia. Qed.

Global Instance simpl_bool_decide_true P `{!Decision P} :
  SimplBoth (bool_decide P = true) P.
Proof. split; case_bool_decide; naive_solver. Qed.
Definition simpl_bool_decide_true_sym P `{!Decision P} :=
  simpl_both_sym (=) (simpl_bool_decide_true P).
Global Existing Instance simpl_bool_decide_true_sym | 5.

Global Instance simpl_bool_decide_false P `{!Decision P} :
  SimplBoth (bool_decide P =  false) (¬P).
Proof. split; case_bool_decide; naive_solver. Qed.
Definition simpl_bool_decide_false_sym P `{!Decision P} :=
  simpl_both_sym (=) (simpl_bool_decide_false P).
Global Existing Instance simpl_bool_decide_false_sym | 5.

Global Instance simpl_bool_decide_eq P1 P2 `{!Decision P1} `{!Decision P2} :
  SimplBoth (bool_decide P1 = bool_decide P2) (P1 ↔ P2).
Proof. split; repeat case_bool_decide; naive_solver. Qed.

Global Instance simpl_if_bool_decide_true P x y `{!Decision P} `{!CanSolve P} :
  SimplBoth (if bool_decide P then x else y) x.
Proof. unfold CanSolve in *. by rewrite bool_decide_true. Qed.
Global Instance simpl_if_bool_decide_false P x y `{!Decision P} `{!CanSolve (¬ P)} :
  SimplBoth (if bool_decide P then x else y) y.
Proof. unfold CanSolve in *. by rewrite bool_decide_false. Qed.

Global Instance simpl_Is_true_true b : SimplBoth (Is_true b) (b = true).
Proof. split; destruct b; naive_solver. Qed.
Global Instance simpl_Is_true_false b : SimplBoth (¬ Is_true b) (b = false).
Proof. split; destruct b; naive_solver. Qed.

Global Instance simpl_negb_true b:
  SimplBoth (negb b = true) (b = false).
Proof. destruct b; done. Qed.
Definition simpl_negb_true_sym b :=
  simpl_both_sym (=) (simpl_negb_true b).
Global Existing Instance simpl_negb_true_sym | 5.
Global Instance simpl_negb_false b:
  SimplBoth (negb b = false) (b = true).
Proof. destruct b; done. Qed.
Definition simpl_negb_false_sym b :=
  simpl_both_sym (=) (simpl_negb_false b).
Global Existing Instance simpl_negb_false_sym | 5.

Global Instance simpl_eqb_true b1 b2:
  SimplBoth (eqb b1 b2 = true) (b1 = b2).
Proof. destruct b1, b2; done. Qed.
Definition simpl_eqb_true_sym b1 b2 :=
  simpl_both_sym (=) (simpl_eqb_true b1 b2).
Global Existing Instance simpl_eqb_true_sym | 5.
Global Instance simpl_eqb_false b1 b2:
  SimplBoth (eqb b1 b2 = false) (b1 = negb b2).
Proof. destruct b1, b2; done. Qed.
Definition simpl_eqb_false_sym b1 b2 :=
  simpl_both_sym (=) (simpl_eqb_false b1 b2).
Global Existing Instance simpl_eqb_false_sym | 5.

Global Instance simpl_min_glb_nat n1 n2 m :
  SimplBoth (m ≤ n1 `min` n2)%nat (m ≤ n1 ∧ m ≤ n2)%nat.
Proof. constructor. lia. Qed.
Global Instance simpl_min_glb n1 n2 m :
  SimplBoth (m ≤ n1 `min` n2) (m ≤ n1 ∧ m ≤ n2).
Proof. constructor. lia. Qed.
Global Instance simpl_max_glb_nat n1 n2 m :
  SimplBoth (n1 `max` n2 ≤ m)%nat (n1 ≤ m ∧ n2 ≤ m)%nat.
Proof. constructor. lia. Qed.
Global Instance simpl_max_glb n1 n2 m :
  SimplBoth (n1 `max` n2 ≤ m) (n1 ≤ m ∧ n2 ≤ m).
Proof. constructor. lia. Qed.

Global Instance simpl_gt_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} :
  SimplBoth (n1 > n2 * n1) (n2 = 0%nat).
Proof. unfold CanSolve in *; split; destruct n2; naive_solver lia. Qed.
Global Instance simpl_ge_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} :
  SimplBoth (n1 >= n2 * n1) (n2 = 0 ∨ n2 = 1)%nat.
Proof. unfold CanSolve in *; split; destruct n2 as [|[]]; naive_solver lia. Qed.
Global Instance simpl_ge_both_Z (n1 n2 : Z) `{!CanSolve (0 < n1)} :
  SimplBoth (n1 >= n2 * n1) (1 >= n2).
Proof. unfold CanSolve in *; split; nia. Qed.
Global Instance simpl_neq_ge_both_Z (n1 n2 : Z) `{!CanSolve (0 < n1)} :
  SimplBoth (¬ (n1 >= n2 * n1)) (n2 > 1).
Proof. unfold CanSolve in *; split; nia. Qed.
Global Instance simpl_gt_neq_0_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} :
  SimplBoth (¬ n1 > n2 * n1) (n2 > 0)%nat.
Proof. unfold CanSolve in *; split; destruct n2; try naive_solver lia. Qed.
Global Instance simpl_ge_neq_0_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} :
  SimplBoth (¬ n1 >= n2 * n1) (n2 > 1)%nat.
Proof. unfold CanSolve in *; split; destruct n2 as [|[]]; naive_solver lia. Qed.
Global Instance simpl_mult_0 n m :
  SimplBoth (n * m = 0) (n = 0 ∨ m = 0).
Proof. split; destruct n, m; naive_solver lia. Qed.
Definition simpl_mult_0_sym n m :=
  simpl_both_sym (=) (simpl_mult_0 n m).
Global Existing Instance simpl_mult_0_sym | 5.

Global Instance simpl_nat_le_0 (n : nat) :
  SimplBoth (n ≤ 0)%nat (n = 0)%nat.
Proof. split; lia. Qed.

Global Instance simpl_mult_neq_0 n m :
  SimplBoth (n * m ≠ 0) (n ≠ 0 ∧ m ≠ 0).
Proof. split; destruct n, m; naive_solver lia. Qed.
Global Instance simpl_mult_le z1 z2:
  SimplBoth (0 ≤ z1 * z2) ((0 ≤ z1 ∧ 0 ≤ z2) ∨ (z1 ≤ 0 ∧ z2 ≤ 0)).
Proof. split; destruct z1, z2; naive_solver lia. Qed.

Global Instance simpl_divides_impl a b:
  SimplImpl (a | b) (∃ n, b = n * a).
Proof. rewrite /Z.divide. split; naive_solver. Qed.

Global Instance simpl_divides_and a b `{!CanSolve (a ≠ 0 ∧ b `mod` a = 0)}:
  SimplAnd (a | b) (True).
Proof. revert select (CanSolve _) => -[?]. rewrite Z.mod_divide //. Qed.
Global Instance simpl_divides_and_mul_r a b:
  SimplAnd (a | b * a) (True).
Proof. rewrite /Z.divide. split; naive_solver. Qed.

Global Instance simpl_nat_divides_and_mul_r a b:
  SimplAnd (a | b * a)%nat (True).
Proof. rewrite /divide. split; naive_solver. Qed.

Global Instance simpl_is_power_of_two_mult n1 n2 :
  SimplBoth (is_power_of_two (n1 * n2)) (is_power_of_two n1 ∧ is_power_of_two n2).
Proof. constructor. by apply is_power_of_two_mult. Qed.

(* TODO: This instance is quite specific and for mpool. *)
Global Instance simpl_forall_eq_plus n x:
  SimplBoth (x = n + x)%nat (n = 0)%nat.
Proof. split; naive_solver lia. Qed.

Global Instance simpl_n_mul_m_minus n m k `{!CanSolve (m ≠ 0)} :
  SimplBoth (n * m - m = k * m) (n-1 = k).
Proof.
  unfold CanSolve in *. constructor. split; last naive_solver lia.
  move => ?. apply (Z.mul_cancel_r _ _ m) => //. lia.
Qed.
Definition simpl_n_mul_m_minus_sym n m k `{!CanSolve (m ≠ 0)} :=
  simpl_both_sym (=) (simpl_n_mul_m_minus n m k).
Global Existing Instance simpl_n_mul_m_minus_sym | 5.
(* TODO: unify these two instances *)
Global Instance simpl_n_mul_m_minus_nat n m k `{!CanSolve (m ≠ 0)%nat} :
  SimplBoth (n * m - m = k * m)%nat (n-1 = k)%nat.
Proof.
  unfold CanSolve in *. constructor. split.
  - move => ?. apply (Nat.mul_cancel_r _ _ m) => //. rewrite Nat.mul_sub_distr_r. lia.
  - move => <-. rewrite Nat.mul_sub_distr_r. lia.
Qed.
Definition simpl_n_mul_m_minus_nat_sym n m k `{!CanSolve (m ≠ 0)%nat} :=
  simpl_both_sym (=) (simpl_n_mul_m_minus_nat n m k).
Global Existing Instance simpl_n_mul_m_minus_nat_sym | 5.
Global Instance simpl_cancel_mult_nat n1 n2 m `{!CanSolve (m ≠ 0)%nat}:
  SimplBoth (n1 * m = n2 * m)%nat (n1 = n2)%nat.
Proof. constructor. unfold CanSolve in *. by rewrite Nat.mul_cancel_r. Qed.
Global Instance simpl_cancel_mult_nat_1 n m `{!CanSolve (m ≠ 0)%nat}:
  SimplBoth (n * m = m)%nat (n = 1)%nat.
Proof. constructor. unfold CanSolve in *. nia. Qed.
Definition simpl_cancel_mult_nat_1_sym n m `{!CanSolve (m ≠ 0)%nat} :=
  simpl_both_sym (=) (simpl_cancel_mult_nat_1 n m).
Global Existing Instance simpl_cancel_mult_nat_1_sym | 5.
Global Instance simpl_cancel_mult_le_nat n1 n2 m `{!CanSolve (0 < m)%nat}:
  SimplBoth (n1 * m ≤ n2 * m)%nat (n1 ≤ n2)%nat.
Proof. constructor. unfold CanSolve in *. nia. Qed.
Global Instance simpl_cancel_mult_le n1 n2 m `{!CanSolve (0 < m)}:
  SimplBoth (n1 * m ≤ n2 * m) (n1 ≤ n2).
Proof. constructor. unfold CanSolve in *. by rewrite -Z.mul_le_mono_pos_r. Qed.
Global Instance simpl_cancel_mult_eq n1 n2 m `{!CanSolve (0 ≠ m)}:
  SimplBoth (n1 * m = n2 * m) (n1 = n2).
Proof. constructor. unfold CanSolve in *. by rewrite Z.mul_cancel_r. Qed.
Global Instance simpl_cancel_mult_neq n1 n2 m `{!CanSolve (0 ≠ m)}:
  SimplBoth (n1 * m ≠ n2 * m) (n1 ≠ n2).
Proof. constructor. unfold CanSolve in *. split; by rewrite Z.mul_cancel_r. Qed.
Global Instance simpl_cancel_mult_nat_Z n1 n2 m `{!CanSolve (m ≠ 0)%nat}:
  SimplBoth (n1 * m = (n2 * m)%nat) (n1 = n2).
Proof. constructor. unfold CanSolve in *. rewrite Nat2Z.inj_mul Z.mul_cancel_r; lia. Qed.
Definition simpl_cancel_mult_nat_Z_sym n1 n2 m `{!CanSolve (m ≠ 0)%nat} :=
  simpl_both_sym (=) (simpl_cancel_mult_nat_Z n1 n2 m).
Global Existing Instance simpl_cancel_mult_nat_Z_sym | 5.
Global Instance simpl_Zsub_to_nat (n m : nat) `{!CanSolve (n > 0)} :
  SimplBoth (n - 1 = m) ((n-1) = m)%nat.
Proof. constructor. unfold CanSolve in *. split; naive_solver lia. Qed.
Definition simpl_Zsub_to_nat_sym (n m : nat) `{!CanSolve (n > 0)} :=
  simpl_both_sym (=) (simpl_Zsub_to_nat n m).
Global Existing Instance simpl_Zsub_to_nat_sym | 5.
Global Instance simpl_Zadd_to_nat (n m : nat) :
  SimplBoth (n + 1 = m) ((n+1) = m)%nat.
Proof. unfold CanSolve in *. split; naive_solver lia. Qed.
Definition simpl_Zadd_to_nat_sym n m :=
  simpl_both_sym (=) (simpl_Zadd_to_nat n m).
Global Existing Instance simpl_Zadd_to_nat_sym | 5.
Global Instance simpl_n_add_sub_n_nat n m k :
  SimplBoth (n + m - n = k)%nat (m = k)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_n_add_sub_n_nat_sym n m k :=
  simpl_both_sym (=) (simpl_n_add_sub_n_nat n m k).
Global Existing Instance simpl_n_add_sub_n_nat_sym | 5.
Global Instance simpl_nat_sub_0 (n m : nat) :
  SimplBoth (m - 0 = n)%nat (n = m).
Proof. split; naive_solver lia. Qed.
Definition simpl_nat_sub_0_sym n m :=
  simpl_both_sym (=) (simpl_nat_sub_0 n m).
Global Existing Instance simpl_nat_sub_0_sym | 5.
(* TODO: add a more general impl? *)
Global Instance simpl_eq_0 (n : nat) :
  SimplBoth (n =@{Z} 0) (n = 0)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_0_sym n :=
  simpl_both_sym (=) (simpl_eq_0 n).
Global Existing Instance simpl_eq_0_sym | 5.
Global Instance simpl_eq_1 (n : nat) :
  SimplBoth (n =@{Z} 1) (n = 1)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_1_sym n :=
  simpl_both_sym (=) (simpl_eq_0 n).
Global Existing Instance simpl_eq_1_sym | 5.
Global Instance simpl_eq_2 (n : nat) :
  SimplBoth (n =@{Z} 2) (n = 2)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_2_sym n :=
  simpl_both_sym (=) (simpl_eq_2 n).
Global Existing Instance simpl_eq_2_sym | 5.
Global Instance simpl_eq_3 (n : nat) :
  SimplBoth (n =@{Z} 3) (n = 3)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_3_sym n :=
  simpl_both_sym (=) (simpl_eq_3 n).
Global Existing Instance simpl_eq_3_sym | 5.
Global Instance simpl_eq_4 (n : nat) :
  SimplBoth (n =@{Z} 4) (n = 4)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_4_sym n :=
  simpl_both_sym (=) (simpl_eq_4 n).
Global Existing Instance simpl_eq_4_sym | 5.
Global Instance simpl_eq_5 (n : nat) :
  SimplBoth (n =@{Z} 5) (n = 5)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_5_sym n :=
  simpl_both_sym (=) (simpl_eq_5 n).
Global Existing Instance simpl_eq_5_sym | 5.
Global Instance simpl_eq_6 (n : nat) :
  SimplBoth (n =@{Z} 6) (n = 6)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_6_sym n :=
  simpl_both_sym (=) (simpl_eq_6 n).
Global Existing Instance simpl_eq_6_sym | 5.
Global Instance simpl_eq_7 (n : nat) :
  SimplBoth (n =@{Z} 7) (n = 7)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_7_sym n :=
  simpl_both_sym (=) (simpl_eq_7 n).
Global Existing Instance simpl_eq_7_sym | 5.
Global Instance simpl_eq_8 (n : nat) :
  SimplBoth (n =@{Z} 8) (n = 8)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_8_sym n :=
  simpl_both_sym (=) (simpl_eq_8 n).
Global Existing Instance simpl_eq_8_sym | 5.
Global Instance simpl_eq_9 (n : nat) :
  SimplBoth (n =@{Z} 9) (n = 9)%nat.
Proof. split; naive_solver lia. Qed.
Definition simpl_eq_9_sym n :=
  simpl_both_sym (=) (simpl_eq_9 n).
Global Existing Instance simpl_eq_9_sym | 5.

Global Instance simpl_eq_Ztonat (n m : nat) :
  SimplBoth (n =@{Z} m) (n = m).
Proof. split; naive_solver lia. Qed.

Global Instance simpl_bool_to_Z_0 (b : bool) :
  SimplBoth (0 = bool_to_Z b) (b = false).
Proof. split; destruct b; naive_solver. Qed.
Definition simpl_bool_to_Z_0_sym b :=
  simpl_both_sym (=) (simpl_bool_to_Z_0 b).
Global Existing Instance simpl_bool_to_Z_0_sym | 5.
Global Instance simpl_bool_to_Z_1 (b : bool) :
  SimplBoth (1 = bool_to_Z b) (b = true).
Proof. split; destruct b; naive_solver. Qed.
Definition simpl_bool_to_Z_1_sym b :=
  simpl_both_sym (=) (simpl_bool_to_Z_1 b).
Global Existing Instance simpl_bool_to_Z_1_sym | 5.

Global Instance simpl_bool_to_Z_nonzero b :
  SimplBoth (bool_to_Z b ≠ 0) (b = true).
Proof. by destruct b. Qed.
Definition simpl_bool_to_Z_nonzero_sym b :=
  simpl_both_sym (≠) (simpl_bool_to_Z_nonzero b).
Global Existing Instance simpl_bool_to_Z_nonzero_sym | 5.

Global Instance simpl_add_eq_0 n m:
  SimplBoth (n + m = 0)%nat (n = 0%nat ∧ m = 0%nat).
Proof. split; naive_solver lia. Qed.
Definition simpl_add_eq_0_sym n m :=
  simpl_both_sym (=) (simpl_add_eq_0 n m).
Global Existing Instance simpl_add_eq_0_sym | 5.

Global Instance simpl_and_S n m `{!ContainsEx n}:
  SimplAnd (S n = m) ((m > 0)%nat ∧ n = pred m).
Proof. split; destruct n; naive_solver lia. Qed.
Definition simpl_and_S_sym n m `{!ContainsEx n} :=
  simpl_and_impl_sym (=) (simpl_and_S n m).
Global Existing Instance simpl_and_S_sym | 5.

Global Instance simpl_and_Z_of_nat n m `{!ContainsEx n}:
  SimplAnd (Z.of_nat n = m) (0 ≤ m ∧ n = Z.to_nat m).
Proof. unfold CanSolve in *. split; naive_solver lia. Qed.
Definition simpl_and_Z_of_nat_sym n m `{!ContainsEx n} :=
  simpl_and_impl_sym (=) (simpl_and_Z_of_nat n m).
Global Existing Instance simpl_and_Z_of_nat_sym | 5.

Global Instance simpl_both_shiftl_nonneg z n:
  SimplBoth (0 ≤ z ≪ n) (0 ≤ z).
Proof. split; by rewrite Z.shiftl_nonneg. Qed.


Global Instance simpl_in_nil {A} (x : A):
  SimplBoth (x ∈ []) False.
Proof. split; set_solver. Qed.
Global Instance simpl_not_in_nil {A} (x : A):
  SimplBoth (x ∉ []) True.
Proof. split; set_solver. Qed.
Global Instance simpl_in_cons {A} (x : A) y ys:
  SimplBoth (x ∈ y :: ys) (x = y ∨ x ∈ ys).
Proof. split; set_solver. Qed.
Global Instance simpl_not_in_cons {A} (x : A) y ys:
  SimplBoth (x ∉ y :: ys) (x ≠ y ∧ x ∉ ys).
Proof. split; set_solver. Qed.

Global Instance simpl_both_forall_nil {A} (f : A → Prop):
  SimplBoth (Forall f []) (True).
Proof. split; naive_solver. Qed.
Global Instance simpl_both_forall_cons {A} f (x : A) xs:
  SimplBoth (Forall f (x::xs)) (f x ∧ Forall f xs).
Proof. constructor. split; [ by move => /(Forall_cons_1 _ _) | naive_solver]. Qed.

Global Instance list_Forall_simpl_and {A} (P : nat → A → Prop) xs :
  SimplAnd (list_Forall P xs) (∀ i x, xs !! i = Some x → P i x).
Proof. done. Qed.

Global Instance simpl_both_forall2_nil {A B} (f : A → B → Prop):
  SimplBoth (Forall2 f [] []) (True).
Proof. constructor. split; [by move => /(Forall2_nil_inv_l _ _)| naive_solver]. Qed.
Global Instance simpl_both_forall2_cons {A B} f (x : A) (y : B) xs ys:
  SimplBoth (Forall2 f (x::xs)(y::ys)) (f x y ∧ Forall2 f xs ys).
Proof. constructor. split; [by move => /(Forall2_cons _ _ _ _)|naive_solver]. Qed.

Global Instance simpl_length_0 {A} (l : list A):
  SimplBoth (length l = 0%nat) (l = []).
Proof. split; by destruct l. Qed.
Definition simpl_length_0_sym A l :=
  simpl_both_sym (=) (@simpl_length_0 A l).
Global Existing Instance simpl_length_0_sym | 5.

Global Instance simpl_length_S {A} (l : list A) (n : nat):
  SimplAnd (length l = S n) (∃ hd tl, l = hd :: tl ∧ length tl = n).
Proof.
  constructor. split.
  - move => Hlen. destruct l as [|hd tl] => //.
    eexists hd, tl. by inversion Hlen.
  - move => [hd [tl [-> <-]]] //.
Qed.
Definition simpl_length_S_sym A l n :=
  simpl_and_impl_sym (=) (@simpl_length_S A l n).
Global Existing Instance simpl_length_S_sym | 5.

Global Instance simpl_length_ex_add {A} (n m : nat) (p : list A)
  `{!ContainsEx p} `{!CanSolve (m ≤ n)%nat} :
  SimplAnd (n = length p + m)%nat ((n - m)%nat = length p).
Proof.
  constructor. unfold CanSolve in *. split.
  - move => ->. lia.
  - move => Heq. lia.
Qed.
Definition simpl_length_ex_add_sym A n m p `{!ContainsEx p} `{!CanSolve (m ≤ n)%nat} :=
  simpl_and_impl_sym (=) (@simpl_length_ex_add A n m p _ _).
Global Existing Instance simpl_length_ex_add_sym | 5.

Global Instance simpl_insert_list_subequiv {A} (l1 l2 : list A) j x1 `{!CanSolve (j < length l1)%nat} :
  SimplBoth (<[j:=x1]>l1 = l2) (list_subequiv [j] l1 l2 ∧ l2 !! j = Some x1).
Proof. unfold CanSolve in *. split; rewrite list_insert_subequiv //; naive_solver. Qed.
Definition simpl_insert_list_subequiv_sym A (l1 l2 : list A) j x1 `{!CanSolve (j < length l1)%nat} :=
  simpl_both_sym (=) (simpl_insert_list_subequiv l1 l2 j x1).
Global Existing Instance simpl_insert_list_subequiv_sym | 5.

Global Instance simpl_insert_subequiv {A} (l1 l2 : list A) j x1 ig `{!CanSolve (j < length l1)%nat}:
  SimplBoth (list_subequiv ig (<[j:=x1]>l1) l2)
    (if bool_decide (j ∈ ig) then list_subequiv ig l1 l2 else
       list_subequiv (j :: ig) l1 l2 ∧ l2 !! j = Some x1).
Proof.
  unfold CanSolve in *. constructor.
  case_bool_decide; [rewrite list_subequiv_insert_in_l | rewrite list_subequiv_insert_ne_l ]; naive_solver.
Qed.
Definition simpl_insert_subequiv_sym {A} (l1 l2 : list A) j x1 ig `{!CanSolve (j < length l1)%nat} :=
  simpl_both_sym (list_subequiv ig) (simpl_insert_subequiv l1 l2 j x1 ig).
Global Existing Instance simpl_insert_subequiv_sym | 5.

Global Instance simpl_ig_nil_subequiv {A} (l1 l2 : list A) :
  SimplBoth (list_subequiv [] l1 l2) (l1 = l2).
Proof.
  constructor. split; [|naive_solver] => Hl. apply: list_eq => i.
  move: (Hl i) => [? ?]. set_solver.
Qed.

Global Instance simpl_nil_subequiv {A} (l : list A) ig :
  SimplBoth (list_subequiv ig [] l) (l = []).
Proof. by split; rewrite list_subequiv_nil_l. Qed.
Definition simpl_nil_subequiv_sym {A} (l : list A) ig :=
  simpl_both_sym (list_subequiv ig) (simpl_nil_subequiv l ig).
Global Existing Instance simpl_nil_subequiv_sym | 5.

Global Instance simpl_app_r_subequiv {A} (l1 l2 suffix : list A) ig :
  SimplBoth (list_subequiv ig (l1 ++ suffix) (l2 ++ suffix))
    (list_subequiv ig l1 l2).
Proof. constructor. apply: list_subequiv_app_r. Qed.
Definition simpl_app_r_subequiv_sym {A} (l1 l2 suffix : list A) ig :=
  simpl_both_sym (list_subequiv ig) (simpl_app_r_subequiv l1 l2 suffix ig).
Global Existing Instance simpl_app_r_subequiv_sym | 5.

(* The other direction requires `{!Inj (=) (=) f}, but we cannot prove
it if f goes into type. Thus we use the AssumeInj typeclass such that
the user can mark functions which are morally injective, but one
cannot prove it. *)
Global Instance simpl_fmap_fmap_subequiv_Unsafe {A B} (l1 l2 : list A) ig (f : A → B) `{!AssumeInj (=) (=) f}:
  SimplAndUnsafe (list_subequiv ig (f <$> l1) (f <$> l2)) (list_subequiv ig l1 l2).
Proof. constructor. move => ? Hs. by apply: list_subequiv_fmap. Qed.

(* The other direction might not hold if ig contains indices which are
out of bounds, but we don't care about that. *)
Global Instance simpl_subequiv_ex {A} (l1 l2 : list A) ig `{!IsEx l2}:
  SimplAndUnsafe (list_subequiv ig l1 l2) (
    foldr (λ i f, (λ l', ∃ x, f (<[i:=x]> l'))) (λ l', l2 = l') ig l1).
Proof.
  (* TODO: add a lemma for list_subequiv such that this unfolding is not necessary anymore. *)
  constructor. unfold_opaque @list_subequiv.
  clear IsEx0. elim: ig l1 l2.
  - move => ??/=. move => ?. naive_solver.
  - move => i ig IH l1 l2/= [x /IH Hi ] i'.
    move: (Hi i') => [<- Hlookup]. rewrite length_insert. split => //.
    move => Hi'. rewrite -Hlookup ?list_lookup_insert_ne; set_solver.
Qed.

Global Instance simpl_fmap_nil {A B} (l : list A) (f : A → B) :
  SimplBoth (f <$> l = []) (l = []).
Proof. split; destruct l; naive_solver. Qed.
Definition simpl_fmap_nil_sym {A B} (l : list A) (f : A → B) :=
  simpl_both_sym (=) (simpl_fmap_nil l f).
Global Existing Instance simpl_fmap_nil_sym | 5.
Global Instance simpl_fmap_cons_and {A B} x (l : list A) l2 (f : A → B):
  SimplAnd (f <$> l = x :: l2) (∃ x' l2', l = x' :: l2' ∧ f x' = x ∧ f <$> l2' = l2).
Proof. constructor. split; last naive_solver. intros ?%fmap_cons_inv. naive_solver. Qed.
Definition simpl_fmap_cons_and_sym {A B} x (l : list A) l2 (f : A → B) :=
  simpl_and_impl_sym (=) (simpl_fmap_cons_and x l l2 f).
Global Existing Instance simpl_fmap_cons_and_sym | 5.
Global Instance simpl_fmap_cons_impl {A B} x (l : list A) l2 (f : A → B):
  SimplImpl (f <$> l = x :: l2) (∃ x' l2', l = x' :: l2' ∧ f x' = x ∧ f <$> l2' = l2).
Proof. constructor. split; last naive_solver. intros ?%fmap_cons_inv. naive_solver. Qed.
Definition simpl_fmap_cons_impl_sym {A B} x (l : list A) l2 (f : A → B) :=
  simpl_and_impl_sym (=) (simpl_fmap_cons_impl x l l2 f).
Global Existing Instance simpl_fmap_cons_impl_sym | 5.

Global Instance simpl_fmap_app_and {A B} (l : list A) l1 l2 (f : A → B) `{!AssumeInj (=) (=) f}:
   SimplAndUnsafe (f <$> l = (f <$> l1) ++ (f <$> l2)) (l = l1 ++ l2).
Proof.
  constructor => ->. by rewrite fmap_app.
Qed.
Definition simpl_fmap_app_and_sym {A B} (l : list A) l1 l2 (f : A → B) `{!AssumeInj (=) (=) f} :=
  simpl_and_impl_sym (=) (simpl_fmap_app_and l l1 l2 f).
Global Existing Instance simpl_fmap_app_and_sym | 5.

Global Instance simpl_fmap_assume_inj_Unsafe {A B} (l1 l2 : list A) (f : A → B) `{!AssumeInj (=) (=) f}:
  SimplAndUnsafe (f <$> l1 = f <$> l2) (l1 = l2).
Proof. constructor. move => ->. naive_solver. Qed.

Global Instance simpl_replicate_app_and {A} (l1 l2 : list A) x n:
  SimplAnd (replicate n x = l1 ++ l2) (∃ n', l1 = replicate n' x ∧ l2 = replicate (n - n') x ∧ (n' ≤ n)%nat).
Proof.
  constructor. split; last first.
  - move => [n'[?[??]]]; subst.
    have ->: (n = n' + (n - n'))%nat by lia. rewrite replicate_add. do 2 f_equal. lia.
  - move => Hr.
    have Hn: (n = length l1 + length l2)%nat by rewrite -(length_replicate n x) -length_app Hr.
    move: Hr. rewrite Hn replicate_add => /app_inj_1[|<- <-]. 1: by rewrite length_replicate.
    exists (length l1). repeat split => //.
    + rewrite !length_replicate. f_equal. lia.
    + rewrite !length_replicate. lia.
Qed.
Definition simpl_replicate_app_and_sym {A} (l1 l2 : list A) x n :=
  simpl_and_impl_sym (=) (simpl_replicate_app_and l1 l2 x n).
Global Existing Instance simpl_replicate_app_and_sym | 5.

Global Instance simpl_replicate_eq_nil {A} (x : A) n :
  SimplBoth (replicate n x = []) (n = 0%nat).
Proof. by destruct n. Qed.
Definition simpl_replicate_eq_nil_sym {A} (x : A) n :=
  simpl_both_sym (=) (simpl_replicate_eq_nil x n).
Global Existing Instance simpl_replicate_eq_nil_sym | 5.

Global Instance simpl_replicate_cons {A} (l : list A) x x' n:
  SimplBoth (replicate n x = x' :: l) ((n > 0)%nat ∧ x' = x ∧ l = replicate (pred n) x).
Proof. split; destruct n; naive_solver lia. Qed.
Definition simpl_replicate_cons_sym {A} (l : list A) x x' n :=
  simpl_both_sym (=) (simpl_replicate_cons l x x' n).
Global Existing Instance simpl_replicate_cons_sym | 5.

Global Instance simpl_replicate_lookup {A} (x x' : A) n m :
  SimplBoth (replicate n x !! m = Some x') (x' = x ∧ (m < n)%nat).
Proof. constructor. by apply: lookup_replicate. Qed.
Definition simpl_replicate_lookup_sym {A} (x x' : A) n m :=
  simpl_both_sym (=) (simpl_replicate_lookup x x' n m).
Global Existing Instance simpl_replicate_lookup_sym | 5.

Global Instance simpl_replicate_eq {A} (x : A) n n' :
  SimplBoth (replicate n x = replicate n' x) (n = n').
Proof.
  constructor. split; last naive_solver.
  elim: n n'; first by case.
  move => n IH []//= n' []. naive_solver.
Qed.

Global Instance simpl_replicate_elem_of {A} (x x' : A) n :
  SimplBoth (x' ∈ replicate n x) (x' = x ∧ (n ≠ 0)%nat).
Proof. constructor. by set_unfold. Qed.

Global Instance simpl_filter_nil {A} P `{!∀ x, Decision (P x)} (l : list A) :
  SimplBoth (filter P l = []) (∀ x, x ∈ l → ¬ P x).
Proof. constructor. by rewrite filter_nil_inv. Qed.
Definition simpl_filter_nil_sym {A} P `{!∀ x, Decision (P x)} (l : list A) :=
  simpl_both_sym (=) (simpl_filter_nil P l).
Global Existing Instance simpl_filter_nil_sym | 5.

Global Instance simpl_app_r_id {A} (l1 l2 : list A):
  SimplBoth (l2 = l1 ++ l2) (l1 = []).
Proof.
  constructor. split.
  - move => H. assert (length (l1 ++ l2) = length l2) as Hlen by by rewrite -H.
    rewrite length_app in Hlen. assert (length l1 = 0%nat) by lia. by destruct l1.
  - by naive_solver.
Qed.
Definition simpl_app_r_id_sym {A} (l1 l2 : list A) :=
  simpl_both_sym (=) (simpl_app_r_id l1 l2).
Global Existing Instance simpl_app_r_id_sym | 5.

Global Instance simpl_app_l_id {A} (l1 l2 : list A):
  SimplBoth (l1 = l1 ++ l2) (l2 = []).
Proof.
  constructor. split.
  - move => H. assert (length (l1 ++ l2) = length l1) as Hlen by by rewrite -H.
    rewrite length_app in Hlen. assert (length l2 = 0%nat) by lia. by destruct l2.
  - move => ->. by rewrite app_nil_r.
Qed.
Definition simpl_app_l_id_sym {A} (l1 l2 : list A) :=
  simpl_both_sym (=) (simpl_app_l_id l1 l2).
Global Existing Instance simpl_app_l_id_sym | 5.

(* TODO: make something more general *)
Global Instance simpl_cons_app_eq {A} (l1 l2 l3 : list A) x:
  SimplBoth (x :: l1 ++ l2 = l3 ++ l2) (x :: l1 = l3).
Proof. constructor. split; try naive_solver. move => ?. by apply: app_inv_tail. Qed.
Definition simpl_cons_app_eq_sym {A} (l1 l2 l3 : list A) x :=
  simpl_both_sym (=) (simpl_cons_app_eq l1 l2 l3 x).
Global Existing Instance simpl_cons_app_eq_sym | 5.

Global Instance simpl_lookup_app {A} (l1 l2 : list A) i x:
  SimplBoth ((l1 ++ l2) !! i = Some x)
               (if bool_decide (i < length l1)%nat then l1 !! i = Some x else l2 !! (i - length l1)%nat = Some x).
Proof.
  constructor. case_bool_decide.
  - by rewrite lookup_app_l.
  - rewrite lookup_app_r //. lia.
Qed.
Definition simpl_lookup_app_sym {A} (l1 l2 : list A) i x :=
  simpl_both_sym (=) (simpl_lookup_app l1 l2 i x).
Global Existing Instance simpl_lookup_app_sym | 5.

Global Instance simpl_rev_nil {A} (l : list A):
  SimplBoth (rev l = []) (l = []).
Proof.
  constructor. split.
  - move => H. destruct l; first done. simpl in H. by destruct (rev l).
  - move => ->. done.
Qed.
Definition simpl_rev_nil_sym {A} (l : list A) :=
  simpl_both_sym (=) (simpl_rev_nil l).
Global Existing Instance simpl_rev_nil_sym | 5.

Global Instance simpl_lookup_drop {A} (l : list A) n i x :
  SimplBoth (drop n l !! i = Some x) (l !! (n + i)%nat = Some x).
Proof. by rewrite lookup_drop. Qed.
Definition simpl_lookup_drop_sym {A} (l : list A) n i x :=
  simpl_both_sym (=) (simpl_lookup_drop l n i x).
Global Existing Instance simpl_lookup_drop_sym | 5.

Global Instance simpl_fmap_lookup {A B} (l : list A) i (f : A → B) x:
  SimplBoth ((f <$> l) !! i = Some x) (∃ y : A, x = f y ∧ l !! i = Some y).
Proof.
  constructor. split.
  - move => Hf. have := list_lookup_fmap_Some_1 _ _ _ _ Hf. naive_solver.
  - move => [y [-> Hl]]. rewrite list_lookup_fmap Hl. naive_solver.
Qed.
Definition simpl_fmap_lookup_sym {A B} (l : list A) i (f : A → B) x :=
  simpl_both_sym (=) (simpl_fmap_lookup l i f x).
Global Existing Instance simpl_fmap_lookup_sym | 5.
Global Instance simpl_lookup_insert_eq {A} (l : list A) i j x x' `{!CanSolve (i = j)}:
  SimplBoth (<[i := x']> l !! j = Some x) (x = x' ∧ (j < length l)%nat).
Proof.
  constructor. unfold CanSolve in *; subst.
  rewrite list_lookup_insert_Some. naive_solver.
Qed.
Definition simpl_lookup_insert_eq_sym {A} (l : list A) i j x x' `{!CanSolve (i = j)} :=
  simpl_both_sym (=) (simpl_lookup_insert_eq l i j x x').
Global Existing Instance simpl_lookup_insert_eq_sym | 5.
Global Instance simpl_lookup_insert_neq {A} (l : list A) i j x x' `{!CanSolve (i ≠ j)}:
  SimplBoth (<[i := x']> l !! j = Some x) (l !! j = Some x).
Proof.
  constructor. unfold CanSolve in *; subst.
  rewrite list_lookup_insert_Some. naive_solver.
Qed.
Definition simpl_lookup_insert_neq_sym {A} (l : list A) i j x x' `{!CanSolve (i ≠ j)} :=
  simpl_both_sym (=) (simpl_lookup_insert_neq l i j x x').
Global Existing Instance simpl_lookup_insert_neq_sym | 5.

Global Instance simpl_and_lookup_ex {A} (l : list A) (i : nat) v `{!IsEx v} `{Inhabited A}:
  SimplAnd (l !! i = Some v) (i < length l ∧ v = l !!! i) | 30.
Proof.
  constructor. split.
  - move => /list_lookup_alt ?. naive_solver lia.
  - move => -[? ->]. apply: list_lookup_lookup_total_lt. lia.
Qed.
Definition simpl_and_lookup_ex_sym {A} (l : list A) (i : nat) v `{!IsEx v} `{Inhabited A} :=
  simpl_and_impl_sym (=) (simpl_and_lookup_ex l i v).
Global Existing Instance simpl_and_lookup_ex_sym | 30.

Global Instance simpl_and_lookup_lookup_total {A} (l : list A) (i : nat) `{Inhabited A}:
  SimplBoth (l !! i = Some (l !!! i)) (i < length l).
Proof. constructor. rewrite list_lookup_alt. naive_solver lia. Qed.
Definition simpl_and_lookup_lookup_total_sym {A} (l : list A) (i : nat) `{Inhabited A} :=
  simpl_both_sym (=) (simpl_and_lookup_lookup_total l i).
Global Existing Instance simpl_and_lookup_lookup_total_sym | 5.

Global Instance simpl_learn_insert_some_len_impl {A} l i (x : A) :
  (* The false is important here as we learn additional information,
  but we don't want to remove the lookup. *)
  SimplImplUnsafe false (l !! i = Some x) ((i < length l)%nat) | 100.
Proof. constructor. move => ?. by apply: lookup_lt_Some. Qed.

Global Instance simpl_is_Some_unfold {A} (o : option A):
  SimplBoth (is_Some o) (∃ x, o = Some x) | 100.
Proof. split; naive_solver. Qed.

Global Instance simpl_Some {A} o (x x' : A) `{!TCFastDone (o = Some x)}:
  SimplBoth (o = Some x') (x = x') | 1.
Proof. unfold TCFastDone in *; subst. split; naive_solver. Qed.
Definition simpl_Some_sym {A} o (x x' : A) `{!TCFastDone (o = Some x)} :=
  simpl_both_sym (=) (simpl_Some o x x').
Global Existing Instance simpl_Some_sym | 5.

Global Instance simpl_both_fmap_Some A B f (o : option A) (x : B):
  SimplBoth (f <$> o = Some x) (∃ x', o = Some  x' ∧ x = f x').
Proof. constructor. rewrite fmap_Some. naive_solver. Qed.
Definition simpl_both_fmap_Some_sym A B f (o : option A) (x : B) :=
  simpl_both_sym (=) (simpl_both_fmap_Some A B f o x).
Global Existing Instance simpl_both_fmap_Some_sym | 5.

Global Instance simpl_both_option_fmap_None {A B} (f : A → B) (x : option A) :
  SimplBoth (f <$> x = None) (x = None).
Proof. by split; rewrite fmap_None. Qed.
Definition simpl_both_option_fmap_None_sym {A B} (f : A → B) (x : option A) :=
  simpl_both_sym (=) (simpl_both_option_fmap_None f x).
Global Existing Instance simpl_both_option_fmap_None_sym | 5.
Global Instance simpl_both_option_fmap_neq_None {A B} (f : A → B) (x : option A) :
  SimplBoth (f <$> x ≠ None) (x ≠ None).
Proof. by split; rewrite fmap_None. Qed.
(* TODO: should this be SimplBoth? *)
Global Instance simpl_impl_option_neq_None {A} (x : option A) :
  SimplImpl (x ≠ None) (∃ y, x = Some y).
Proof. split; destruct x; naive_solver. Qed.

Global Instance simpl_both_rotate_lookup_Some A b l i (x : A):
  SimplBoth (rotate b l !! i = Some x)
    (l !! rotate_nat_add b i (length l) = Some x ∧ (i < length l)%nat).
Proof. constructor. by rewrite lookup_rotate_r_Some. Qed.
Definition simpl_both_rotate_lookup_Some_sym A b l i (x : A) :=
  simpl_both_sym (=) (simpl_both_rotate_lookup_Some A b l i x).
Global Existing Instance simpl_both_rotate_lookup_Some_sym | 5.

(* Unsafe because the other direction does not hold if base >= len.
  But one should not use rotate nat in this case.
   TODO: use CanSolve when it is able to prove base < len for slot_for_key_ref key len *)
Global Instance simpl_rotate_nat_add_0_Unsafe base offset len:
  SimplAndUnsafe (base = rotate_nat_add base offset len) ((base < len)%nat ∧ offset = 0%nat).
Proof. constructor. move => [? ->]. rewrite rotate_nat_add_0 //. Qed.

Global Instance simpl_rotate_nat_add_next_Unsafe (base offset1 offset2 len : nat) `{!CanSolve (0 < len)%nat}:
  SimplAndUnsafe ((rotate_nat_add base offset1 len + 1) `rem` len = rotate_nat_add base offset2 len) (offset2 = S offset1).
Proof.
  constructor. unfold CanSolve in * => ->.
  rewrite rotate_nat_add_S // Nat2Z.inj_mod.
  rewrite Z.rem_mod_nonneg //=; lia.
Qed.
