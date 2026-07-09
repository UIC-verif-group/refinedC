From stdpp Require Import list sets ssreflect.

  (* upstream to stdpp? *)
Lemma list_difference_app_r `{!EqDecision A} (l k k' : list A) :
  list_difference l (k ++ k') =
    list_difference (list_difference l k) k'.
Proof.
  induction l in k,k' |- * => //=.
  case_decide.
  - case_decide => /=; first by rewrite IHl.
    case_decide; [ by rewrite IHl | set_solver ].
  - case_decide => /=; first set_solver.
    case_decide => /=; first set_solver.
    by rewrite IHl.
Qed.

(* upstream or factor into a separate library lemma *)
Lemma unique_elems_cons_2 {A} (p p' : A) ps :
  NoDup (p :: p' :: ps) →
  NoDup (p :: ps).
Proof.
  move => Hunique /=. constructor.
  - by apply NoDup_cons in Hunique as [[? ?]%not_elem_of_cons ?].
  - by apply NoDup_cons in Hunique as [? [? ?]%NoDup_cons].
Qed.

(* upstream or factor into a separate library lemma *)
Lemma list_difference_unique_elems `{! EqDecision A} (p : A) ps :
  NoDup (p :: ps) → list_difference ps [p] = ps.
Proof.
  induction ps in p |- * => Hunique //=. case_decide.
  - apply NoDup_cons in Hunique as [[Hp _]%not_elem_of_cons _].
    set_solver.
  - rewrite IHps => //. by eapply (unique_elems_cons_2 _ a).
Qed.

Lemma drop_lt {A} (l : list A) n:
  (drop n l <> []) → (n < length l)%nat.
Proof.
  induction n in l|-*.
  - destruct l => //=; lia.
  - destruct l => //= ?.
    apply -> Nat.succ_lt_mono. by apply IHn.
Qed.

Lemma drop_ge'{A} (l : list A) n:
  (drop n l = []) → (length l ≤ n)%nat.
Proof.
  induction n in l|-*.
  - destruct l => //=; lia.
  - destruct l => //= ?; first lia.
    apply le_n_S. by apply IHn.
Qed.
