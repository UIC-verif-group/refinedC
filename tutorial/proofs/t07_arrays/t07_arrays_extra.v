From refinedc.typing Require Import typing.

Definition sum_list_Z : list Z → Z :=
  fix go l :=
  match l with
  | []     => 0
  | x :: l => x + go l
  end.

Definition index_of_min_list_Z (l : list Z) (i : nat) :=
  ∃ x : Z, l !! i = Some x ∧ ∀ j y, l !! j = Some y → x ≤ y.

Lemma index_of_min_list_Z_take_1 (l : list Z) :
  (1 ≤ length l → index_of_min_list_Z (take 1 l) 0)%nat.
Proof.
  move: l => [] /=; first by lia.
  move => x l H; rewrite firstn_O; exists x.
  split; first done. move => [] y Hjy; by inversion Hjy.
Qed.

Lemma index_of_min_list_Z_last (m i : nat) (xm x : Z) (l : list Z) :
  l !! m = Some xm →
  x < xm →
  index_of_min_list_Z l m →
  index_of_min_list_Z (l ++ [x]) (length l).
Proof.
  move => Hm Hx [xm' [H1 H2]]. rewrite Hm in H1.
  inversion H1; subst xm'; simplify_eq. exists x. split.
  - rewrite lookup_app_r; last done. by rewrite Nat.sub_diag.
  - move => j y H. destruct (decide (j < length l)%nat).
    + assert (xm ≤ y); last by lia.
      apply: H2. by rewrite -H lookup_app_l.
    + rewrite lookup_app_r in H; last by lia.
      destruct (j - length l)%nat; by inversion H.
Qed.

Lemma index_of_min_list_Z_take_last (m i : nat) (xm xi : Z) (l : list Z) :
  i < length l →
  m < i →
  l !! m = Some xm →
  l !! i = Some xi →
  xi < xm →
  index_of_min_list_Z (take i l) m →
  index_of_min_list_Z (take (i + 1) l) i.
Proof.
  move => Hlen Hli Hm Hi Hxixm [xm' [H1 H2]].
  rewrite lookup_take in H1; last by lia. rewrite Hm in H1.
  inversion H1; subst xm'; simplify_eq. exists xi. split.
  - rewrite lookup_take; [ done | by lia ].
  - move => j y H. destruct (decide (j < i)%nat).
    + assert (xm ≤ y); last by lia. apply: H2.
      rewrite -H. rewrite lookup_take.
      * rewrite lookup_take; [ done | by lia ].
      * by lia.
    + clear H2. assert (xi = y); last by lia.
      assert (i = j) as Hij.
      { assert (j < i + 1); last by lia.
        assert (is_Some ((take (i + 1) l) !! j)) as P by by exists y.
        apply lookup_lt_is_Some_1 in P. rewrite length_take in P. lia. }
      subst j.
      rewrite lookup_take in H; last by lia.
      rewrite Hi in H. by inversion H.
Qed.

Lemma index_of_min_list_Z_take_not_last (m i : nat) (xm xi : Z) (l : list Z) :
  i < length l →
  m < i →
  l !! m = Some xm →
  l !! i = Some xi →
  xm ≤ xi →
  index_of_min_list_Z (take i l) m →
  index_of_min_list_Z (take (i + 1) l) m.
Proof.
  move => Hlen Hli Hm Hi Hxixm [xm' [H1 H2]].
  rewrite lookup_take in H1; last by lia. rewrite Hm in H1.
  inversion H1; subst xm'; simplify_eq. exists xm. split.
  - rewrite lookup_take; [ done | by lia ].
  - move => j y H. destruct (decide (j < i)%nat).
    + assert (xm ≤ y); last by lia. apply: H2.
      rewrite -H. rewrite lookup_take.
      * rewrite lookup_take; [ done | by lia ].
      * by lia.
    + clear H2. assert (xi = y); last by lia.
      assert (i = j) as Hij.
      { assert (j < i + 1); last by lia.
        assert (is_Some ((take (i + 1) l) !! j)) as P by by exists y.
        apply lookup_lt_is_Some_1 in P. rewrite length_take in P. lia. }
      subst j.
      rewrite lookup_take in H; last by lia.
      rewrite Hi in H. by inversion H.
Qed.

Global Typeclasses Opaque index_of_min_list_Z.
Opaque index_of_min_list_Z.
