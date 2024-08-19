From stdpp.unstable Require Import bitblast.
From refinedc.typing Require Import typing.
From caesium Require Import builtins_specs.

(* TODO: make a proper version and upstream? *)
Ltac to_div_mod :=
  rewrite ->Z.rem_mod_nonneg in *; [|done..];
  rewrite ->Z.quot_div_nonneg in *; [|done..]
.

Definition encode_prio_bitmap (bm : list bool) : list Z :=
  let bigZ := little_endian_to_Z 1 (bool_to_Z <$> bm) in
  [Z.land (Z.ones 64) (bigZ ≫ (64 * 0));
   Z.land (Z.ones 64) (bigZ ≫ (64 * 1));
   Z.land (Z.ones 64) (bigZ ≫ (64 * 2));
   Z.land (Z.ones 64) (bigZ ≫ (64 * 3))].

Notation num_priorities := (max_int u8 + 1) (only parsing).

Notation array_p ly elts n :=
  (array ly (elts ++ replicate n (uninit ly)))
  (only parsing).

Lemma encode_prio_bitmap_length bm :
  length (encode_prio_bitmap bm) = 4%nat.
Proof. done. Qed.
#[export] Hint Rewrite encode_prio_bitmap_length : lithium_rewrite.

(** Some helpful tactics *)
Local Ltac destruct_priority priority :=
  destruct (decide (priority = 0)); [try lia|
  destruct (decide (priority = 1)); [try lia|
  destruct (decide (priority = 2)); [try lia|
  destruct (decide (priority = 3)); try lia]]].

Local Ltac rewrite_priority H :=
  match goal with
  | E : (?priority `div` 64 = ?x) |- _ =>
      try rewrite E in H; try rewrite E; try subst; inversion_clear H
  end.

(** Some helpful arithmetic facts *)

Lemma Z_lt_ge_exists_sub' k j lvl :
  0 ≤ k →
  j < lvl * 64 + k →
  ¬ j < lvl * 64 →
  ∃ i : Z, 0 ≤ i < k ∧ j = lvl * 64 + i.
Proof.
  intros Hk Hlt Hge.
  apply Znot_lt_ge, Z.ge_le in Hge.
  apply Z.le_exists_sub in Hge as [i [Hi Hi']].
  eauto with lia.
Qed.

Lemma testbit_land_ones_shiftr a b k n:
  0 ≤ k < n →
  Z.testbit (Z.land (Z.ones n) (a ≫ b)) k = Z.testbit a (b + k).
Proof.
  move => H. bitblast. by rewrite Z.add_comm.
Qed.

Lemma encode_prio_bitmap_lookup_Some bm (i : nat) x :
  encode_prio_bitmap bm !! i = Some x ↔
   i < 4 ∧ x = Z.land (Z.ones 64) (little_endian_to_Z 1 (bool_to_Z <$> bm) ≫ (64 * i)).
Proof. do 4 (destruct i as [|i]; [naive_solver|]). naive_solver lia. Qed.

Lemma encode_prio_bitmap_lookup_total bm (i : nat) :
  i < 4 →
  encode_prio_bitmap bm !!! i =
    Z.land (Z.ones 64) (little_endian_to_Z 1 (bool_to_Z <$> bm) ≫ (64 * i)).
Proof. do 4 (destruct i as [|i]; [naive_solver|]). naive_solver lia. Qed.

Lemma encode_prio_bitmap_bound bm i y :
  encode_prio_bitmap bm !! (Z.to_nat i) = Some y →
  0 ≤ y < 2 ^ 64.
Proof.
  move => /encode_prio_bitmap_lookup_Some [? ->].
  rewrite Z.land_comm Z.land_ones; last lia.
  by apply Z.mod_pos_bound.
Qed.

Lemma testbit_spec_bitmap_out_of_range bm i :
  (length bm ≤ (Z.to_nat i))%nat →
  Z.testbit (little_endian_to_Z 1 (bool_to_Z <$> bm)) i = false.
Proof.
  move => Hlen.
  have H: (0 ≤ little_endian_to_Z 1 (bool_to_Z <$> bm) < 2 ^ length bm); last bitblast.
  rewrite -(Z.mul_1_r (length bm)) -(length_fmap bool_to_Z).
  apply (little_endian_to_Z_bound _ _); first lia.
  by rewrite Forall_map Forall_forall => x; case x.
Qed.

Lemma little_endian_to_Z_bool_to_Z_spec bm n :
  0 ≤ n →
  Z.testbit (little_endian_to_Z 1 (bool_to_Z <$> bm)) n = default false (bm !! (Z.to_nat n)).
Proof.
  move => ?.
  destruct (bm !! Z.to_nat n) eqn:E.
  - rewrite (little_endian_to_Z_spec _ _ _ (bool_to_Z b)); try lia.
    + rewrite Z.mod_1_r. case b; done.
    + rewrite /bool_to_Z Forall_map Forall_forall => x; case x; lia.
    + by rewrite Z.div_1_r list_lookup_fmap E.
  - apply lookup_ge_None_1 in E.
    by rewrite -(testbit_spec_bitmap_out_of_range bm n).
Qed.

Lemma encode_prio_bitmap_spec bm lvl k y b:
  length bm = 256%nat →
  0 ≤ lvl →
  0 ≤ k < 64 →
  encode_prio_bitmap bm !! Z.to_nat lvl = Some y →
  Z.testbit y k = b ↔
  bm !! Z.to_nat (lvl * 64 + k) = Some b.
Proof.
  move => Hlen ? ? Hlookup.
  destruct (bm !! _) eqn:Hlookup'; last first.
  - apply lookup_ge_None_1 in Hlookup'.
    suff: lvl < 4 by lia.
    apply lookup_lt_Some in Hlookup.
    simpl in Hlookup; lia.
  - destruct_priority lvl; simplify_eq/=; last first.
    { apply lookup_lt_Some in Hlookup'; lia. }
    all: rewrite testbit_land_ones_shiftr ?little_endian_to_Z_bool_to_Z_spec ?Hlookup'; [|lia..].
    all: naive_solver.
Qed.

Lemma highest_pending_priority_not_in_element bm lvl y j:
  length bm = 256%nat →
  0 ≤ lvl →
  encode_prio_bitmap bm !! Z.to_nat lvl = Some y →
  (∀ j : Z, 0 ≤ j < lvl * 64 → bm !! Z.to_nat j = Some false) →
  0 ≤ j < (lvl + 1) * 64 →
  Z_least_significant_one y = -1 →
  bm !! Z.to_nat j = Some false.
Proof.
  move => ? ? Hlookup Hfalse_bits Hrange Hy.
  destruct (decide (j < lvl * 64)) as [Hlt | Hge]; [naive_solver lia|].
  apply (Z_lt_ge_exists_sub' 64) in Hge as [k [Hk ->]]; try lia.
  eapply encode_prio_bitmap_spec => //.
  replace y with 0 in *; first by apply Z.bits_0.
  unfold Z_least_significant_one in Hy.
  case_bool_decide => //.
  pose proof (Z.log2_nonneg (Z.land y (-y))); lia.
Qed.

Lemma encode_prio_bitmap_insert bm priority b new_int old_int i:
  length bm = 256%nat →
  0 ≤ priority < 256 →
  encode_prio_bitmap bm !! Z.to_nat (priority `div` 64) = Some old_int →
  encode_prio_bitmap (<[Z.to_nat priority := b]> bm) !! Z.to_nat (priority `div` 64) = Some new_int →
  i ≠ priority `mod` 64 →
  0 ≤ i →
  Z.testbit new_int i = Z.testbit old_int i.
Proof.
  move => Hlen Hprio Hold_int Hnew_int Hneq Hlt.
  destruct (decide (i < 64)).
  + apply (encode_prio_bitmap_spec (<[Z.to_nat priority:=b]> bm) (priority `div` 64) _ _) => //; try lia.
    * by rewrite length_insert.
    * rewrite list_lookup_insert_ne; last lia.
      by apply (encode_prio_bitmap_spec bm _ i old_int) => //; try lia.
  + apply encode_prio_bitmap_lookup_Some in Hold_int as [? ->], Hnew_int as [? ->].
    bitblast.
Qed.

Lemma priority_level_set_clear_rest bm priority b :
  list_subequiv [Z.to_nat (priority `div` 64)] (encode_prio_bitmap bm)
    (encode_prio_bitmap (<[Z.to_nat priority := b]> bm)).
Proof.
  move => i; split; first done.
  move => Hi.
  apply option_eq => ?.
  rewrite !encode_prio_bitmap_lookup_Some.
  destruct (decide (i < 4)); [|lia].
  do 2 f_equiv.
  bitblast as z.
  rewrite !little_endian_to_Z_bool_to_Z_spec; try lia.
  f_equal; rewrite list_lookup_insert_ne => //.
  set_solver by lia.
Qed.

Lemma priority_level_set_changed bm priority old_int :
  length bm = 256%nat →
  0 ≤ priority < 256 →
  encode_prio_bitmap bm !! Z.to_nat (priority `div` 64) = Some old_int →
  Z.lor old_int (1 ≪ (priority `mod` 64)) = encode_prio_bitmap (<[Z.to_nat priority := true]> bm)
    !!! Z.to_nat (priority `div` 64).
Proof.
  move => Hlen Hrange Hold_int.
  symmetry. bitblast as i.
  - apply (encode_prio_bitmap_spec (<[Z.to_nat priority:=true]> bm) (priority `div` 64) _ _) => //; try lia.
    + by rewrite length_insert.
    + apply list_lookup_lookup_total_lt => /=. lia.
    + replace i with (priority `mod` 64) by lia.
      rewrite Z.mul_comm -Z_div_mod_eq_full.
      rewrite list_lookup_insert => //; lia.
  - eapply encode_prio_bitmap_insert=> //; try lia.
    apply list_lookup_lookup_total_lt => /=. lia.
Qed.

Lemma priority_level_clear_changed bm priority old_int:
  length bm = 256%nat →
  0 ≤ priority < 256 →
  encode_prio_bitmap bm !! Z.to_nat (priority `div` 64) = Some old_int →
  Z.land old_int (Z_lunot (bits_per_int u64) (1 ≪ (priority `mod` 64))) =
    encode_prio_bitmap (<[Z.to_nat priority := false]> bm) !!! Z.to_nat (priority `div` 64).
Proof.
  move => Hlen Hrange Hold_int.
  reduce_closed (bits_per_int u64).
  symmetry. bitblast as i.
  - have ? : (i = priority `mod` 64) by lia. subst.
    apply (encode_prio_bitmap_spec (<[Z.to_nat priority:=false]> bm) (priority `div` 64)); solve_goal.
  - eapply encode_prio_bitmap_insert; solve_goal.
  - rewrite encode_prio_bitmap_lookup_total; [|lia].
    bitblast.
Qed.

(** `find_highest_prio` facts *)

Definition find_highest_prio (bm : list bool) : Z :=
  match list_find is_true bm with
  | None => -1
  | Some tuple' => fst tuple'
  end.

Lemma encode_prio_bitmap_least_significant_one_bound bm i y :
  encode_prio_bitmap bm !! Z.to_nat i = Some y →
  Z_least_significant_one y ≤ 64.
Proof.
  move => /encode_prio_bitmap_bound ?.
  have := Z_least_significant_one_upper_bound y 64.
  lia.
Qed.

Lemma least_significant_one_range bm ind y:
  0 ≤ ind →
  encode_prio_bitmap bm !! Z.to_nat ind = Some y →
  0 < y →
  0 ≤ Z_least_significant_one y < 64.
Proof.
  move => Hind /encode_prio_bitmap_bound Hlookup Hy.
  split; first by apply Z_least_significant_one_lower_bound_pos.
  apply Z_least_significant_one_upper_bound; lia.
Qed.

Lemma highest_pending_priority_found (bm : list bool) (y lvl: Z):
  length bm = 256%nat →
  0 ≤ lvl →
  (∀ j : Z, 0 ≤ j < lvl * 64 → bm !! (Z.to_nat j) = Some false) →
  (encode_prio_bitmap bm) !! (Z.to_nat lvl) = Some y →
  Z_least_significant_one y ≠ -1 →
  find_highest_prio bm = lvl * 64 + (Z_least_significant_one y).
Proof.
  move => ? ? Hzeros Hlookup Hnon_empty.
  have Hy : 0 < y.
  { destruct (decide (y = 0)) as [E|E]; first by subst.
    apply encode_prio_bitmap_bound in Hlookup. lia. }
  have [Htrue_bit Hfalse_bits]: is_least_significant_one (Z_least_significant_one y) y
    by (apply Z_least_significant_one_is_least_significant_one).
  set (k := Z_least_significant_one y).
  have Hk : 0 ≤ k < 64 by apply (least_significant_one_range bm lvl).
  apply (encode_prio_bitmap_spec bm lvl (Z_least_significant_one y) y true) in Htrue_bit => //.
  destruct (list_find is_true bm) as [[p [ ]] | ] eqn:E;
    [ | by apply list_find_Some in E as [_ [H _]] | ].
  - unfold find_highest_prio; rewrite E => //=.
    apply list_find_Some in E as [Hp [_ Hfalse_bits']].
    have H0 : 0 ≤ p by lia.
    have Hle: p ≤ lvl * 64 + k.
    { destruct (decide ((lvl * 64 + k) < p)) as [E | E].
      + apply Hfalse_bits' in Htrue_bit; first done.
        suff: 0 ≤ Z_least_significant_one y by lia.
        by apply Z_least_significant_one_lower_bound_pos.
      + by apply Z.nlt_ge in E. }
    suff Hge: p >= lvl * 64 + k by lia.
    destruct (decide (p < lvl * 64 + k)) as [Hlt|?] => //.
    suff Hfalse: @lookup _ _ _ (list_lookup) p bm = Some false
      by rewrite Hp in Hfalse.
    destruct (decide (p < lvl * 64)) as [? | Hge].
    + have Hrange: (0 ≤ p < lvl * 64) by lia.
      apply Hzeros in Hrange. by replace p with (Z.to_nat p) by lia.
    + apply (Z_lt_ge_exists_sub' k) in Hge as [i [Hi Hp']]; try lia.
      have Hi': 0 ≤ i < 64 by lia.
      apply Hfalse_bits in Hi.
      apply (encode_prio_bitmap_spec bm lvl i y false) in Hi => //.
      replace p with (Z.to_nat p) by lia; by rewrite -Hp' in Hi.
  - apply list_find_None in E.
    by eapply (Forall_lookup_1 _ _ _ _ E) in Htrue_bit.
Qed.

Lemma highest_pending_priority_not_found bm lvl :
  length bm = 256%nat →
  4 ≤ lvl →
  (∀ j : Z, 0 ≤ j < lvl * 64 → bm !! (Z.to_nat j) = Some false) →
  find_highest_prio bm = -1.
Proof.
  move => Hlen ? Hzeros.
  unfold find_highest_prio.
  destruct (list_find is_true bm) as [[p [ ]] | ] eqn:E;
    [ | by apply list_find_Some in E as [_ [? _]] | ] => //.
  apply list_find_Some in E as [Hlookup [HP _]].
  destruct (decide (p < lvl * 64)) as [Hlt | Hge].
  { have Hrange: 0 ≤ p < lvl * 64 by lia.
    apply Hzeros in Hrange.
    replace (Z.to_nat p) with p in Hrange by lia; naive_solver.
  }
  apply lookup_lt_Some in Hlookup.
  rewrite Hlen in Hlookup; lia.
Qed.

Global Opaque encode_prio_bitmap.
