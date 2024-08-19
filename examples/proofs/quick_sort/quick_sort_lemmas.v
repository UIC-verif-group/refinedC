From refinedc.typing Require Import typing.

Ltac simpl_insert :=
  match goal with
  | [ H : ?xs !! ?i = Some ?x |- context [ (<[?i:=?x]> ?xs) ] ] =>
      rewrite (list_insert_id _ _ _ H)
  end.

Definition interval : Type := nat → Prop.

Definition interval_eq (I : interval) {A : Type} (xs ys : list A) :=
  ∀ i, I i → xs !! i = ys !! i.

Notation "xs =[ I ]= ys" := (interval_eq I xs ys) (at level 40, format "xs  =[ I ]=  ys").

Lemma interval_eq_refl I {A : Type} (xs : list A) :
  xs =[I]= xs.
Proof. done. Qed.

Lemma interval_eq_trans I {A : Type} (xs ys zs : list A) :
  xs =[I]= zs → zs =[I]= ys → xs =[I]= ys.
Proof.
  move => Hxz Hzy i Hi.
  by rewrite Hxz ?Hzy.
Qed.

Lemma interval_eq_insert I {A : Type} (xs ys : list A) i x :
  ¬ I i → xs =[I]= ys → (<[i:=x]> xs) =[I]= ys.
Proof.
  move => Hi He j Hj.
  rewrite -He ?list_lookup_insert_ne => //.
  solve_goal.
Qed.

Notation "I ⊆ J" := (∀ i, I i → J i).

Lemma interval_eq_weaken (I J : interval) {A : Type} (xs ys : list A) :
  I ⊆ J → xs =[J]= ys → xs =[I]= ys.
Proof.
  move => Hs He i Hi.
  by apply He, Hs.
Qed.

Definition unchanged (l r : Z) {A : Type} (xs ys : list A) :=
  xs =[λ i, i < l]= ys ∧ xs =[λ i, i > r]= ys.
Global Typeclasses Opaque unchanged.

Ltac solve_unchanged :=
  try done;
  match goal with
  | [ |- ?X =[_]= ?X ] => by apply interval_eq_refl
  | [ |- <[_:=_]> _ =[_]=  _ ] =>
      apply interval_eq_insert; [ solve_goal | solve_unchanged ]
  | [ _ : ?X =[?a]= ?Y |- ?X =[_]= ?Y ] =>
      apply interval_eq_weaken with (J := a); [ solve_goal | solve_unchanged ]
  | [ _ : ?X =[_]= ?Z |- ?X =[_]= _ ] =>
      apply interval_eq_trans with (zs := Z); solve_unchanged
  end.

(* TODO: Remove this instance? *)
Global Instance simpl_unchanged {A} l r (xs ys : list A) :
  SimplBoth (unchanged l r xs ys) (xs =[λ i, i < l]= ys ∧ xs =[λ i, i > r]= ys).
Proof. done. Qed.

Inductive range : Type :=
  | ie : nat → nat → range (* [l, r) *)
  | ei : nat → nat → range (* (l, r] *)
  .

Global Instance range_elem_of : ElemOf nat range := λ i I,
  match I with
  | ie l r => l ≤ i ∧ i < r
  | ei l r => l < i ∧ i ≤ r
  end.
Global Typeclasses Opaque range_elem_of.

Global Instance range_elem_of_decision (i : nat) (I : range) : Decision (i ∈ I).
Proof.
  destruct I as [l r | l r].
  - destruct (decide (l ≤ i ∧ i < r)); by [ left | right ].
  - destruct (decide (l < i ∧ i ≤ r)); by [ left | right ].
Qed.

Global Instance simpl_range_elem_of_ie l r (i : nat) :
  SimplBoth (i ∈ ie l r) (l ≤ i ∧ i < r).
Proof. done. Qed.

Global Instance simpl_range_elem_of_ei l r (i : nat) :
  SimplBoth (i ∈ ei l r) (l < i ∧ i ≤ r).
Proof. done. Qed.

Definition range_forall (I : range) {A : Type} (φ : A → Prop) (xs : list A) :=
  ∀ i x, i ∈ I → (xs !! i = Some x → φ x).

Definition range_empty (I : range) :=
  match I with
  | ie l r | ei l r => r ≤ l
  end.

Lemma range_forall_empty {A : Type} (xs : list A) I φ :
  range_empty I → range_forall I φ xs.
Proof.
  rewrite /range_forall /elem_of => He i x Hi Hx.
  destruct I; solve_goal.
Qed.

Inductive extends {A : Type} (φ : A → Prop) (xs : list A) : range → range → Prop :=
  | extends_left (l r : nat) x :
    xs !! r = Some x →
    φ x →
    extends φ xs (ie l (r + 1)) (ie l r)
  | extends_right (l r : nat) x :
    xs !! l = Some x →
    φ x →
    extends φ xs (ei (l - 1) r) (ei l r)
  .

Ltac split_eq x y := destruct (decide (x=y)) as [<-|].

Lemma range_forall_extend {A : Type} (φ : A → Prop) I J xs :
  extends φ xs J I → range_forall I φ xs → range_forall J φ xs.
Proof.
  rewrite /range_forall /elem_of => H He i x Hi Hx.
  inversion H; subst.
  - split_eq r i; by [ congruence | apply (He i x); solve_goal ].
  - split_eq l i; by [ congruence | apply (He i x); solve_goal ].
Qed.

Lemma range_forall_insert {A : Type} (xs : list A) I φ i x :
  i ∉ I → range_forall I φ xs → range_forall I φ (<[i:=x]> xs).
Proof.
  rewrite /range_forall /elem_of => Hi He j y Hj Hy.
  rewrite list_lookup_insert_ne in Hy; last solve_goal.
  by apply (He j y).
Qed.

Definition partitioned (l s t r : nat) (key : Z) (xs : list Z) :=
  range_forall (ie l s) (λ x, x ≤ key) xs ∧ range_forall (ei t r) (λ x, key ≤ x) xs.
Global Typeclasses Opaque partitioned.

Global Instance simpl_partitioned l s t r key xs :
  SimplBoth (partitioned l s t r key xs)
    (range_forall (ie l s) (λ x, x ≤ key) xs ∧ range_forall (ei t r) (λ x, key ≤ x) xs).
Proof. done. Qed.


From stdpp Require Import natmap.

Section natmap_lemmas.

  Lemma natmap_to_list_disjoint_maps {A : Type} (m1 m2 : natmap A) :
    m1 ##ₘ m2 →
    map_to_list (m1 ∪ m2) ≡ₚ map_to_list m1 ++ map_to_list m2.
  Proof.
    move => Hd. apply NoDup_Permutation.
    - by apply NoDup_map_to_list.
    - rewrite NoDup_app. split; last split.
      all: try by apply NoDup_map_to_list.
      move => [i x]. rewrite !elem_of_map_to_list => ?.
      by eapply eq_None_ne_Some, map_disjoint_Some_l.
    - move => [i x].
      by rewrite elem_of_app !elem_of_map_to_list lookup_union_Some.
  Qed.

End natmap_lemmas.

Definition indexed {A : Type} (xs : list A) :=
  list_to_natmap (Some <$> xs).

Lemma indexed_lookup {A : Type} (xs : list A) i x :
  indexed xs !! i = Some x ↔ xs !! i = Some x.
Proof.
  rewrite list_to_natmap_spec list_lookup_fmap.
  split; move => He; by [ destruct (xs !! i) | rewrite He ].
Qed.

Definition unindexed {A : Type} (m : natmap A) :=
  snd <$> map_to_list m.

Lemma unindexed_elem_of {A : Type} (m : natmap A) x :
  x ∈ unindexed m ↔ ∃ i, m !! i = Some x.
Proof.
  rewrite elem_of_list_fmap. split.
  - move => [[i ?] [-> /elem_of_map_to_list ?]].
    by exists i.
  - move => [i ?].
    exists (i, x).
    by rewrite elem_of_map_to_list.
Qed.

Lemma strip_Nones_Forall_Some {A : Type} (l : natmap_raw A) :
  Forall is_Some l → strip_Nones l = l.
Proof.
  destruct l as [|x l] => //=.
  destruct x => // /Forall_forall He.
  have Hcontra : ∃ (y : A), None = Some y.
  { apply (He None). solve_goal. }
  by destruct Hcontra.
Qed.

(* TODO: The following proof is quite horrible since it unfolds the
definition of map_fold for natmap, but I am not sure what a better
proof would be. *)
Lemma indexed_unindexed {A : Type} (xs : list A) :
  unindexed (indexed xs) ≡ₚ xs.
Proof.
  rewrite /unindexed /indexed /list_to_natmap/map_to_list/map_fold/=.
  rewrite -fmap_reverse strip_Nones_Forall_Some.
  2: { rewrite Forall_fmap Forall_forall => ? ?. simpl. done. }
  rewrite -fmap_reverse reverse_involutive.
  move: 0%nat => n. move Hl: ([]) => l.
  have {2}-> : xs = l.*2 ++ xs by naive_solver.
  clear Hl.
  elim: xs n l; csimpl. { move => ??. by rewrite app_nil_r. }
  move => // x xs IH n l. rewrite IH. csimpl.
  apply Permutation_middle.
Qed.

Definition filter_index (I : interval) `{∀ x, Decision (I x)} {A : Type} (xs : list A) :=
  unindexed (filter (I ∘ fst) (indexed xs)).

Lemma filter_index_eq I `{∀ x, Decision (I x)} {A : Type} (xs ys : list A) :
  xs =[I]= ys → filter_index I xs = filter_index I ys.
Proof.
  move => Heq.
  rewrite /filter_index.
  apply f_equal, map_eq => i.
  apply option_eq => x.
  rewrite !map_lookup_filter_Some !indexed_lookup.
  split; move => [? ?]; by [ rewrite -Heq | rewrite Heq ].
Qed.

Definition filter_in_range (I : range) {A : Type} (xs : list A) :=
  filter_index (λ i, i ∈ I) xs.

Definition filter_out_range (I : range) {A : Type} (xs : list A) :=
  filter_index (λ i, i ∉ I) xs.

Lemma filter_in_out_range_perm I {A : Type} (xs : list A) :
   filter_in_range I xs ++ filter_out_range I xs ≡ₚ xs.
Proof.
  rewrite -fmap_app -natmap_to_list_disjoint_maps ?map_filter_union_complement;
    last by apply map_disjoint_filter_complement.
  by apply indexed_unindexed.
Qed.

Lemma filter_in_range_perm I {A : Type} (xs ys : list A) :
  xs ≡ₚ ys →
  xs =[λ i, i ∉ I]= ys →
  filter_in_range I xs ≡ₚ filter_in_range I ys.
Proof.
  move => Hp Heq.
  apply Permutation_app_inv_r with (l := filter_out_range I xs).
  by rewrite {2}/filter_out_range (filter_index_eq _ _ _ Heq)
    !filter_in_out_range_perm.
Qed.

Lemma range_forall_iff_Forall I {A : Type} (xs : list A) φ :
  range_forall I φ xs ↔ Forall φ (filter_in_range I xs).
Proof.
  rewrite /filter_in_range /filter_index Forall_forall.
  split.
  - move => He x /unindexed_elem_of [i /map_lookup_filter_Some
      [/indexed_lookup ? ?]].
    by apply (He i x).
  - move => He i x Hi Hx.
    apply (He x).
    rewrite unindexed_elem_of. exists i.
    by rewrite map_lookup_filter_Some indexed_lookup.
Qed.

Lemma perm_insert_swap {A : Type} (l1 l2 : list A) i j x y :
  (i < length l1)%nat →
  l1 !! j = Some y →
  <[i:=x]> l1 ≡ₚ l2 →
  <[j:=x]> (<[i:=y]> l1) ≡ₚ l2.
Proof.
  split_eq i j; first by intros; simpl_insert.
  move => Hlt Hj /Permutation_inj [Hlen [f [Hinj Heq]]].
  (* i ≠ j *)
  rewrite length_insert in Hlen.
  apply Permutation_inj. split.
  - by rewrite -Hlen length_insert length_insert.
  - exists (λ k, if bool_decide (k = i) then f j
      else if bool_decide (k = j) then f i else f k).
    split.
    + rewrite /Inj => a b Hab.
      repeat case_bool_decide; apply Hinj in Hab; congruence.
    + move => k.
      have ? : (j < length (<[i:=y]> l1))%nat.
      { rewrite length_insert. apply lookup_lt_is_Some. by exists y. }
      repeat case_bool_decide; simplify_eq; rewrite -Heq.
      all: by do!
        [ rewrite list_lookup_insert_ne; last solve_goal
        | rewrite list_lookup_insert;    last solve_goal ].
Qed.

Ltac solve_length_by_perm :=
  repeat match goal with
  | [ H : ?xs ≡ₚ ?ys |- context [ (length ?xs) ] ] =>
    rewrite (Permutation_length H)
  end; solve_goal.

Ltac solve_perm_by_trans :=
  repeat (eapply Permutation_trans; eauto).

Definition sorted (l r : Z) (xs : list Z) :=
  ∀ (i j : nat) x y, l ≤ i ∧ i < j ∧ j ≤ r →
    xs !! i = Some x → xs !! j = Some y → x ≤ y.

Lemma sorted_nil xs l r :
  r ≤ l → sorted l r xs.
Proof.
  rewrite /sorted. solve_goal.
Qed.

Lemma sorted_combine xs k key lo hi :
  xs !! k = Some key →
  partitioned (Z.to_nat lo) k k (Z.to_nat hi) key xs →
  sorted lo (k - 1) xs →
  sorted (k + 1) hi xs →
  sorted lo hi xs.
Proof.
  move => Hk [Hle Hge] Hsl Hsr i j x y ? Hx Hy.
  (* j < k *)
  destruct (decide (j < k)); first by eapply Hsl; solve_goal.
  (* k < i *)
  destruct (decide (k < i)); first by eapply Hsr; solve_goal.
  (* i ≤ k ∧ k ≤ j *)
  have : x ≤ key.
  { split_eq k i.
    - suff : x = key by solve_goal. congruence.
    - apply (Hle i); solve_goal. }
  have : key ≤ y.
  { split_eq k j.
    - suff : y = key by solve_goal. congruence.
    - apply (Hge j); solve_goal. }
  solve_goal.
Qed.

Lemma sorted_qsort xs1 xs2 xs3 k key lo hi :
  xs1 !! k = Some key →
  partitioned (Z.to_nat lo) k k (Z.to_nat hi) key xs1 →
  xs2 ≡ₚ xs1 →
  unchanged lo (k - 1) xs2 xs1 →
  sorted lo (k - 1) xs2 →
  xs3 ≡ₚ xs2 →
  unchanged (k + 1) hi xs3 xs2 →
  sorted (k + 1) hi xs3 →
  sorted lo hi xs3.
Proof.
  move => Hk [Hle Hge] Hp21 [Heq21 Heq21'] Hsl Hp32 [Heq32 Heq32'] Hsr.
  eapply sorted_combine with (k := k).
  + rewrite Heq32; last solve_goal.
    by rewrite Heq21'; last solve_goal.
  + split.
    - rewrite /range_forall /elem_of => i x Hi Hx.
      rewrite Heq32 in Hx; last solve_goal.
      eapply filter_in_range_perm in Hp21.
      * symmetry in Hp21.
        apply range_forall_iff_Forall in Hle.
        eapply Permutation_Forall in Hle; last by apply Hp21.
        apply range_forall_iff_Forall in Hle.
        by apply (Hle i).
      * rewrite /range_forall /elem_of /interval_eq => j Hj.
        destruct (decide (j < lo)).
        -- apply (Heq21 j); solve_goal.
        -- apply (Heq21' j); solve_goal.
    - eapply filter_in_range_perm in Hp32.
      * symmetry in Hp32.
        apply range_forall_iff_Forall.
        eapply Permutation_Forall. { by apply Hp32. }
        apply range_forall_iff_Forall.
        rewrite /range_forall /elem_of => i x Hi Hx.
        rewrite Heq21' in Hx; last solve_goal.
        by apply (Hge i).
      * rewrite /range_forall /elem_of /interval_eq => j Hj.
        destruct (decide (j > hi)).
        -- apply (Heq32' j); solve_goal.
        -- apply (Heq32 j); solve_goal.
  + move => i j x y ? Hx Hy.
    rewrite Heq32 in Hx; last solve_goal.
    rewrite Heq32 in Hy; last solve_goal.
    by eapply Hsl.
  + by apply Hsr.
Qed.
