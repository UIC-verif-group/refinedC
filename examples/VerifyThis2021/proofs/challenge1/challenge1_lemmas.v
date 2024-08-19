From stdpp Require Import sorting.
From refinedc.typing Require Import typing.

Local Set Default Goal Selector "!".

(* TODO: make this simplify_list tactic more useable?! *)
Lemma take_cons' {A} n a (l : list A) :
  n ≠ 0%nat →
  take n (a :: l) = a :: take (pred n) l.
Proof. by destruct n. Qed.
Lemma take_0' {A} n (l : list A) :
  n = 0%nat →
  take n l = [].
Proof. by destruct n. Qed.
Lemma drop_cons' {A} n a (l : list A) :
  n ≠ 0%nat →
  drop n (a :: l) = drop (pred n) l.
Proof. by destruct n. Qed.
Lemma drop_0' {A} n (l : list A) :
  n = 0%nat →
  drop n l = l.
Proof. by destruct n. Qed.
Lemma lookup_cons_eq_0 {A} (l : list A) x i : i = 0%nat → (x :: l) !! i = Some x.
Proof. by destruct i. Qed.
Lemma insert_eq_0 {A} (l : list A) y i : i = 0%nat → (length l ≠ 0%nat) → <[i := y]> l = y :: tail l.
Proof. by destruct i, l. Qed.
Lemma insert_cons_ne_0 {A} (l : list A) x y i : i ≠ 0%nat → <[i := y]> (x :: l) = x :: <[pred i := y]> l.
Proof. by destruct i. Qed.
Lemma tail_drop {A} (l : list A) : tail l = drop 1 l.
Proof. by destruct l. Qed.

Create HintDb simplify_list discriminated.
Global Hint Rewrite @firstn_cons @take_0 : simplify_list.
(* TODO: These hints don't seem to work if there is another take where the sidecondition fails. *)
(* Global Hint Rewrite @take_cons' @take_0' using list_lia : simplify_list. *)
(* Global Hint Rewrite @drop_cons' @drop_0' using list_lia : simplify_list. *)
Global Hint Rewrite @take_insert @take_insert_lt using list_lia : simplify_list.
Global Hint Rewrite @take_app_le @take_app_ge using list_lia : simplify_list.
Global Hint Rewrite @skipn_cons @drop_0 : simplify_list.
Global Hint Rewrite @drop_insert_gt @drop_insert_le using list_lia : simplify_list.
Global Hint Rewrite @drop_app_le @drop_app_ge using list_lia : simplify_list.
Global Hint Rewrite @take_take @drop_drop skipn_firstn_comm : simplify_list.
Global Hint Rewrite @lookup_cons_eq_0 @lookup_cons_ne_0 using list_lia : simplify_list.
Global Hint Rewrite @insert_eq_0 @insert_cons_ne_0 using list_lia : simplify_list.
Global Hint Rewrite @lookup_app_l @lookup_app_r using list_lia : simplify_list.
Global Hint Rewrite @app_nil_r : simplify_list.
Global Hint Rewrite @tail_drop : simplify_list.

Ltac simplify_list :=
  repeat first [
      progress simplify_length
    | progress autorewrite with simplify_list
    | progress repeat match goal with
      | |- context [take ?n ?l] =>
          let H := fresh in
          assert (n = 0%nat) as H by list_lia;
          rewrite (take_0' n l H);
          clear H
      | |- context [take ?n ?l] =>
          let H := fresh in
          assert ((length l ≤ n)%nat) as H by list_lia;
          rewrite (take_ge l n H);
          clear H
      | |- context [take ?n (?x::?l)] =>
          let H := fresh in
          assert (n ≠ 0%nat) as H by list_lia;
          rewrite (take_cons' n x l H);
          clear H
      | |- context [drop ?n ?l] =>
          let H := fresh in
          assert (n = 0%nat) as H by list_lia;
          rewrite (drop_0' n l H);
          clear H
      | |- context [drop ?n (?x::?l)] =>
          let H := fresh in
          assert (n ≠ 0%nat) as H by list_lia;
          rewrite (drop_cons' n x l H);
          clear H
      end
    | progress simpl
  ].


Global Instance simpl_and_fmap_snoc {A B} (f : A → B) l x y k `{!TCEq (x) (f y)}:
  SimplBothRel (=) ((f <$> l) ++ [x]) k (f <$> l ++ [y] = k) | 1.
Proof. revert select (TCEq _ _) => /TCEq_eq ->. by rewrite fmap_snoc. Qed.
Global Instance ge_trans : Transitive Z.ge.
Proof. move => ??. lia. Qed.

Lemma Sorted_small {A} R (l : list A):
  length l ≤ 1%nat →
  Sorted R l.
Proof. destruct l as [|?[]] => //= ?; [ constructor; constructor | lia]. Qed.

Lemma StronglySorted_NoDup {A} R (l : list A):
  StronglySorted R l →
  (∀ x, ¬ R x x) →
  NoDup l.
Proof.
  move => Hs Hirrefl. elim: Hs. { by constructor. }
  move => ???? /Forall_forall ?. constructor; [|done].
  naive_solver.
Qed.

Lemma Sorted_lookup_next {A} (R : A → A → Prop) (l : list A):
  (∀ i x y, l !! i = Some x → l !! S i = Some y → R x y) ↔ Sorted R l.
Proof.
  split.
  - elim: l. { constructor. }
    move => x l IH Hnext. constructor. { apply IH => i ??. move: (Hnext (S i)). naive_solver. }
    destruct l => //. constructor. by apply (Hnext 0%nat).
  - elim => //= ? {}l ? IH Hrel i x y ??. destruct i; simplify_eq/=.
    + by inversion Hrel; simplify_eq/=.
    + by apply: IH.
Qed.

Lemma Sorted_insert {A} (R : A → A → Prop) i x l y:
  Sorted R l →
  l !! i = Some y →
  R y x →
  Transitive R →
  (∀ z, l !! S i = Some z → R x z) →
  Sorted R (<[i:=x]> l).
Proof.
  move => Hs Hi ?? Hn.
  elim: Hs i Hi Hn => // z {}l ? IH Hd [|i] /= ? ?; simplify_eq.
  - constructor => //. destruct l => //. constructor. naive_solver.
  - constructor => //; [ by apply: IH|].
    inversion Hd; simplify_eq. destruct i => //=; simplify_eq/=; constructor => //. by etrans.
Qed.

Lemma delete_drop A (l : list A) i j :
  (j ≤ length l)%nat →
  delete i (drop j l) = drop j (delete (i + j)%nat l).
Proof.
  move => ?.
  rewrite !delete_take_drop drop_drop drop_app_le.
  2: { rewrite length_take. lia. }
  rewrite skipn_firstn_comm. do 2 f_equal; lia.
Qed.

Lemma insert_Permutation {A} i x (l : list A):
  (i < length l)%nat →
  <[i:=x]> l ≡ₚ x :: (delete i l).
Proof.
  move => ?.
  rewrite (delete_Permutation (<[i:=x]> l) i). 2: by apply: list_lookup_insert.
  rewrite !delete_take_drop drop_insert_gt ?take_insert //. lia.
Qed.

Lemma exists_snoc {A} (l : list A) :
  (0 < length l)%nat →
  ∃ x, l = take (length l - 1) l ++ [x].
Proof.
  elim/rev_ind: l => //=. { lia. }
  move => ????. eexists _. f_equal. rewrite take_app_length'// length_app/=. lia.
Qed.


Fixpoint lexico_lt (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => false
  | x1 :: l1', x2 :: l2' => if bool_decide (x1 = x2) then lexico_lt l1' l2' else bool_decide (x1 < x2)
  | _, _ => false
  end.

Infix "<ₗ" := lexico_lt (at level 80).

Section lexico.

Lemma lexico_top l l2:
  Sorted (Z.ge) l →
  l ≡ₚ l2 →
  ¬ (l <ₗ l2).
Proof.
  move => /Sorted_StronglySorted Hs. elim: Hs l2; clear.
  - move => [|] //=; naive_solver.
  - move => x1 l ? IH /Forall_forall Hall l2 Hl2 Hlt.
    destruct l2 as [|x2 l2] => //. simpl in *.
    case_bool_decide; subst.
    + apply: IH; [|done]. by apply: Permutation.Permutation_cons_inv.
    + have /elem_of_cons[//|Hin] : x2 ∈ x1 :: l by rewrite Hl2; set_solver.
      naive_solver lia.
Qed.

Lemma lexico_bot l l2:
  Sorted (Z.ge) l →
  l ≡ₚ l2 →
  ¬ (l2 <ₗ rev l).
Proof.
  move => /Sorted_StronglySorted.
  elim/rev_ind: l l2.
  - move => [|] //=; naive_solver.
  - move => x1 l IH l2 HSorted /=.
    rewrite rev_app_distr/=. destruct l2 => //=.
    { move => /Permutation_length. rewrite length_app /=. lia. }
    case_bool_decide; simplify_eq => Hcons.
    + apply: IH; [by apply: StronglySorted_app_inv_l|].
      rewrite <-Permutation_cons_append in Hcons.
        by apply: Permutation.Permutation_cons_inv.
    + rewrite <-Permutation_cons_append in Hcons.
      have /elem_of_cons[//|?]: z ∈ x1 :: l by rewrite Hcons; set_solver.
      have := elem_of_StronglySorted_app _ _ _ _ x1 ltac:(done) ltac:(done) ltac:(set_solver).
      case_bool_decide; naive_solver lia.
Qed.

Lemma lexico_bot' l l2:
  Sorted (Z.le) l →
  l ≡ₚ l2 →
  ¬ (l2 <ₗ l).
Proof.
  move => Hs ?. rewrite -(rev_involutive l). apply lexico_bot; [|by rewrite -Permutation_rev].
  elim: Hs => //.
  move => ????/= Hhd. apply: Sorted_snoc => //.
  inversion Hhd; constructor. lia.
Qed.

Lemma lexico_eq A1 A2:
  length A1 = length A2 →
  ¬ (A1 <ₗ A2) →
  ¬ (A2 <ₗ A1) →
  A1 = A2.
Proof.
  elim: A1 A2 => //. { by case. }
  move => ?? IH [//|??] [?] /=. do 2 case_bool_decide => //; simplify_eq.
  1: naive_solver.
  case_bool_decide => //.
  naive_solver lia.
Qed.

Global Instance lexico_trans : Transitive (λ l1 l2 : list Z, l1 <ₗ l2).
Proof.
  move => l1. elim: l1 => //. { move => []//. }
  move => ?? IH [|??] [|??] //=.
  repeat case_bool_decide => //; simplify_eq/=; naive_solver lia.
Qed.

Lemma lexico_irrefl A :
  ¬ (A <ₗ A).
Proof. elim: A => //=. { naive_solver. } move => ???. case_bool_decide => //. Qed.
End lexico.

Definition swap (i j : nat) (A : list Z) : list Z :=
  <[j := default 0 (A !! i)]> $
  <[i := default 0 (A !! j)]> A.
Global Typeclasses Opaque swap.
Lemma swap_intro i ni j nj A :
  A !! i = Some ni → A !! j = Some nj →
  <[j:=ni]> (<[i:=nj]> A) = swap i j A.
Proof. unfold swap. by move => -> ->. Qed.

Lemma swap_app_l i j A1 A2 :
  (i < length A1)%nat → (j < length A1)%nat →
  swap i j (A1 ++ A2) = swap i j A1 ++ A2.
Proof. move => ??. rewrite /swap !lookup_app_l // !insert_app_l ?length_insert//. Qed.
Lemma swap_app_r i j A1 A2 :
  (length A1 ≤ i)%nat → (length A1 ≤ j)%nat →
  swap i j (A1 ++ A2) = A1 ++ swap (i - length A1)%nat (j - length A1)%nat A2.
Proof. move => ??. rewrite /swap !lookup_app_r // !insert_app_r_alt //. Qed.

Lemma swap_start_end i j A :
  i = 0%nat →
  (j = length A - 1)%nat →
  (i < j)%nat →
  ∃ x y,
    A !! 0%nat = Some x ∧
    A !! (length A - 1)%nat = Some y ∧
    swap i j A = y :: take (length A - 2)%nat (drop 1 A) ++ [x].
Proof.
  move => -> ->. destruct A => //=; [lia|]. move => HA.
  rewrite drop_0.
  have [//|? Heq]:= exists_snoc A; [lia|].
  rewrite {1 4}Heq.
  eexists _, _. split; [done|]. split. {
    simplify_length. rewrite {3}Heq/=.
    rewrite Nat.min_l; [|lia].
    by simplify_list.
  }
  rewrite /= Nat.sub_0_r/swap/=.
  apply: (list_eq_split 1); simplify_list; [done|].
  by apply: (list_eq_split (length A - 1)); simplify_list.
Qed.

Definition next_start (i : nat) (A : list Z) :=
  ∃ ni niprev, A !! i = Some ni ∧
               A !! (i - 1)%nat = Some niprev ∧
               niprev < ni ∧ Sorted (Z.ge) (drop i A).
Global Typeclasses Opaque next_start.

Definition next_end (i j : nat) (A : list Z) :=
  ∃ nj ni, A !! j = Some nj ∧
           A !! (i - 1)%nat = Some ni ∧
           ni < nj ∧ i ≤ j ∧
           (∀ (u : nat) nu, A !! u = Some nu → j < u → nu ≤ ni).
Global Typeclasses Opaque next_end.

Inductive next_partial_swap : nat → nat → nat → list Z → list Z → Prop :=
| NPSBase s i j A Acur e:
    next_end i e A →
    s = i →
    j = (length A - 1)%nat →
    Acur = (swap (s - 1) e A) →
    next_partial_swap s i j Acur A
| NPSStep (s i j : nat) A A' Acur:
    s < i →
    j < length A - 1 →
    i ≤ S j →
    next_partial_swap s (pred i) (S j) A' A →
    Acur = (swap (pred i) (S j) A') →
    next_partial_swap s i j Acur A.

Inductive next_perm : list Z → option (list Z) → Prop :=
| NPNext l1 l2:
    l1 ≡ₚ l2 →
    l1 <ₗ l2 →
    (∀ l3, l3 ≡ₚ l1 → l1 <ₗ l3 → l3 <ₗ l2 → False) →
    next_perm l1 (Some l2)
| NPEnd l1 :
    ¬ (∃ l2, l1 ≡ₚ l2 ∧ l1 <ₗ l2) →
    next_perm l1 None
.

Lemma next_start_bound i A :
  next_start i A →
  0 < i < length A.
Proof.
  move => [?[?[Hs ?]]]. move: (Hs) => /(lookup_lt_Some _ _ _).
  split; [|lia].
  destruct i => //. destruct A => //. naive_solver lia.
Qed.

Lemma next_start_Sorted i A :
  next_start i A →
  Sorted (Z.ge) (drop i A).
Proof. case. naive_solver. Qed.

Global Instance simpl_next_start_Unsafe i1 i2 A `{!TCFastDone (next_start i2 A)}:
  SimplAndUnsafe (next_start i1 A) (i1 = i2).
Proof. unfold TCFastDone, SimplAndUnsafe in *. naive_solver. Qed.

Lemma next_start_lt i A ni niprev:
  next_start i A →
  A !! i = Some ni →
  A !! (i - 1)%nat = Some niprev →
  niprev < ni.
Proof. move => [?[?[?[??]]]]. naive_solver. Qed.
Lemma next_end_gt (j : nat) i e A niprev nj:
  next_end i e A →
  A !! (i - 1)%nat = Some niprev →
  A !! j = Some nj →
  ¬ nj ≤ niprev →
  ¬ e < j.
Proof. move => [?[?[?[?[? ?]]]]] ????. naive_solver lia. Qed.

Lemma next_end_exists i A ni niprev:
  A !! i = Some ni →
  A !! (i - 1)%nat = Some niprev →
  niprev < ni →
  ∃ e, next_end i e A.
Proof.
  elim/rev_ind: A => // x A IH Hi Hp ?.
  saturate_list_lookup.
  destruct (decide (niprev < x)).
  - eexists (length A). eexists _, _. split_and! => //.
    + by simplify_list.
    + list_lia.
    + intros. saturate_list_lookup. list_lia.
  - destruct (decide (i < length A)); subst. 2: {
     do [simplify_list] in Hi. naive_solver.
    }
    do [simplify_list] in Hi.
    do [simplify_list] in Hp.
    have [//|//|// |e [?[?[He[?[?[??]]]]]]]:= IH; simplify_eq.
    saturate_list_lookup.
    eexists e, _, _. split_and!.
    + by simplify_list.
    + by simplify_list.
    + list_lia.
    + list_lia.
    + move => ?? /lookup_app_Some[?|[? Hl]].
      * naive_solver lia.
      * saturate_list_lookup. do [simplify_list] in Hl. naive_solver lia.
Qed.

Lemma next_end_upper i e A:
  next_end i e A →
  e ≤ length A - 1.
Proof. move => [?]. solve_goal. Qed.


Lemma next_partial_swap_mono s1 s2 i1 i2 j1 j2 Acur1 Acur2 A1 A2:
  next_partial_swap s1 i1 j1 Acur1 A1 →
  s1 = s2 → i1 = i2 → j1 = j2 → Acur1 = Acur2 → A1 = A2 →
  next_partial_swap s2 i2 j2 Acur2 A2.
Proof. naive_solver. Qed.
Lemma next_partial_finish_step s i j Acur A:
  next_partial_swap s i j Acur A →
  next_start s A →
  ∃ e ne ns l1 l2 l3, next_end s e A ∧
     A !! e = Some ne ∧
     A !! (s - 1)%nat = Some ns ∧
     s ≤ j ∧
     i ≤ S j ∧
     (j + (i - s) = length A - 1)%nat ∧
     (take (i - s) (drop s (<[e:=ns]> A))) = l1 ∧
     (take (j + 1 - i) (drop i (<[e:=ns]> A))) = l2 ∧
     (take (length A - 1 - j) (drop (j + 1) (<[e:=ns]> A))) = l3 ∧
     Acur = take (s - 1)%nat A ++ [ne] ++ rev l3 ++ l2 ++ rev l1.
Proof.
  elim; clear.
  - move => ? i j A ? e [?[?[He[Hs[?[??]]]]]] ??? Hstart.
    move: (Hstart) => /next_start_bound[??]. simplify_eq.
    saturate_list_lookup.
    eexists _, _, _, _, _, _. split_and!.
    + eexists _, _. split_and!; [|done| done| | ] => //.
    + done.
    + done.
    + lia.
    + lia.
    + lia.
    + done.
    + done.
    + done.
    + rewrite /swap He Hs/=.
      apply: (list_eq_split (i - 1)); simplify_list; [done|].
      apply: (list_eq_split 1); simplify_list; [done|].
      apply: (list_eq_split (e - i)); simplify_list.
      * f_equal. f_equal. lia.
      * f_equal. f_equal. lia.
  - move => s i j A ?????? IH ? Hstart.
    have {IH}[//|xx[?[xxx[?[?[?[Hend?]]]]]]]:= IH.
    move : Hend => [?[?[He[Hs[?[??]]]]]].
    move: (Hstart) => /next_start_bound[??]. simplify_eq.
    move: (He) => /(lookup_lt_Some _ _ _)?.
    move: (Hs) => /(lookup_lt_Some _ _ _)?.
    destruct_and!. simplify_eq.
    eexists _, _, _, _, _, _.
    split_and!.
    { eexists _, _. by split_and!; [|done| done| | ]. }
    all: try done.
    all: try lia.
    (* TODO: simplify this proof using simplify_list *)
    rewrite swap_app_r ?length_take; [ |lia..].
    rewrite swap_app_r //=; [ |lia..].
    do 2 f_equal.
    rewrite Nat.min_l; [ |lia].
    have ->: (Init.Nat.pred i - (s - 1) - 1 = i - s - 1)%nat by lia.
    have ->: ((S j - (s - 1) - 1) = j + 1 - s)%nat by lia.
    have -> : ((length A - 1 - S j) = length A - j - 2)%nat by lia.
    have ?: ((i - s - 1) ≤ (j + 1 - s))%nat by lia.
    rewrite swap_app_r ?rev_length ?length_take ?length_drop ?length_insert//=.
    2, 3: rewrite Nat.min_l; lia.
    rewrite swap_app_l ?rev_length ?length_take ?length_drop ?length_insert//=.
    2, 3: rewrite ?Nat.min_l; [|lia..]; lia.
    rewrite Nat.min_l; [|lia].
    have ->: (i - s - 1 - (length A - j - 2) = 0)%nat by lia.
    have ->: (S (j + 1) - Init.Nat.pred i = S (S (j + 1 - i)))%nat by lia.
    pose proof (swap_start_end 0 ((j + 1 - s - (length A - j - 2)))%nat (take (S (S (j + 1 - i))) (drop (Init.Nat.pred i) (<[xx:=xxx]> A)))) as [?[?[? [? ->]]]].
    { done. }
    { rewrite ?length_take ?length_drop ?length_insert. rewrite Nat.min_l; lia. }
    { lia. }
    rewrite length_take length_drop length_insert Nat.min_l; [|lia].
    simpl.
    rewrite !skipn_firstn_comm drop_drop take_take.
    rewrite Nat.min_l. 2: lia.
    move Hl: ((<[xx:=xxx]> A)) => l.
    have ?: length l = length A by rewrite -Hl length_insert.
    have ->: (take (length A - 1 - j) (drop (j + 1) l) =
            x0 :: take (length A - j - 2) (drop (S (j + 1)) l)
             ). {
      revert select (take _ _ !! (length _ - 1)%nat = Some _).
      rewrite length_take length_drop length_insert lookup_take?lookup_drop ?Hl; [|lia] => Htake.
      have ->: (length A - 1 - j = S (length A - j - 2))%nat by lia.
      erewrite drop_S => /=//. rewrite -Htake. f_equal. lia.
    }

    simpl.
    rewrite -[in X in _ = X](app_assoc _ [x0]) /=. f_equal.
    f_equal.
    rewrite -(app_assoc _ [x]) /=. f_equal. { f_equal; [lia|]. f_equal. lia. }
    have ->: ((i - s) = S (pred i - s))%nat by lia.
    erewrite take_S_r. { by rewrite rev_app_distr. }
    rewrite lookup_drop.
    revert select (take _ _ !! 0%nat = Some _). rewrite lookup_take ?lookup_drop ?Hl; [|lia].
    move => <-. f_equal. lia.
Qed.

Lemma next_partial_finish s i j Acur A:
  next_start s A →
  next_partial_swap s i j Acur A →
  j ≤ i →
  ∃ e ne ns, next_end s e A ∧
       A !! e = Some ne ∧
       A !! (s - 1)%nat = Some ns ∧
       Acur = take (s - 1) A ++ [ne] ++ rev (drop s (<[e :=ns]> A)).
Proof.
  move => Hstart /next_partial_finish_step[//|?[?[?[?[?[??]]]]]].
  move: (Hstart) => /next_start_bound[??]. simplify_eq.
  destruct_and!; simplify_eq => ?.
  eexists _, _, _. split_and! => //.
  f_equal => /=. f_equal.
  rewrite -(take_drop (j + 1 - s) (drop s (_))).
  rewrite rev_app_distr. f_equal.
  - f_equal. rewrite drop_drop.
    rewrite firstn_skipn_comm. f_equal; [lia|].
    rewrite take_ge // length_insert. lia.
  - destruct (decide ((j + 1 - i) = 0)%nat) as [Heq|?].
    + rewrite Heq take_0/=. f_equal. rewrite take_drop. f_equal.
      f_equal. lia.
    + have Heq : ((j + 1 - i)%nat = 1%nat) by lia.
      rewrite Heq/=. rewrite take_drop.
      have ->: ((j + 1 - s) = (S (i - s)))%nat by lia.
      move Hl: ((<[_:=_]> A)) => l.
      have [|? Hp]:= lookup_lt_is_Some_2 l i. { rewrite -Hl length_insert. lia. }
      erewrite drop_S => //=.
      erewrite (take_S_r _ (i - s)%nat). 2: {
        rewrite lookup_drop.
        have -> : (s + (i - s) = i)%nat by lia.
        done.
      }
      by rewrite rev_app_distr.
Qed.


Lemma next_perm_implies_perm A B:
  next_perm A (Some B) → A ≡ₚ B.
Proof. by inversion 1. Qed.
Lemma next_perm_implies_lexico A B:
  next_perm A (Some B) → A <ₗ B.
Proof. by inversion 1. Qed.

Lemma next_perm_end l :
  Sorted (Z.ge) l →
  next_perm l None.
Proof. move => ?. constructor => -[?[??]]. by apply: lexico_top. Qed.

Lemma next_perm_cons A Acur x:
  next_perm A (Some Acur) →
  next_perm (x :: A) (Some (x :: Acur)).
Proof.
  inversion 1; simplify_eq.
  constructor => /=. { by constructor. } { by case_bool_decide. }
  move => [//|x3 l3] Hperm.
  case_bool_decide => //=; simplify_eq; case_bool_decide => //.
  - move => ?.
    revert select (∀ x, _). apply => //.
      by apply: Permutation.Permutation_cons_inv.
  - do 2 case_bool_decide => //. lia.
Qed.

Lemma next_perm_app A Acur xs:
  next_perm A (Some Acur) →
  next_perm (xs ++ A) (Some (xs ++ Acur)).
Proof. elim: xs => //=????. apply: next_perm_cons. eauto. Qed.

Lemma next_perm_next A Acur s i j:
  next_start s A →
  next_partial_swap s i j Acur A →
  j ≤ i →
  next_perm A (Some Acur).
Proof.
  move => Hstart Hnext ?.
  move: (Hstart) => /next_start_bound ?.
  move: (Hstart) => /next_start_Sorted Hsorted.
  move: Hnext => /next_partial_finish[//|//|e[?[?[[ne[ns[He[Hs[?[??]]]]]][?[??]]]]]].
  simplify_eq. rewrite -{1}(take_drop (s - 1) A).
  move: (He) => /(lookup_lt_Some _ _ _)?.
  move: (Hs) => /(lookup_lt_Some _ _ _)?.
  apply: next_perm_app => /=.
  erewrite drop_S; [|done].
  constructor.
  - rewrite -Permutation_rev.
    rewrite (delete_Permutation (_ :: drop s (<[e:=ns]> A)) (S (e - s)) ns). 2: {
      simpl. rewrite lookup_drop.
      have -> : (s + (e - s))%nat = e by lia.
      apply list_lookup_insert. lia.
    }
    constructor => /=.
    rewrite (delete_Permutation (drop (S (s - 1)) A) (e - s) ne). 2: {
      simpl. rewrite lookup_drop.
      have -> : (S (s - 1) + (e - s))%nat = e => //. lia.
    }
    constructor.
    rewrite !delete_drop ?length_insert; [|lia..]. f_equiv; [lia|].
    rewrite !delete_take_drop take_insert ?drop_insert_gt; [|lia..].
    do 2 f_equal; lia.
  - simpl. case_bool_decide; [lia|]. by case_bool_decide.
  - move => l3 Hl3.
    destruct l3 as [|x3 l3] => //=.
    case_bool_decide; simplify_eq.
    + move: Hl3. intros Hl3%Permutation.Permutation_cons_inv.
      case_bool_decide; simplify_eq; [lia|].
      move => ? /bool_decide_unpack ?.
      have Heq : (S (s - 1)) = s by lia. rewrite ->Heq in *.
      by apply: lexico_top.
    + move => /bool_decide_unpack ?.
      have /elem_of_cons[//|] : x3 ∈ ns :: drop (S (s - 1)) A by rewrite -Hl3; set_solver.
      have Heq : (S (s - 1)) = s by lia. rewrite ->Heq in *. clear Heq.
      case_bool_decide; simplify_eq.
      * move => ?.
        move => /lexico_bot. apply.
        -- rewrite drop_insert_le; [|lia].
           apply: Sorted_insert; [done|..].
           { rewrite lookup_drop. have ->: (s + (e - s))%nat = e by lia. done. }
           { lia. }
           move => z. rewrite lookup_drop => ?.
           revert select (∀ x, _) => Hb.
           have := Hb _ _ ltac:(done). lia.
        -- apply (@Permutation.Permutation_cons_inv _ _ _ ne). rewrite Hl3.
           rewrite drop_insert_le; [|lia].
           erewrite <-(list_insert_id (drop s A) (e - s)) at 2. 2:{
             rewrite lookup_drop. have -> : (s + (e - s))%nat = e by lia. done.
           }
           rewrite !insert_Permutation ?length_drop; [|lia..].
           apply: perm_swap.
      * move => /(elem_of_list_lookup_1 _ _)[nx ].
        rewrite lookup_drop => ? /bool_decide_unpack ?.
        revert select (∀ x, _) => Hb.
        have := Hb _ x3 ltac:(done).
        destruct (decide ( e = (s + nx)%nat)); simplify_eq/=.
        have : e < (s + nx)%nat. 2: lia.
        move: Hsorted => /Sorted_StronglySorted ?.
        have := StronglySorted_lookup_lt _ _ (e - s) nx _ _ ltac:(done).
        setoid_rewrite lookup_drop.
        have -> : (s + (e - s))%nat = e by lia.
        naive_solver lia.
Qed.

Lemma all_perms (A A' : list Z) (ps : (list (list Z))) Aend Ahead:
  (∀ i p1 p2, ps !! i = Some p1 → ps !! S i = Some p2 → next_perm p1 (Some p2)) →
  last ps = Some Aend →
  head ps = Some Ahead →
  Sorted (Z.le) Ahead →
  Ahead ≡ₚ A →
  next_perm Aend None →
  A ≡ₚ A' →
  A' ∈ ps.
Proof.
  rewrite last_lookup.
  destruct ps => //= Hnext Hlast [?] Hsorted Hhead Hend Hperm; subst.
  have := lexico_bot' _ A' ltac:(done) ltac:(by etrans).
  destruct (lexico_lt Ahead A') eqn: Hlt. 2: {
    move => ?.
    have <- := lexico_eq _ _ _ ltac:(done).
    - left.
    - apply: Permutation_length. by etrans.
    - destruct (Ahead <ₗ A') eqn:? => //. naive_solver.
  }
  move: Hlt => /Is_true_eq_left Hlt _.
  right. clear Hsorted. rewrite Hperm in Hhead. clear Hperm.
  elim: ps Ahead Hlast Hnext Hhead Hlt.
  - move => ? /= [?] ???.
    exfalso. simplify_eq.
    inversion Hend. contradict H. by eexists _.
  - move => Acur ? IH h /= ? Hnext ? ?.
    have Hnp := Hnext 0%nat _ _ ltac:(done) ltac:(done).
    destruct (decide (A' = Acur)); subst; [left|].
    right. apply: (IH Acur).
    + done.
    + move => ?????. by apply: (Hnext (S _)).
    + etrans;[|done]. symmetry. by apply: next_perm_implies_perm.
    + inversion Hnp; simplify_eq.
      destruct (Acur <ₗ A') eqn: Hle => //.
      contradict n.
      apply: lexico_eq.
      * apply: Permutation_length. symmetry. by etrans.
      * move => ?. by apply: (H3 A').
      * rewrite Hle. naive_solver.
Qed.

Lemma perms_no_dup ps :
  (∀ i p1 p2, ps !! i = Some p1 → ps !! S i = Some p2 → next_perm p1 (Some p2)) →
  NoDup ps.
Proof.
  move => Hps.
  apply: (StronglySorted_NoDup lexico_lt). 2: { by apply lexico_irrefl. }
  apply: Sorted_StronglySorted.
  apply Sorted_lookup_next => ?????.
  apply: next_perm_implies_lexico.
  naive_solver.
Qed.
