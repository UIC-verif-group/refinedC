From refinedc.typing Require Import typing.

Arguments Nat.div : simpl never.

Inductive tree (A : Type) :=
| Leaf : tree A
| Node : tree A → A → tree A → tree A.

Arguments Leaf {_}.
Arguments Node {_}.

Global Instance inhabited_tree A : Inhabited (tree A) := populate Leaf.

Definition node_data {A} (t : tree A) : option (tree A * A * tree A) :=
  match t with
  | Leaf       => None
  | Node l v r => Some (l, v, r)
  end.

Global Instance simpl_node_data_None A (t : tree A) :
  SimplBothRel (=) (node_data t) None (t = Leaf).
Proof. split; destruct t; naive_solver. Qed.

Global Instance simpl_node_data_Some A (t : tree A) x y z :
  SimplBothRel (=) (node_data t) (Some (x, y, z)) (t = Node x y z).
Proof. split; destruct t; naive_solver. Qed.

Fixpoint tree_member (key : Z) (t : tree Z) : bool :=
  match t with
  | Leaf       => false
  | Node l k r => if bool_decide (k = key) then true
                  else if bool_decide (key < k) then
                      tree_member key l
                    else
                      tree_member key r
  end.

Fixpoint tree_insert (key : Z) (t : tree Z) : tree Z :=
  match t with
  | Leaf       => Node Leaf key Leaf
  | Node l k r => if bool_decide (k = key) then t
                  else if bool_decide (key < k) then
                      Node (tree_insert key l) k r
                    else
                      Node l k (tree_insert key r)
  end.

Fixpoint tree_max_node (l : tree Z) (k : Z) (r : tree Z) : Z :=
  match r with
  | Leaf       => k
  | Node l k r => tree_max_node l k r
  end.

Definition tree_max (t : tree Z) : option Z :=
  match t with
  | Leaf       => None
  | Node l k r => Some (tree_max_node l k r)
  end.

Fixpoint tree_remove (key : Z) (t : tree Z) : tree Z :=
  match t with
  | Leaf       => Leaf
  | Node l k r => if bool_decide (k = key) then
                   if tree_max l is Some m then
                     Node (tree_remove m l) m r
                   else
                     r
                  else if bool_decide (key < k) then
                      Node (tree_remove key l) k r
                    else
                      Node l k (tree_remove key r)
  end.

Inductive tree_rel : gset Z → tree Z → Prop :=
| LeafRel: tree_rel ∅ Leaf
| NodeRel l r sl sr k s:
    tree_rel sl l → tree_rel sr r →
    s = (sl ∪ {[k]} ∪ sr) →
    set_Forall (λ i, i < k) sl →
    set_Forall (λ i, k < i) sr →
    tree_rel s (Node l k r).

Lemma tree_rel_trans s1 s2 t: tree_rel s1 t → s1 = s2 → tree_rel s2 t.
Proof. by move => ? <-. Qed.

Lemma tree_rel_insert k s t:
  tree_rel s t →
  tree_rel ({[k]} ∪ s) (tree_insert k t).
Proof.
  elim: t s => /=.
  { move => ? Hrel. inversion Hrel; subst. apply: NodeRel; try apply LeafRel; set_solver. }
  move => tl IHl m tr IHr s. inversion_clear 1; simplify_eq.
  case_bool_decide; subst. { apply: NodeRel => //. set_solver. }
  case_bool_decide; apply: NodeRel; try apply: IHl; try apply: IHr; try done; set_unfold_trigger; refined_solver (trigger_foralls; lia).
Qed.

Lemma tree_rel_tree_max s t:
  tree_rel s t →
  tree_max t = None ∧ s = ∅ ∨ ∃ m, tree_max t = Some m ∧ m ∈ s ∧ set_Forall (λ i, i ≤ m) s.
Proof.
  destruct t as [|tl m tr]. { inversion 1. by left. }
  inversion_clear 1; simplify_eq. right.
  generalize dependent sl => sl. generalize dependent sr => sr => /=.
  elim: tr sr tl sl m.
  { move => ??? m. inversion_clear 1; subst => ??? /=. eexists _. split_and! => //; set_solver by lia. }
  move => tl _ k tr IH sr tl' sl m.
  inversion_clear 1; subst => ??? /=.
  case: (IH _ tl _ k ltac:(done) _ _ ltac:(done)) => // m' [[<-] [? Hb]].
  eexists _. split_and! => //; set_unfold_trigger; refined_solver (trigger_foralls; lia).
Qed.

Lemma tree_rel_remove k s t:
  tree_rel s t →
  tree_rel (s ∖ {[k]}) (tree_remove k t).
Proof.
  elim: t s k => /=.
  { move => ? k. inversion 1; subst. apply: tree_rel_trans => //. set_solver. }
  move => tl IHl m tr IHr s k. inversion_clear 1; simplify_eq.
  case_bool_decide; subst.
  - have ? : (k ∉ sr) by set_unfold; naive_solver lia.
    have ? : (k ∉ sl) by set_unfold; naive_solver lia.
    destruct (tree_rel_tree_max sl tl) as [[-> ->] |[? [-> [??]]]] => //.
    + apply: tree_rel_trans => //. have : (k ∉ sr) by set_unfold; naive_solver lia. set_solver.
    + apply: NodeRel => //; [ by apply: IHl| |set_unfold_trigger; refined_solver (trigger_foralls; lia)..].
      rewrite difference_union_L !difference_union_distr_l_L !difference_diag_L !difference_disjoint_L; set_solver.
  - case_bool_decide; apply: NodeRel; try apply: IHl; try apply: IHr; try done; by set_unfold_trigger; refined_solver (trigger_foralls; lia).
Qed.

Lemma tree_rel_member k s t:
  tree_rel s t → k ∈ s ↔ tree_member k t.
Proof.
  elim: t s => /=.
  { move => ? Hrel. inversion Hrel; subst. set_solver. }
  move => tl IHl m tr IHr s.
  inversion_clear 1; simplify_eq.
  case_bool_decide; subst; [by set_solver|].
  case_bool_decide; etrans; [|by apply IHl| |by apply IHr].
  - have ? : (k ∉ sr) by set_unfold; naive_solver lia. set_solver.
  - have ? : (k ∉ sl) by set_unfold; naive_solver lia. set_solver.
Qed.

Inductive list_tree_eq_aux {A : Type} : nat → list A → tree A → list A → Prop :=
| LT_zero l : list_tree_eq_aux 0 l Leaf l
| LT_other n l_l v l_r rest tr_l tr_r:
    (n ≠ 0)%nat →
    list_tree_eq_aux (n / 2)%nat (l_l ++ [v] ++ l_r ++ rest) tr_l ([v] ++ l_r ++ rest) →
    list_tree_eq_aux (n - n/2 - 1)%nat (l_r ++ rest) tr_r rest →
    list_tree_eq_aux n (l_l ++ [v] ++ l_r ++ rest) (Node tr_l v tr_r) rest.

Definition list_tree_eq {A : Type} (l : list A) (t : tree A) : Prop :=
  list_tree_eq_aux (length l) l t [].

Fixpoint tree_to_list {A} (t : tree A) : list A :=
  match t with
  | Leaf             => []
  | Node tr_l v tr_r => tree_to_list tr_l ++ [v] ++ tree_to_list tr_r
  end.

Lemma list_tree_eq_aux_tree_to_list {A : Type} (n : nat) (l rest : list A) (t : tree A):
  list_tree_eq_aux n l t rest → l = tree_to_list t ++ rest.
Proof.
  elim; first done.
  move => ????????? -> ? -> /=.
  by rewrite -app_assoc.
Qed.

Lemma tree_list_eq_annoying {A : Type} (n : nat) (l l_rest : list A) (t : tree A):
  list_tree_eq_aux n l t l_rest →
  (n ≤ length l)%nat →
  (length l_rest = length l - n)%nat.
Proof.
  elim; first lia.
  move => n0 l_l v l_r rest tr_l tr_r Hnz.
  assert (n0 `div` 2 < n0)%nat as Hdiv. { apply Nat.div_lt; lia. }
  revert Hdiv. generalize (n0 `div` 2)%nat => n0div2.
  rewrite !length_app /=. lia.
Qed.

Lemma tree_list_eq_full_length {A : Type} (l l_rest : list A) (t : tree A):
  list_tree_eq_aux (length l) l t l_rest →
  list_tree_eq l t.
Proof.
  rewrite /list_tree_eq => H.
  move: (tree_list_eq_annoying _ _ _ _ H ltac:(done)) => Hrest.
  rewrite Nat.sub_diag in Hrest. destruct l_rest; first done.
  simpl in Hrest. inversion Hrest.
Qed.

Global Instance simpl_tree_list_eq_aux_0_and {A : Type} (l l_rest : list A) (t : tree A):
  SimplAnd (list_tree_eq_aux 0 l t l_rest) (t = Leaf ∧ l_rest = l).
Proof.
  split.
  - move => [-> ->]. constructor.
  - move => H. by inversion H.
Qed.

Lemma list_tree_eq_aux_Node {A : Type} (n : nat) (l l' l_rest : list A) (tr_l tr_r : tree A) (v : A):
  (n ≠ 0)%nat →
  list_tree_eq_aux (n `div` 2)%nat l tr_l (v :: l') →
  list_tree_eq_aux (n - n `div` 2 - 1)%nat l' tr_r l_rest →
  list_tree_eq_aux n l (Node tr_l v tr_r) l_rest.
Proof.
  move => ? Hl Hr.
  move: (list_tree_eq_aux_tree_to_list _ _ _ _ Hl) => H1.
  move: (list_tree_eq_aux_tree_to_list _ _ _ _ Hr) => H2.
  rewrite H1 H2. apply LT_other; first done.
  - rewrite -H2. by rewrite H1 in Hl.
  - by rewrite H2 in Hr.
Qed.

Lemma list_tree_eq_aux_Node_Z {A : Type} (n : nat) (l l' l_rest : list A) (tr_l tr_r : tree A) (v : A):
  (n ≠ 0)%nat →
  list_tree_eq_aux (Z.to_nat (n `quot` 2)) l tr_l (v :: l') →
  list_tree_eq_aux (n - Z.to_nat (n `quot` 2) - Z.to_nat 1) l' tr_r l_rest →
  list_tree_eq_aux n l (Node tr_l v tr_r) l_rest.
Proof.
  assert (n - Z.to_nat (n `quot` 2)%Z - Z.to_nat 1 = n - n `div` 2 - 1)%nat as ->.
  { rewrite Z.quot_div_nonneg ?Z2Nat.inj_div; try lia. repeat f_equal. lia. }
  assert (Z.to_nat (n `quot` 2) = n `div` 2)%nat as ->.
  { rewrite Z.quot_div_nonneg ?Z2Nat.inj_div; try lia. f_equal. lia. }
  by apply list_tree_eq_aux_Node.
Qed.

Lemma list_tree_eq_aux_is_Some {A : Type} (n : nat) (l rest : list A) (t : tree A):
  list_tree_eq_aux (Z.to_nat (n `quot` 2)) l t rest →
  (n ≠ 0)%nat →
  (n ≤ length l)%nat →
  is_Some (maybe2 cons rest).
Proof.
  rewrite /is_Some Z.quot_div_nonneg ?Z2Nat.inj_div ?Nat2Z.id; try lia.
  change (Z.to_nat 2) with 2%nat. move => H Hnz Hle.
  assert (rest ≠ []); last first. { destruct rest; naive_solver. }
  assert (n `div` 2 ≤ length l)%nat as Hlediv2.
  { etransitivity; last done. apply Nat.Div0.div_le_upper_bound; lia. }
  move: (tree_list_eq_annoying _ _ _ _ H Hlediv2) => Hlen.
  assert (n `div` 2 < n)%nat as Hdiv. { apply Nat.div_lt; lia. }
  move => ?. subst rest. simpl in *. lia.
Qed.

Lemma list_tree_eq_aux_le {A : Type} (n : nat) (l rest : list A) (v : A) (t : tree A):
  list_tree_eq_aux (Z.to_nat (n `quot` 2)) l t (v :: rest) →
  (n ≠ 0)%nat →
  (n ≤ length l)%nat →
  (n - Z.to_nat (n `quot` 2) - Z.to_nat 1)%nat ≤ length rest.
Proof.
  rewrite Z.quot_div_nonneg ?Z2Nat.inj_div ?Nat2Z.id; try lia.
  change (Z.to_nat 2) with 2%nat. change (Z.to_nat 1) with 1%nat.
  move => H Hnx Hle.
  assert (n `div` 2 ≤ length l)%nat as Hlediv2.
  { etransitivity; last done. apply Nat.Div0.div_le_upper_bound; lia. }
  move: (tree_list_eq_annoying _ _ _ _ H Hlediv2). simpl. lia.
Qed.

(*
Lemma list_tree_eq_aux_tree_member (n : nat) (l_r l_rest : list Z) tr_r:
  list_tree_eq_aux n (l_r ++ l_rest) tr_r l_rest →
  ∀ i, i ∈ l_r ↔ tree_member i tr_r.
Proof.
  remember (l_r ++ l_rest) as l.
  move => H.
  elim: H l_r Heql.
  - move => *. admit.
  - move => /= ???????? H1 IH1 H2 IH2 ???.
    case_bool_decide.
    + admit.
    + case_bool_decide.
      apply IH1.

    rewrite IH2; last first.
Admitted.

Lemma list_tree_eq_sorted (n : nat) (l rest : list Z) (t : tree Z):
  list_tree_eq_aux n l t rest →
  StronglySorted (<) l →
  ∃ s, tree_rel s t ∧ ∀ i j, i ∈ s → j ∈ rest → i < j.
Proof.
  elim.
  - move => *. exists ∅. split; first apply LeafRel. set_solver.
  - move => ? l_l v l_r l_rest tl_l tr_r ? H1 IH1 H2 IH2 Hsorted.
    move: (IH1 Hsorted); clear IH1; move => [sl [Htr1 Hrest1]].
    assert (StronglySorted (<) (l_r ++ l_rest)) as Hsorted_tl.
    { do 2 apply StronglySorted_app_inv_r in Hsorted. done. }
    move: (IH2 Hsorted_tl); clear IH2; move => [sr [Htr2 Hrest2]].
    exists (sl ∪ {[v]} ∪ sr). split.
    + apply (NodeRel _ _ sl sr v) => //.
      * move => i Hi. apply Hrest1; set_solver.
      * move => i Hi.
        assert (i ∈ l_r). {
          assert (tree_member i tr_r) as Hmem by eapply tree_rel_member => //.
          by eapply list_tree_eq_aux_tree_member.
        }
        apply StronglySorted_app_inv_r in Hsorted.
        eapply (elem_of_StronglySorted_app _ [v]); set_solver.
    + move => i j /elem_of_union []; last by set_solver.
      move => /elem_of_union []; first by set_solver.
      move => /elem_of_singleton -> H.
      apply StronglySorted_app_inv_r in Hsorted.
      eapply (elem_of_StronglySorted_app _ [v]); set_solver.
Qed.
*)
