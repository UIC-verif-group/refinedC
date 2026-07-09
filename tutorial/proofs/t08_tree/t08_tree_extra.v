From refinedc.typing Require Import typing.

Inductive tree A : Type :=
  | leaf : tree A
  | node : tree A → A → tree A → tree A.

Arguments leaf {_}.
Arguments node {_}.

Global Instance inhabited_tree A : Inhabited (tree A).
Proof. constructor. exact leaf. Qed.

Definition node_data {A} (t : tree A) : option (tree A * A * tree A) :=
  match t with
  | leaf       => None
  | node l v r => Some (l, v, r)
  end.

Global Instance simpl_node_data_None A (t : tree A) :
  SimplBoth (node_data t = None) (t = leaf).
Proof. split; destruct t; naive_solver. Qed.
Definition simpl_node_data_None_sym A (t : tree A) :=
  simpl_both_sym (=) (simpl_node_data_None A t).
Global Existing Instance simpl_node_data_None_sym.

Global Instance simpl_node_data_Some A (t : tree A) x y z :
  SimplBoth (node_data t = Some (x, y, z)) (t = node x y z).
Proof. split; destruct t; naive_solver. Qed.
Definition simpl_node_data_Some_sym A (t : tree A) x y z :=
  simpl_both_sym (=) (simpl_node_data_Some A t x y z).
Global Existing Instance simpl_node_data_Some_sym.

Fixpoint tree_member (key : Z) (t : tree Z) : bool :=
  match t with
  | leaf       => false
  | node l k r => if bool_decide (k = key) then true
                  else if bool_decide (key < k) then
                      tree_member key l
                    else
                      tree_member key r
  end.

Fixpoint tree_insert (key : Z) (t : tree Z) : tree Z :=
  match t with
  | leaf       => node leaf key leaf
  | node l k r => if bool_decide (k = key) then t
                  else if bool_decide (key < k) then
                      node (tree_insert key l) k r
                    else
                      node l k (tree_insert key r)
  end.

Fixpoint tree_max_node (l : tree Z) (k : Z) (r : tree Z) : Z :=
  match r with
  | leaf       => k
  | node l k r => tree_max_node l k r
  end.

Definition tree_max (t : tree Z) : option Z :=
  match t with
  | leaf       => None
  | node l k r => Some (tree_max_node l k r)
  end.

Fixpoint tree_remove (key : Z) (t : tree Z) : tree Z :=
  match t with
  | leaf       => leaf
  | node l k r => if bool_decide (k = key) then
                   if tree_max l is Some m then
                     node (tree_remove m l) m r
                   else
                     r
                  else if bool_decide (key < k) then
                      node (tree_remove key l) k r
                    else
                      node l k (tree_remove key r)
  end.

Inductive tree_rel : gset Z → tree Z → Prop :=
| LeafRel: tree_rel ∅ leaf
| NodeRel l r sl sr k s:
    tree_rel sl l → tree_rel sr r →
    s = (sl ∪ {[k]} ∪ sr) →
    set_Forall (λ i, i < k) sl →
    set_Forall (λ i, k < i) sr →
    tree_rel s (node l k r).

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
  case: (IH _ tl _ k ltac:(done) _ _ ltac:(done)) => // m' [[<-] [??]].
  eexists _.
  split_and! => //; set_unfold_trigger; refined_solver (trigger_foralls; lia).
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
    + apply: tree_rel_trans => //.
      have ? : (k ∉ sr) by set_unfold; naive_solver lia.
      set_solver.
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
