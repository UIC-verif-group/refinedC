From lithium Require Import hooks.
From refinedc.typing Require Import naive_simpl typing.
Set Default Proof Using "Type".

Ltac can_solve_hook ::= naive_solve.

Section defs.
  Context `{typeG Σ}.

  Inductive item_ref : Type :=
    | Empty
    | Entry (key : Z) (ty : type)
    | Tombstone (key : Z).

  Global Instance item_ref_empty_dec x: Decision (x = Empty).
  Proof. by destruct x; [left| right..]. Defined.

  Definition slot_for_key_ref (key : Z) (len : nat) : nat :=
    Z.to_nat (key `mod` len).

  Definition probe_ref_found (key : Z) (x : item_ref) : Prop :=
    match x with
    | Empty       => True
    | Entry k _
    | Tombstone k => key = k
    end.

  Global Instance probe_ref_found_decision key x : Decision (probe_ref_found key x).
  Proof. destruct x; simpl; apply _. Defined.

  (* TODO: define this via maybe? *)
  Definition item_ref_to_ty (x : item_ref) : option type := if x is Entry _ ty then Some ty else None.
  Definition item_ref_set_ty (x : item_ref) (ty : type) : item_ref := if x is Entry key _ then Entry key ty else x.
  Definition item_ref_to_key (x : item_ref) : option Z :=
    match x with
    | Entry key _ => Some key
    | Tombstone key => Some key
    | _ => None
    end.

  Definition probe_ref_go (key : Z) (items : list item_ref) : option (nat * item_ref) :=
    list_find (probe_ref_found key) items.
  Definition probe_ref (key : Z) (items : list item_ref) : option (nat * item_ref) :=
    let hash := slot_for_key_ref key (length items) in
    prod_map (λ idx, rotate_nat_add hash idx (length items)) id <$>
             (probe_ref_go key (rotate hash items)).

  Definition probe_ref_Empty_inv (key : Z) (items : list item_ref) : Prop :=
    (∀ i ir, items !! i = Some ir → item_ref_to_key ir = Some key → probe_ref key items = Some (i, ir)).

  Definition fsm_invariant (mp : gmap Z type) (items : list item_ref) : Prop :=
    (∀ key ty, mp !! key = Some ty ↔ ∃ i, probe_ref key items = Some (i, Entry key ty)) ∧
    (∀ key, probe_ref_Empty_inv key items).
  Local Typeclasses Opaque fsm_invariant.
  Local Typeclasses Opaque probe_ref.

  Lemma slot_for_key_ref_unfold_rem key (len : nat):
    0 ≤ key → 0 < len →
    key `rem` len = slot_for_key_ref key len.
  Proof. move => ??. rewrite /slot_for_key_ref Z.rem_mod_nonneg //; lia. Qed.

  Lemma slot_for_key_ref_length key n:
    (0 < n)%nat → (slot_for_key_ref key n < n)%nat.
  Proof. unfold slot_for_key_ref => ?. have [|??]:= Z_mod_lt key n; lia. Qed.

  Global Instance simpl_both_slot_for_key_ref_length key n:
    SimplBoth (slot_for_key_ref key n < n)%nat (0 < n)%nat.
  Proof.
    unfold SimplBoth, slot_for_key_ref. split.
    - destruct n; rewrite ?Zmod_0_r; lia.
    - move => ?. rewrite /slot_for_key_ref. have [|??]:= Z_mod_lt key n; lia.
  Qed.

  Local Instance simpl_both_list_find_Some A P x (l : list A) `{∀ x, Decision (P x)}:
    SimplBothRel (=) (list_find P l) (Some x) (l !! x.1 = Some x.2 ∧ P x.2 ∧ ∀ y : A, y ∈ take x.1 l → ¬ P y).
  Proof. unfold SimplBothRel. by rewrite list_find_Some'. Qed.

  Local Instance simpl_both_list_find_None A P (l : list A) `{∀ x, Decision (P x)}:
    SimplBothRel (=) (list_find P l) (None) (∀ y, y ∈ l → ¬ P y).
  Proof. unfold SimplBothRel. by rewrite list_find_None Forall_forall. Qed.


  (*** probe_ref_go lemmata *)
  (* used by automation *)
  Lemma probe_ref_go_next_take key items n:
    probe_ref_go key (take n items) = None →
    (∀ i, items !! n = Some i → ¬ probe_ref_found key i) →
    probe_ref_go key (take (S n) items) = None.
  Proof.
    move => Hl Hf. destruct (items !! n) as [i|] eqn:Hi.
    - rewrite (take_S_r _ _ i) //. move/list_find_None/Forall_forall in Hl.
      apply/list_find_None/Forall_forall. set_solver.
    - move/lookup_ge_None in Hi. rewrite firstn_all2; last lia. by rewrite firstn_all2 in Hl.
  Qed.
  (*** probe_ref lemmata *)

  Lemma probe_ref_lookup key l x:
    probe_ref key l = Some x ↔
    l !! x.1 = Some x.2 ∧ probe_ref_found key x.2 ∧ (x.1 < length l)%nat ∧ ∀ y, y ∈ rotate_take (slot_for_key_ref key (length l)) x.1 l → ¬ probe_ref_found key y.
  Proof.
    rewrite /probe_ref. move: x => [??]. split; naive_simpl.
    - revert select (_ ∈ rotate_take _ _ _). rewrite rotate_take_add //. eauto.
    - eexists (rotate_nat_sub (slot_for_key_ref key (length l)) _ (length l), _) => /=.
      rewrite rotate_nat_add_sub. 1: split_and! => //. 2: done.
      naive_simpl; rewrite ?rotate_nat_add_sub //; [apply rotate_nat_sub_lt|]; naive_solver lia.
  Qed.

  Local Instance simpl_both_probe_ref_Some key x l:
    SimplBothRel (=) (probe_ref key l) (Some x) (l !! x.1 = Some x.2 ∧ probe_ref_found key x.2 ∧ (x.1 < length l)%nat ∧ ∀ y, y ∈ rotate_take (slot_for_key_ref key (length l)) x.1 l → ¬ probe_ref_found key y).
  Proof. unfold SimplBothRel. by rewrite probe_ref_lookup. Qed.

  (* used by automation *)
  Lemma probe_ref_take_Some key n i items:
    probe_ref_go key (take n (rotate (slot_for_key_ref key (length items)) items)) = None →
    probe_ref_found key i →
    items !! rotate_nat_add (slot_for_key_ref key (length items)) n (length items) = Some i →
    probe_ref key items = Some (rotate_nat_add (slot_for_key_ref key (length items)) n (length items), i).
  Proof.
    naive_simpl. move => ?. revert select (_ ∈ rotate_take _ _ _).
    rewrite rotate_take_add; naive_simpl; try naive_solver lia.
    apply dec_stable => Hlen. revert select (∀ y, y ∈ _ → _) => Hempty.
    move: (Hempty i). rewrite take_ge; last by naive_solve.
    rewrite elem_of_rotate elem_of_list_lookup. naive_solve.
  Qed.

  Lemma probe_ref_Empty_inv_upd n key key' items ir' ir:
    probe_ref_Empty_inv key' items →
    probe_ref key items = Some (n, ir') →
    item_ref_to_key ir = Some key →
    probe_ref_Empty_inv key' (<[n:=ir]> items).
  Proof.
    move => Hinv. rewrite /probe_ref_Empty_inv.
    move => Hprobe ? i ir0 /list_lookup_insert_Some Hl ?.
    have ?: (probe_ref_found key' ir0) by destruct ir0; naive_solver.
    case: Hl.
    - move: Hprobe. naive_simpl. destruct (decide (key = key')); subst; last by destruct ir'; naive_solver.
      revert select (_ ∈ _). rewrite rotate_take_insert;[|naive_solve..]. case_decide => ?; naive_solver lia.
    - move => [? Hl]. opose proof* (Hinv i ir0) as Hp => //.
      destruct (decide (key = key')); simplify_eq. move: Hl Hprobe Hp. naive_simpl.
      revert select (_ ∈ _). rewrite rotate_take_insert;[|naive_solve..].
      case_decide; last naive_solver.
      move => /(list_elem_of_insert1 _ _ _ _)[?|?]; subst => //; last by naive_solver.
        by destruct ir; naive_solver.
  Qed.

  Lemma probe_ref_find_entry key ty items :
    probe_ref_Empty_inv key items →
    Entry key ty ∈ items → ∃ i, probe_ref key items = Some (i, Entry key ty).
  Proof. move => Hinv /elem_of_list_lookup[i ?]. eexists. by apply Hinv. Qed.

  (*** fsm_invariant *)
  (* used by automation *)
  Lemma fsm_invariant_lookup mp items key n ir o:
    fsm_invariant mp items → probe_ref key items = Some (n, ir) → o=item_ref_to_ty ir → mp !! key = o.
  Proof.
    rewrite /fsm_invariant. move => [Hinv ?] Hp ?; subst. apply option_eq => ty. rewrite (Hinv key ty) Hp.
    move: Hp => /probe_ref_lookup/=?. destruct ir; naive_solver.
  Qed.

  (* used by automation *)
  Lemma fsm_invariant_init items:
    (0 < length items)%nat → (∀ i, i ∈ items → i = Empty) →
    fsm_invariant ∅ items.
  Proof.
    move => ??. have <-: replicate (length items) Empty = items by apply replicate_as_elem_of.
    split => key.
    - move => ?. rewrite lookup_empty. setoid_rewrite probe_ref_lookup => /=.
      setoid_rewrite lookup_replicate. naive_solver.
    - move => ? ir /lookup_replicate[??]. by destruct ir.
  Qed.

  Lemma fsm_invariant_partial_alter key mp n items ir ir' f:
    fsm_invariant mp items →
    probe_ref key items = Some (n, ir) →
    (ir' = Empty → ir = Empty) →
    probe_ref_found key ir' →
    (f (item_ref_to_ty ir) = item_ref_to_ty ir') →
    fsm_invariant (partial_alter f key mp) (<[n:=ir']> items).
  Proof.
    move => Hinv Hprobe Hempty Hkey Hf.
    move: (Hprobe) => /probe_ref_lookup/= [Hn [?[??]]].
    move: (Hinv) => [Hinv1 Hinv2].
    opose proof* fsm_invariant_lookup as Hmp => //. rewrite -Hmp in Hf.
    destruct (item_ref_to_key ir') as [?|] eqn:Hkey'. 2: {
      destruct ir', ir => //; simpl in *; [|naive_solver..].
      by rewrite list_insert_id // partial_alter_self_alt' // Hf Hmp.
    }
    split => key'; last by apply: probe_ref_Empty_inv_upd => //; destruct ir' => //=; simpl in *; by simplify_eq.
    move => ?. destruct (decide (key = key')) as [<-|?].
    - rewrite lookup_partial_alter Hf.
      assert (probe_ref key (<[n:=ir']> items) = Some (n, ir')) as ->. 2: destruct ir'; naive_solver.
      naive_simpl. revert select (_ ∈ _). rewrite rotate_take_insert;[case_decide|..]; naive_solver lia.
    - rewrite lookup_partial_alter_ne // Hinv1. f_equiv => i. split; naive_simpl.
      1: { rewrite list_lookup_insert_Some. naive_solver. }
      2: { revert select ( <[ _ := _ ]> _ !! _ = Some _). rewrite list_lookup_insert_Some. naive_solver. }
      2: revert select ( <[ _ := _ ]> _ !! _ = Some _); rewrite list_lookup_insert_Some => -[?|[??]]; [ naive_solver |].
      all: revert select (_ ∈ _); revert select (∀ y, y ∈ _ → _); rewrite rotate_take_insert ?length_insert; [|lia];
        case_decide;[|naive_solver lia].
      + move => ? /(list_elem_of_insert1 _ _ _ _)[?|?]; subst; destruct ir'; naive_solver.
      + move => Hx Hin' Hx'. apply: (Hx _ _ Hx'). apply: list_elem_of_insert2' => //.
        { rewrite lookup_take // lookup_rotate_l//. }
        move => ?. subst. destruct ir; [|naive_solver..].
        opose proof* (Hinv2 key' i) as Hi => //. move: Hi => /probe_ref_lookup[_ [_ [_ ]]]. by apply.
  Qed.

  (* used by automation *)
  Lemma fsm_invariant_insert key ty mp n items ir:
    fsm_invariant mp items →
    probe_ref key items = Some (n, ir) →
    fsm_invariant (<[key:=ty]> mp) (<[n:=Entry key ty]> items).
  Proof. move => ??. by apply: fsm_invariant_partial_alter. Qed.

  (* used by automation *)
  Lemma fsm_invariant_alter key ty mp n items ir ir':
    fsm_invariant mp items →
    probe_ref key items = Some (n, ir) →
    ir' = item_ref_set_ty ir ty →
    fsm_invariant (alter (λ _, ty) key mp) (<[n:=ir']> items).
  Proof.
    move => Hinv Hprobe ->. move: (Hprobe) => /probe_ref_lookup/=[? [??]].
    apply: fsm_invariant_partial_alter => //; by destruct ir.
  Qed.

  (* used by automation *)
  Lemma fsm_invariant_delete key mp n items ir ir':
    fsm_invariant mp items →
    probe_ref key items = Some (n, ir) →
    item_ref_to_ty ir' = None →
    item_ref_to_key ir' = Some key ∨ item_ref_to_key ir' = item_ref_to_key ir →
    fsm_invariant (delete key mp) (<[n:=ir']> items).
  Proof.
    move => ? Hprobe ??. move: (Hprobe) => /probe_ref_lookup[? [?[??]]].
    apply: fsm_invariant_partial_alter => //; destruct ir, ir'; naive_solver.
  Qed.

  Global Instance simpl_lookup_fsm_map_and mp key items n ir o `{!TCFastDone (fsm_invariant mp items)} `{!TCFastDone (probe_ref key items = Some (n, ir))}:
      SimplBothRel (=) (mp !! key) o (item_ref_to_ty ir = o).
  Proof. unfold TCFastDone in *. by rewrite (fsm_invariant_lookup _ items _ n ir (item_ref_to_ty ir)). Qed.

  Global Instance simpl_fsm_invariant_and mp1 mp2 items `{!IsEx mp1} `{!TCFastDone (fsm_invariant mp2 items)}:
    SimplAndUnsafe (fsm_invariant mp1 items) (mp1 = mp2) | 50.
  Proof. unfold TCFastDone in *. by move => ->. Qed.

  Global Instance simpl_and_fsm_invariant_alter key ty mp n items ir ir':
    TCFastDone (probe_ref key items = Some (n, ir)) →
    SimplAndUnsafe
      (fsm_invariant (alter (λ _, ty) key mp) (<[n:=ir']> items))
      (fsm_invariant mp items ∧ ir' = item_ref_set_ty ir ty).
  Proof. rewrite /TCFastDone/SimplAndUnsafe => ? [??]. by apply: fsm_invariant_alter. Qed.


  Definition fsm_copy_entries (items : list item_ref) (i : nat) : gmap Z type :=
    list_to_map (im←reverse (take i items); if im is Entry key ty then [(key, ty)] else []).


  Lemma fsm_copy_entries_id mp items i :
    fsm_invariant mp items →
    i = length items →
    fsm_copy_entries items i = mp.
  Proof.
    unfold fsm_copy_entries. move => [Hinv1 Hinv2] ->. apply map_eq => k. apply option_eq => ty.
    rewrite Hinv1 firstn_all -elem_of_list_to_map'; [| move => ?];
      rewrite !elem_of_list_bind; setoid_rewrite elem_of_reverse. 2: {
      move => [[|??|?]] [? Hin1] [[|??|?]] [? Hin2]; set_unfold => //. destruct_or!. simplify_eq.
      move: Hin1 Hin2 => /probe_ref_find_entry[//|??] /probe_ref_find_entry[//|??]. by simplify_eq.
    }
    split.
    - move => [[|? ?|?]]; set_unfold => -[H1 ?]//. destruct_or!. simplify_eq. by apply: probe_ref_find_entry.
    - move => [n /probe_ref_lookup]/=[/(elem_of_list_lookup_2 _ _ _)? ?]. eexists (Entry k ty). set_solver.
  Qed.


  Lemma fsm_copy_entries_not_add items i ir:
    items !! i = Some ir →
    (if ir is Entry _ _ then False else True) →
    fsm_copy_entries items (i + 1) = fsm_copy_entries items i.
  Proof.
    unfold fsm_copy_entries. move => Hl Hir. f_equal.
    rewrite -take_take_drop reverse_app bind_app /= (drop_S _ ir) //= app_nil_r.
    by destruct ir.
  Qed.

  Lemma fsm_copy_entries_add items i key ty:
    items !! i = Some (Entry key ty) →
    fsm_copy_entries items (i + 1) = <[key:=ty]> (fsm_copy_entries items i).
  Proof.
    unfold fsm_copy_entries. move => Hl.
    rewrite -take_take_drop reverse_app bind_app /= (drop_S _ (Entry key ty)) //= app_nil_r.
  Qed.

End defs.

Global Typeclasses Opaque probe_ref_go fsm_invariant probe_ref fsm_copy_entries.
Global Opaque fsm_copy_entries slot_for_key_ref.

Ltac enrich_context_hook ::=
  repeat match goal with
         | |- context C [ rotate_nat_add ?s ?o ?e ] =>
           let G := context C[enrich_marker rotate_nat_add s o e] in
           change_no_check G;
           try have ?:=rotate_nat_add_lt s o e ltac:(lia)
         end.
