From refinedc.typing Require Import typing.
Set Default Proof Using "Type".

Lemma same_length_lookup {A B} (l1 : list A) (l2 : list B) (i : nat):
  length l1 = length l2 → is_Some (l1 !! i) ↔ is_Some (l2 !! i).
Proof.
  move => Hlen. by rewrite lookup_lt_is_Some lookup_lt_is_Some Hlen.
Qed.

Lemma same_length_lookup_Some {A B} (l1 : list A) (l2 : list B) (i : nat) (v : A):
  length l1 = length l2 → l1 !! i = Some v → is_Some (l2 !! i).
Proof.
  move => Hlen H. by eapply same_length_lookup.
Qed.

Lemma StronglySorted_app {A} {R : A → A → Prop} `{!Transitive R} l1 l2 :
  (∀ x y, x ∈ l1 → y ∈ l2 → R x y) →
  StronglySorted R l1 → StronglySorted R l2 → StronglySorted R (l1 ++ l2).
Proof.
  move => H Hl1 Hl2. induction l1 as [|x l1 IH]; first done.
  apply StronglySorted_inv in Hl1 as [Hl1 HRx].
  opose proof* IH; [ by set_solver | exact | rewrite /=; clear IH ].
  constructor; first done. apply Forall_app; split; first done.
  apply Forall_forall; by set_solver.
Qed.

Lemma StronglySorted_insert_middle {A} {R : A → A → Prop} `{!Transitive R} l1 l2 x :
  (∀ y, y ∈ l1 → R y x) → (∀ y, y ∈ l2 → R x y) →
  StronglySorted R l1 → StronglySorted R l2 → StronglySorted R (l1 ++ x :: l2).
Proof.
  move => Hxl Hxr Hl1 Hl2. apply StronglySorted_app; try done.
  - intros x1 x2 Hx1 Hx2. apply elem_of_cons in Hx2 as []; first by set_solver.
    transitivity x; [ by apply Hxl | by apply Hxr ].
  - constructor; first done. apply Forall_forall; by set_solver.
Qed.

Lemma drop_elem_of {A : Type} (x : A) (n : nat) (l : list A) :
  x ∈ drop n l ↔ (∃ i, (n ≤ i)%nat ∧ l !! i = Some x).
Proof.
  rewrite elem_of_list_lookup. split.
  - intros [i H]. rewrite lookup_drop in H.
    exists (n + i)%nat. split; [ by lia | done ].
  - intros [i [H1 H2]]. exists (i - n)%nat.
    rewrite lookup_drop -H2. f_equal. by lia.
Qed.

Lemma StronglySorted_take {A} {R : A → A → Prop} (l : list A) (i : nat) :
  StronglySorted R l → StronglySorted R (take i l).
Proof.
  move => H. rewrite -(take_drop i l) in H.
  by apply StronglySorted_app_1_l in H.
Qed.

Lemma StronglySorted_drop {A} {R : A → A → Prop} (l : list A) (i : nat) :
  StronglySorted R l → StronglySorted R (drop i l).
Proof.
  move => H. rewrite -(take_drop i l) in H.
  by apply StronglySorted_app_1_r in H.
Qed.

Lemma StronglySorted_insert_drop_take {A} {R : A → A → Prop} `{!Transitive R} (l : list A) i x :
  (∀ k, (k < i)%nat → from_option (λ y, R y x) True (l !! k)) →
  from_option (λ y, R x y) True (l !! i) →
  StronglySorted R l →
  StronglySorted R (take i l ++ x :: drop i l).
Proof.
  move => Hl Hr Hs. apply StronglySorted_insert_middle.
  - move => y /elem_of_take [iy [Hy1 Hy2]]. move: (Hl iy Hy2). by rewrite Hy1.
  - move => y Hy. destruct (l !! i) eqn:HEq.
    * rewrite -(take_drop i l) in Hs. apply StronglySorted_app_1_r in Hs.
      erewrite drop_S in Hy, Hs; try done. apply StronglySorted_inv in Hs as [_ Hs].
      simpl in *. apply elem_of_cons in Hy as []; first by simplify_eq.
      transitivity a; first done. eapply Forall_forall in Hs; done.
    * apply drop_elem_of in Hy as [iy [Hy1 Hy2]].
      apply lookup_ge_None in HEq. assert (l !! iy = None); last by simplify_eq.
      apply lookup_ge_None. lia.
  - by apply StronglySorted_take.
  - by apply StronglySorted_drop.
Qed.

Lemma last_is_snoc {A} (l : list A) (x : A) :
  last l = Some x ↔ ∃ l', l = l' ++ [x].
Proof.
  split.
  - case l using rev_ind; first done. rewrite last_snoc.
    move => H. exists l. by simplify_eq.
  - intros [l' ->]. by rewrite last_snoc.
Qed.

Lemma last_is_lookup_last {A} (l : list A) :
  last l = l !! (length l - 1)%nat.
Proof.
  case l using rev_ind; first done.
  rewrite last_snoc length_app /=.
  assert (length l + 1 - 1 = length l)%nat as -> by lia.
  symmetry. by apply list_lookup_middle.
Qed.

Lemma StronglySorted_last_lt {A} {R : A → A → Prop} `{!StrictOrder R} (l : list A) x y :
  StronglySorted R l → x ∈ l → x ≠ y → last l = Some y → R x y.
Proof.
  move => Hs Hx Hne Hl. apply last_is_snoc in Hl as [prefix ->].
  apply elem_of_app in Hx as [Hx | Hx]; last by set_solver.
  eapply StronglySorted_app_1_elem_of; [ done | done | by set_solver ].
Qed.

Lemma StronglySorted_lookup_index_lt {A} {R : A → A → Prop} `{!StrictOrder R} l i1 i2 x1 x2 :
   StronglySorted R l → l !! i1 = Some x1 → l !! i2 = Some x2 → R x1 x2 → (i1 < i2)%nat.
Proof.
  move => HSS H1 H2 HR.
  assert (¬ i2 ≤ i1)%nat; last by lia.
  move => /Nat.lt_eq_cases [H|H]; last first.
  { assert (x1 = x2) as Heq by naive_solver. by apply (@irreflexive_eq _ R _ _ _ Heq). }
  apply (asymmetry HR). move: (take_drop (S i2) l) => Heq. rewrite -Heq in HSS.
  apply (StronglySorted_app_1_elem_of _ _ _ _ _ HSS).
  - apply elem_of_take. exists i2. split; [ done | lia ].
  - apply drop_elem_of. exists i1. split; [ lia | done ].
Qed.

Lemma StronglySorted_strict_NoDup {A} {R : A → A → Prop} `{!Irreflexive R} l :
  StronglySorted R l → NoDup l.
Proof.
  induction l as [|x l IH]; first by rewrite NoDup_nil.
  move => H. apply StronglySorted_inv in H as [H1 H2].
  apply NoDup_cons. split; last by apply IH. intros H.
  assert (R x x) as HRx by by apply (Forall_forall (R x) l).
  assert (¬ R x x) by by apply irreflexive_eq. done.
Qed.

Lemma lookup_zip {A B} (l1 : list A) (l2 : list B) (i : nat) (x : A) (y : B) :
  zip l1 l2 !! i = Some (x, y) ↔ l1 !! i = Some x ∧ l2 !! i = Some y.
Proof.
  revert l1 l2; induction i as [|i IH] => l1 l2; case l1; case l2; by naive_solver.
Qed.

Lemma elem_of_zip {A B} (l1 : list A) (l2 : list B) (x : A) (y : B) :
  (∃ i, l1 !! i = Some x ∧ l2 !! i = Some y) ↔ (x, y) ∈ zip l1 l2.
Proof.
  split.
  - move => [i H]. apply lookup_zip in H. apply elem_of_list_lookup. by exists i.
  - move => /elem_of_list_lookup [i H]. exists i. by apply lookup_zip.
Qed.

Lemma lookup_list_to_map_zip_None {V : Type} (ks : list Z) (vs : list V) (k : Z) :
  k ∉ ks → (list_to_map (zip ks vs) : gmap Z V) !! k = None.
Proof.
  revert vs; induction ks as [|j ks IH] => /= vs Hk //. move: vs => [|v vs] /= //.
  rewrite lookup_insert_ne; [ apply IH | .. ]; by set_solver.
Qed.

Lemma union_list_lookup_None {V} (l : list (gmap Z V)) (k : Z) :
  (⋃ l) !! k = None ↔ ∀ m, m ∈ l → m !! k = None.
Proof.
  induction l as [|? ? IH] => /=.
  - rewrite lookup_empty. split; last done. move => _ m Hm. by apply elem_of_nil in Hm.
  - split.
    + move => H m Hm. apply lookup_union_None in H as [H1 H2].
      apply elem_of_cons in Hm as [-> | Hm]; first done.
      by eapply IH in H2.
    + move => H. apply lookup_union_None. split.
      * apply H. set_solver.
      * apply IH. move => m Hm. apply H. set_solver.
Qed.

Lemma union_list_app {V} (l1 l2 : list (gmap Z V)) : ⋃ (l1 ++ l2) = ⋃ l1 ∪ ⋃ l2.
Proof.
  induction l1 as [|? ? IH] => /=; by [ rewrite left_id_L | rewrite IH assoc_L ].
Qed.

Lemma lookup_fmap_gmap {A B} (f : A → B) (m : gmap Z A) (i : Z) :
  (f <$> m) !! i = f <$> m !! i.
Proof.
  apply lookup_fmap.
Qed.

Notation array_p ly elts n :=
  (array ly (elts ++ replicate n (uninit ly)))
  (only parsing).

Section defs.
  Context `{typeG Σ}.

  Record btree_rfmt := BR {
    br_root : bool;       (* Is this the refinement of the root node? *)
    br_height : nat;      (* Expected height of the B-tree (0 for a leaf). *)
    br_min : Z;           (* Minimal key that can be stored in the B-tree (inclusive). *)
    br_max : Z;           (* Maximal key that can be stored in the B-tree (inclusive). *)
    br_map : gmap Z type; (* Map represented by the B-tree (this is the main part). *)
  }.

  (*
  Definition node_data := (nat * list Z * list type * list btree_rfmt)%type.
  *)

  Global Instance simpl_and_btree_rfmt r b h min_k max_k m :
    SimplAnd (r = {| br_root := b; br_height := h; br_min := min_k; br_max := max_k; br_map := m; |})
             (b = r.(br_root) ∧ h = r.(br_height) ∧ min_k = r.(br_min) ∧
                   max_k = r.(br_max) ∧ m = r.(br_map)).
  Proof. destruct r. split; naive_solver. Qed.

  Global Instance simple_ex_br_map_eq_empty (r : btree_rfmt) `{!IsEx r} :
    SimplAnd (br_map r = ∅) ((∃ b h min max, r = BR b h min max ∅)).
  Proof. split; destruct r; by naive_solver. Qed.

  Global Instance simpl_eq_cons_app {A} (x : A) (l1 l2 : list A) :
    SimplAndRel (=) (x :: l1) (l2 ++ l1) ([x] = l2).
  Proof.
    assert (x :: l1 = l2 ++ l1 → [x] = l2); last (split; by naive_solver). move => Heq.
    assert (length (x :: l1) = length (l2 ++ l1)) as Hlen by by rewrite Heq.
    rewrite /= length_app in Hlen. assert (length l2 = 1%nat) as ? by lia.
    destruct l2 as [|? l2]; first by inversion H0.
    destruct l2 as [|? l2]; last by inversion H0.
    by inversion Heq.
  Qed.

  (* The arguments denote the following:
      - [o] is the order of the B-tree.
      - [r] is the refinement of the B-tree (including the map).
      - [n] is the number of keys the current node.
      - [kv] is the list of keys stored directly in the current node (in order).
      - [vs] gives the values corresponding to the keys of [ks].
      - [cs] represents the the refinement of the children of the current node.
        For each of them, it contains an optional height, the minimum key it may
        store, its contents, and the maximum key it can store.
      - [cs_h] is the height of all children.
  *)
  Definition btree_invariant (o : nat) (r : btree_rfmt) (n : nat) (ks : list Z)
      (vs : list type) (cs : list btree_rfmt) :=
    if bool_decide (br_map r ≠ ∅) then
      (* Constraints on the number of keys and children. *)
      n = length ks ∧ n = length vs ∧ (n < o)%nat ∧ length cs = (n + 1)%nat ∧
      (if br_root r then True else (o+o-1) / 2 ≤ n + 1)%nat ∧
      (* Constraints on the height. *)
      (br_height r > 0)%nat ∧
      (∀ i d, cs !! i = Some d → br_height d = br_height r - 1)%nat ∧
      (* The keys are sorted. *)
      StronglySorted (<) ks ∧
      (* Bound on the elements. *)
      (∀ k, is_Some (br_map r !! k) → br_min r ≤ k ∧ k ≤ br_max r) ∧
      (* Lower bound for the keys in children. *)
      (∀ d, cs !! 0%nat = Some d → br_min d = br_min r) ∧
      (∀ i d, i ≠ 0%nat → cs !! i = Some d → (ks !! (i - 1)%nat) = Some (br_min d - 1)) ∧
      (* Upper bound for the keys in children. *)
      (∀ d, cs !! n = Some d → br_max d = br_max r) ∧
      (∀ i d, i ≠ n → cs !! i = Some d → ks !! i = Some (br_max d + 1)) ∧
      (* Bounds for the children. *)
      (∀ i d, cs !! i = Some d → ∀ k, is_Some (br_map d !! k) → br_min d ≤ k ∧ k ≤ br_max d) ∧
      (* Contents of the map. *)
      br_map r = (list_to_map (zip ks vs)) ∪ ⋃ (br_map <$> cs)
    else
      n = 0%nat ∧ ks = [] ∧ vs = [] ∧ cs = [] ∧
      br_height r = 0%nat.

  Global Instance simpl_and_btree_invariant_empty o r n ks vs cs :
    TCFastDone (br_map r = ∅) →
    SimplAnd (btree_invariant o r n ks vs cs)
             (n = 0%nat ∧ ks = [] ∧ vs = [] ∧ cs = [] ∧ br_height r = 0%nat).
  Proof. rewrite /TCFastDone/btree_invariant => ?. rewrite bool_decide_false //; naive_solver. Qed.

  Lemma btree_invariant_height_empty {o r1 r2 n1 n2 ks1 ks2 vs1 vs2 cs1 cs2} :
    btree_invariant o r1 n1 ks1 vs1 cs1 →
    btree_invariant o r2 n2 ks2 vs2 cs2 →
    br_height r1 = br_height r2 →
    br_map r1 ≠ ∅ ↔ br_map r2 ≠ ∅.
  Proof.
    rewrite /btree_invariant.
    destruct (decide (br_map r1 ≠ ∅)).
    - rewrite bool_decide_true //.
      destruct (decide (br_map r2 ≠ ∅)).
      + rewrite bool_decide_true //.
      + rewrite bool_decide_false //. by lia.
    - rewrite bool_decide_false //.
      destruct (decide (br_map r2 ≠ ∅)).
      + rewrite bool_decide_true //. by lia.
      + rewrite bool_decide_false //.
  Qed.

  Lemma btree_invariant_has_key_non_empty {o r n ks vs cs i} :
    btree_invariant o r n ks vs cs → is_Some (ks !! i) → br_map r ≠ ∅.
  Proof.
    move => Hinv Hi. rewrite /btree_invariant in Hinv.
    destruct (decide (br_map r ≠ ∅)); first done.
    rewrite bool_decide_false in Hinv; last by naive_solver.
    destruct_and!. simplify_eq. by inversion Hi.
  Qed.

  Lemma btree_invariant_has_child_non_empty {o r n ks vs cs i} :
    btree_invariant o r n ks vs cs → is_Some (cs !! i) → br_map r ≠ ∅.
  Proof.
    move => Hinv Hi. rewrite /btree_invariant in Hinv.
    destruct (decide (br_map r ≠ ∅)); first done.
    rewrite bool_decide_false in Hinv; last by naive_solver.
    destruct_and!. simplify_eq. by inversion Hi.
  Qed.

  Lemma btree_invariant_in_keys_not_None {o r n ks vs cs i k} :
    btree_invariant o r n ks vs cs → ks !! i = Some k → br_map r !! k ≠ None.
  Proof.
    move => Hinv Hk. assert (br_map r ≠ ∅) as Hmap.
    { eapply btree_invariant_has_key_non_empty; naive_solver. }
    rewrite /btree_invariant bool_decide_true in Hinv => //.
    destruct Hinv as (Hlen&->&_&_&_&_&_&HSS&_&_&_&_&_&_&->).
    apply not_eq_None_Some. have: (is_Some (vs !! i)) => [|[ty Hv]].
    { apply lookup_lt_is_Some. rewrite Hlen. apply lookup_lt_is_Some. by exists k. }
    have: (is_Some ((((list_to_map (zip ks vs)) : gmap Z type)) !! k)) => [|[v Hzip]].
    { exists ty. apply elem_of_list_to_map; [ .. | apply elem_of_zip; by exists i ].
      rewrite fst_zip; last by lia. apply: (@StronglySorted_strict_NoDup _ (<)) => //. }
    exists v. by apply lookup_union_Some_l.
  Qed.

  Lemma btree_invariant_keys_in_range {o r n ks vs cs} :
    btree_invariant o r n ks vs cs → ∀ k, k ∈ ks → br_min r ≤ k ≤ br_max r.
  Proof.
    move => Hinv k Hk. apply elem_of_list_lookup in Hk as [i Hk]. assert (br_map r ≠ ∅).
    { by eapply btree_invariant_has_key_non_empty. }
    rewrite /btree_invariant bool_decide_true // /= in Hinv.
    destruct Hinv as (Hlen&->&_&_&_&_&_&HSS&HB&_&_&_&_&_&Heq). apply HB.
    assert (is_Some (vs !! i)) as [v Hv] by by eapply same_length_lookup_Some.
    rewrite Heq. assert ((list_to_map (zip ks vs) : gmap Z type) !! k = Some v).
    { apply elem_of_list_to_map.
      - rewrite fst_zip; last by lia.
        by apply (StronglySorted_strict_NoDup _ HSS).
      - apply elem_of_zip. by exists i. }
    exists v. by apply lookup_union_Some_l.
  Qed.

  Lemma btree_invariant_in_range_child {o r n ks vs cs i k d} :
    btree_invariant o r n ks vs cs →
    StronglySorted (<) (take i ks ++ k :: drop i ks) →
    br_min r ≤ k ≤ br_max r → cs !! i = Some d →
    br_min d ≤ k ≤ br_max d.
  Proof.
    move => Hinv HSS [Hmr HMr] Hd. assert (br_map r ≠ ∅) as Hmap.
    { eapply btree_invariant_has_child_non_empty; naive_solver. }
    rewrite /btree_invariant bool_decide_true in Hinv => //.
    destruct Hinv as (Hlen&->&_&Hcs&_&_&?&?&?&Hm0&Hm&HMlast&HM&_). split.
    - destruct (decide (i = 0%nat)) as [->|Hi_not_0]; first by move: (Hm0 d Hd) => ->.
      move: (Hm i d Hi_not_0 Hd) => P.
      rewrite cons_middle app_assoc in HSS. apply StronglySorted_app_1_l in HSS.
      assert (br_min d - 1 < k); last by lia.
      assert (br_min d - 1 ∈ take i ks).
      { apply elem_of_list_lookup. exists (i - 1)%nat. rewrite lookup_take //. by lia. }
      apply (StronglySorted_last_lt _ _ _ HSS); [ apply elem_of_app; by left | .. | by rewrite last_snoc ].
      eapply (StronglySorted_app_1_elem_of _ _ _ (br_min d - 1) k) in HSS; [ lia | done | by set_solver ].
    - destruct (decide (i = length vs)) as [->|Hi]; first by rewrite HMlast.
      move: (HM i d Hi Hd) => P.
      apply StronglySorted_app_1_r in HSS. apply StronglySorted_inv in HSS as [HSS Hlt].
      assert (k < br_max d + 1); last by lia.
      assert (br_max d + 1 ∈ drop i ks).
      { apply elem_of_list_lookup. exists 0%nat. by rewrite lookup_drop // -plus_n_O. }
      by apply (Forall_forall (Z.lt k) (drop i ks)).
  Qed.

  Lemma btree_invariant_lookup_child {o r n ks vs cs i k d} :
    btree_invariant o r n ks vs cs →
    StronglySorted (<) (take i ks ++ k :: drop i ks) →
    cs !! i = Some d → k ∉ ks →
    br_map r !! k = br_map d !! k.
  Proof.
    move => Hinv HSS Hd Hk. assert (br_map r ≠ ∅) as Hmap.
    { eapply btree_invariant_has_child_non_empty; naive_solver. }
    rewrite /btree_invariant bool_decide_true in Hinv => //.
    destruct Hinv as (Hlen1&->&_&Hlen2&_&_&_&HSSks&_&Hm1&Hm2&HM1&HM2&HB&Hmdef).
    rewrite Hmdef.
    assert (⋃ (br_map <$> cs) !! k = br_map d !! k) as <-; last first.
    { move: (lookup_list_to_map_zip_None _ vs _ Hk) => Hks. by apply lookup_union_r. }
    rewrite -(take_drop_middle _ _ _ Hd) fmap_app fmap_cons.
    destruct (decide (i = length ks)) as [->|Hine].
    - assert (S (length ks) = length cs) as -> by lia. rewrite skipn_all /=.
      assert (∃ cs', cs = cs' ++ [d]) as [cs' ->].
      { exists (take (length ks) cs).
        rewrite -[X in X = _](take_drop_middle _ _ _ Hd).
        do 2 f_equal. apply skipn_all2. lia. }
      rewrite length_app /= in Hlen2.
      assert (length cs' = length ks) as Hlen3.
      { destruct (decide (length ks = length cs')); by lia. }
      clear Hlen2. rename Hlen3 into Hlen2.
      rewrite (take_app_length' cs' [d]); last done.
      assert (⋃ (br_map <$> cs') !! k = None) as Hl.
      { apply union_list_lookup_None => m Hm.
        apply elem_of_list_lookup_1 in Hm as [j Hm].
        rewrite list_lookup_fmap in Hm.
        assert (∃ dj, cs' !! j = Some dj) as [dj Hdj].
        { destruct (cs' !! j) eqn:HEq; [ by eauto | by inversion Hm ]. }
        assert (j ≠ length vs) as Hne.
        { move => Heq. rewrite Heq Hlen1 -Hlen2 in Hdj. apply lookup_lt_Some in Hdj. lia. }
        assert (∃ kj, ks !! j = Some kj) as [kj Hkj].
        { destruct (ks !! j) eqn:HEq; [ by eauto | .. ].
          apply lookup_ge_None in HEq. apply lookup_lt_Some in Hdj. lia. }
        assert ((cs' ++ [d]) !! j = Some dj) as Hdj'.
        { rewrite lookup_app_l //. rewrite Hlen1 in Hne. apply lookup_lt_Some in Hkj. lia. }
        move: (HM2 j dj Hne Hdj') => HH. rewrite Hdj /= in Hm. inversion_clear Hm.
        assert (br_max dj < kj) as HHH. { simplify_eq. lia. }
        apply eq_None_not_Some => HSome.
        move: (HB j dj Hdj' k HSome) => [HS1 HS2].
        assert (k < kj) by lia.
        assert (kj ∈ take (length ks) ks).
        { apply elem_of_take. eexists; split; first done. rewrite -Hlen1. apply lookup_lt_Some in Hdj. lia. }
        rewrite cons_middle app_assoc in HSS.
        apply StronglySorted_app_1_l in HSS.
        eapply (StronglySorted_last_lt _ kj k) in HSS;
          [ lia | set_solver | lia | by rewrite last_snoc ]. }
      by rewrite union_list_app lookup_union_r // /= right_id_L.
    - assert (⋃ (br_map <$> drop (S i) cs) !! k = None) as Hr.
      { apply union_list_lookup_None => m Hm.
        apply elem_of_list_lookup_1 in Hm as [j Hm].
        rewrite list_lookup_fmap lookup_drop in Hm.
        assert (∃ dj, cs !! (S i + j)%nat = Some dj) as [dj Hdj].
        { destruct (cs !! (S i + j)%nat) eqn:HEq; [ by eauto | by inversion Hm ]. }
        rewrite Hdj /= in Hm. simplify_eq. apply eq_None_not_Some.
        intros Hconstr. eapply HB in Hconstr as [Hconstr _]; last exact.
        assert (∃ kjmo, ks !! (i + j)%nat = Some kjmo) as [kjmo Hkjmo].
        { destruct (ks !! (i + j)%nat) eqn:HEq; [ by eauto | .. ].
          apply lookup_ge_None in HEq. apply lookup_lt_Some in Hdj. lia. }
        assert ((S i + j)%nat ≠ 0%nat) as Hne by lia.
        move: (Hm2 (S i + j)%nat dj Hne Hdj).
        assert (S i + j - 1 = i + j)%nat as -> by lia. move => HH.
        assert (kjmo < k). { rewrite Hkjmo in HH. simplify_eq. lia. }
        assert (kjmo ∈ drop i ks). { apply drop_elem_of. eexists; split; last done. lia. }
        apply StronglySorted_app_1_r in HSS. apply StronglySorted_inv in HSS as [_ XX].
        assert (k < kjmo); last by lia.
        move: XX => /Forall_forall => XX. apply XX. done. }
      assert (⋃ (br_map <$> take i     cs) !! k = None) as Hl.
      { clear Hr. apply union_list_lookup_None => m Hm.
        apply elem_of_list_lookup_1 in Hm as [j Hm].
        rewrite list_lookup_fmap in Hm.
        assert (j < i)%nat.
        { apply mk_is_Some in Hm. move: Hm => /fmap_is_Some /lookup_lt_is_Some.
          rewrite length_take. lia. }
        rewrite lookup_take in Hm; last done.
        assert (∃ dj, cs !! j = Some dj) as [dj Hdj].
        { destruct (cs !! j) eqn:HEq; [ by eauto | by inversion Hm ]. }
        destruct (decide (j = length vs)) as [Heq|Hne].
        { rewrite Hdj /= in Hm. apply lookup_lt_Some in Hd. lia. }
        rewrite Hdj /= in Hm. simplify_eq. apply eq_None_not_Some.
        intros Hconstr. eapply HB in Hconstr as [_ Hconstr]; last exact.
        assert (∃ kj, ks !! j = Some kj) as [kj Hkj].
        { destruct (ks !! j) eqn:HEq; [ by eauto | .. ].
          apply lookup_ge_None in HEq. apply lookup_lt_Some in Hdj. lia. }
        move: (HM2 j dj Hne Hdj) => HH.
        assert (k < kj). { simplify_eq. lia. }
        assert (kj ∈ take i ks). { apply elem_of_take. eexists; split; first done. lia. }
        rewrite cons_middle app_assoc in HSS.
        apply StronglySorted_app_1_l in HSS.
        eapply (StronglySorted_last_lt _ kj k) in HSS;
          [ lia | set_solver | lia | by rewrite last_snoc ]. }
      rewrite union_list_app lookup_union_r // /=.
      destruct (br_map d !! k) eqn:?;
      by [ apply lookup_union_Some_l | apply lookup_union_None ].
  Qed.

  Definition BRroot (h : nat) (m : gmap Z type) : btree_rfmt := {|
    br_root := true;
    br_height := h;
    br_min := min_int i32;
    br_max := max_int i32;
    br_map := m;
  |}.

  Definition non_root (r : btree_rfmt) : btree_rfmt := {|
    br_root := false;
    br_height := r.(br_height);
    br_min := r.(br_min);
    br_max := r.(br_max);
    br_map := r.(br_map);
  |}.

  Definition make_sp (p : loc) (k : Z) (m : gmap Z type) :=
    alter (λ _, place p)%I k m.
End defs.

Global Typeclasses Opaque btree_invariant.
