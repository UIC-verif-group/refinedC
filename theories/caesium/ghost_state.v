From stdpp Require Import coPset.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export tactics.
From caesium Require Export lang.
Set Default Proof Using "Type".
Import uPred.

Definition lock_stateR : cmra :=
  csumR (exclR unitO) natR.

Definition heap_cellR : cmra :=
  prodR (prodR fracR lock_stateR) (agreeR (prodO alloc_idO mbyteO)).

Definition heapUR : ucmra :=
  gmapUR addr heap_cellR.

Class heapG Σ := HeapG {
  heap_heap_inG              :: inG Σ (authR heapUR);
  heap_heap_name             : gname;
  heap_alloc_meta_map_inG   :: ghost_mapG Σ alloc_id (Z * nat * alloc_kind);
  heap_alloc_meta_map_name  : gname;
  heap_alloc_alive_map_inG  :: ghost_mapG Σ alloc_id bool;
  heap_alloc_alive_map_name : gname;
  heap_fntbl_inG             :: ghost_mapG Σ addr function;
  heap_fntbl_name            : gname;
}.

Definition to_lock_stateR (lk : lock_state) : lock_stateR :=
  match lk with RSt n => Cinr n | WSt => Cinl (Excl ()) end.

Definition to_heap_cellR (hc : heap_cell) : heap_cellR :=
  (1%Qp, to_lock_stateR hc.(hc_lock_state), to_agree (hc.(hc_alloc_id), hc.(hc_value))).

Definition to_heapUR : heap → heapUR :=
  fmap to_heap_cellR.

Definition to_alloc_metaR (al : allocation) : (Z * nat * alloc_kind) :=
  (al.(al_start), al.(al_len), al.(al_kind)).

Definition to_alloc_meta_map : allocs → gmap alloc_id (Z * nat * alloc_kind) :=
  fmap to_alloc_metaR.

Definition to_alloc_alive_map : allocs → gmap alloc_id bool :=
  fmap al_alive.

Section definitions.
  Context `{!heapG Σ} `{!FUpd (iProp Σ)}.

  (** * Allocation stuff. *)

  (** [alloc_meta id al] persistently records the information that allocation
  with identifier [id] has a range corresponding to that of [a]. *)
  Definition alloc_meta_def (id : alloc_id) (al : allocation) : iProp Σ :=
    id ↪[ heap_alloc_meta_map_name ]□ to_alloc_metaR al.
  Definition alloc_meta_aux : seal (@alloc_meta_def). by eexists. Qed.
  Definition alloc_meta := unseal alloc_meta_aux.
  Definition alloc_meta_eq : @alloc_meta = @alloc_meta_def :=
    seal_eq alloc_meta_aux.

  Global Instance allocs_range_pers id al : Persistent (alloc_meta id al).
  Proof. rewrite alloc_meta_eq. by apply _. Qed.

  Global Instance allocs_range_tl id al : Timeless (alloc_meta id al).
  Proof. rewrite alloc_meta_eq. by apply _. Qed.

  (** [loc_in_bounds l n] persistently records the information that location
  [l] and any of its positive offset up to [n] (included) are in range of the
  allocation [l] originated from (or one past the end of it). It also records
  the fact that this allocation is in bounds of allocatable memory. *)
  Definition loc_in_bounds_def (l : loc) (n : nat) : iProp Σ :=
    ∃ (id : alloc_id) (al : allocation),
      ⌜l.1 = ProvAlloc (Some id)⌝ ∗ ⌜al.(al_start) ≤ l.2⌝ ∗ ⌜l.2 + n ≤ al_end al⌝ ∗
      ⌜allocation_in_range al⌝ ∗ alloc_meta id al.
  Definition loc_in_bounds_aux : seal (@loc_in_bounds_def). by eexists. Qed.
  Definition loc_in_bounds := unseal loc_in_bounds_aux.
  Definition loc_in_bounds_eq : @loc_in_bounds = @loc_in_bounds_def :=
    seal_eq loc_in_bounds_aux.

  Global Instance loc_in_bounds_pers l n : Persistent (loc_in_bounds l n).
  Proof. rewrite loc_in_bounds_eq. by apply _. Qed.

  Global Instance loc_in_bounds_tl l n : Timeless (loc_in_bounds l n).
  Proof. rewrite loc_in_bounds_eq. by apply _. Qed.

  (** [alloc_alive id q] is a token witnessing the fact that the allocation
  with identifier [id] is still alive. *)
  Definition alloc_alive_def (id : alloc_id) (dq : dfrac) (a : bool) : iProp Σ :=
    id ↪[ heap_alloc_alive_map_name ]{dq} a.
  Definition alloc_alive_aux : seal (@alloc_alive_def). by eexists. Qed.
  Definition alloc_alive := unseal alloc_alive_aux.
  Definition alloc_alive_eq : @alloc_alive = @alloc_alive_def :=
    seal_eq alloc_alive_aux.

  Global Instance alloc_alive_tl id dq a : Timeless (alloc_alive id dq a).
  Proof. rewrite alloc_alive_eq. by apply _. Qed.

  (** [alloc_global l] is knowledge that the provenance of [l] is
  alive forever (i.e. corresponds to a global variable). *)
  Definition alloc_global_def (l : loc) : iProp Σ :=
    ∃ id, ⌜l.1 = ProvAlloc (Some id)⌝ ∗ alloc_alive id DfracDiscarded true.
  Definition alloc_global_aux : seal (@alloc_global_def). by eexists. Qed.
  Definition alloc_global := unseal alloc_global_aux.
  Definition alloc_global_eq : @alloc_global = @alloc_global_def :=
    seal_eq alloc_global_aux.

  Global Instance alloc_global_tl l : Timeless (alloc_global l).
  Proof. rewrite alloc_global_eq. by apply _. Qed.
  Global Instance alloc_global_pers l : Persistent (alloc_global l).
  Proof. rewrite alloc_global_eq /alloc_global_def alloc_alive_eq. by apply _. Qed.

  (** * Function table stuff. *)

  (** [fntbl_entry l f] persistently records the information that function
  [f] is stored at location [l]. NOTE: we use locations, but do not really
  store the code on the actual heap. *)
  Definition fntbl_entry_def (l : loc) (f: function) : iProp Σ :=
    ∃ a, ⌜l = fn_loc a⌝ ∗ a ↪[ heap_fntbl_name ]□ f.
  Definition fntbl_entry_aux : seal (@fntbl_entry_def). by eexists. Qed.
  Definition fntbl_entry := unseal fntbl_entry_aux.
  Definition fntbl_entry_eq : @fntbl_entry = @fntbl_entry_def :=
    seal_eq fntbl_entry_aux.

  Global Instance fntbl_entry_pers l f : Persistent (fntbl_entry l f).
  Proof. rewrite fntbl_entry_eq. by apply _. Qed.

  Global Instance fntbl_entry_tl l f : Timeless (fntbl_entry l f).
  Proof. rewrite fntbl_entry_eq. by apply _. Qed.

  (** Heap stuff. *)

  Definition heap_mapsto_mbyte_st (st : lock_state) (l : loc) (id : alloc_id)
                                  (q : Qp) (b : mbyte) : iProp Σ :=
    own heap_heap_name (◯ {[ l.2 := (q, to_lock_stateR st, to_agree (id, b)) ]}).

  Definition heap_mapsto_mbyte_def (l : loc) (q : Qp) (b : mbyte) : iProp Σ :=
    ∃ id, ⌜l.1 = ProvAlloc (Some id)⌝ ∗ heap_mapsto_mbyte_st (RSt 0) l id q b.
  Definition heap_mapsto_mbyte_aux : seal (@heap_mapsto_mbyte_def). by eexists. Qed.
  Definition heap_mapsto_mbyte := unseal heap_mapsto_mbyte_aux.
  Definition heap_mapsto_mbyte_eq : @heap_mapsto_mbyte = @heap_mapsto_mbyte_def :=
    seal_eq heap_mapsto_mbyte_aux.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v : val) : iProp Σ :=
    loc_in_bounds l (length v) ∗
    ([∗ list] i ↦ b ∈ v, heap_mapsto_mbyte (l +ₗ i) q b)%I.
  Definition heap_mapsto_aux : seal (@heap_mapsto_def). by eexists. Qed.
  Definition heap_mapsto := unseal heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    seal_eq heap_mapsto_aux.


  (** Token witnessing that [l] has an allocation identifier that is alive. *)
  Definition alloc_alive_loc_def (l : loc) : iProp Σ :=
    |={⊤, ∅}=> ((∃ id q, ⌜l.1 = ProvAlloc (Some id)⌝ ∗ alloc_alive id q true) ∨
               (∃ a q v, ⌜v ≠ []⌝ ∗ heap_mapsto (l.1, a) q v)).
  Definition alloc_alive_loc_aux : seal (@alloc_alive_loc_def). by eexists. Qed.
  Definition alloc_alive_loc := unseal alloc_alive_loc_aux.
  Definition alloc_alive_loc_eq : @alloc_alive_loc = @alloc_alive_loc_def :=
    seal_eq alloc_alive_loc_aux.

  (** * Freeable *)

  Definition freeable_def (l : loc) (n : nat) (k : alloc_kind) : iProp Σ :=
    ∃ id, ⌜l.1 = ProvAlloc (Some id)⌝ ∗ alloc_meta id {| al_start := l.2; al_len := n; al_alive := true; al_kind := k |} ∗
     alloc_alive id (DfracOwn 1) true.
  Definition freeable_aux : seal (@freeable_def). by eexists. Qed.
  Definition freeable := unseal freeable_aux.
  Definition freeable_eq : @freeable = @freeable_def :=
    seal_eq freeable_aux.

  (** * Authoritative parts and contexts. *)

  Definition heap_ctx (h : heap) : iProp Σ :=
    own heap_heap_name (● to_heapUR h).

  Definition alloc_meta_ctx (ub : allocs) : iProp Σ :=
    ghost_map_auth heap_alloc_meta_map_name 1 (to_alloc_meta_map ub).

  Definition alloc_alive_ctx (ub : allocs) : iProp Σ :=
    ghost_map_auth heap_alloc_alive_map_name 1 (to_alloc_alive_map ub).

  Definition fntbl_ctx (fns : gmap addr function) : iProp Σ :=
    ghost_map_auth heap_fntbl_name 1 fns.

  Definition heap_state_ctx (st : heap_state) : iProp Σ :=
    ⌜heap_state_invariant st⌝ ∗
    heap_ctx st.(hs_heap) ∗
    alloc_meta_ctx st.(hs_allocs) ∗
    alloc_alive_ctx st.(hs_allocs).

  Definition state_ctx (σ:state) : iProp Σ :=
    heap_state_ctx σ.(st_heap) ∗
    fntbl_ctx σ.(st_fntbl).
End definitions.

Global Typeclasses Opaque alloc_meta loc_in_bounds alloc_alive alloc_global
  fntbl_entry heap_mapsto_mbyte heap_mapsto alloc_alive_loc
  freeable.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : bi_scope.
Notation "l ↦{ q '}' ':' P" := (∃ v, l ↦{ q } v ∗ P v)%I
  (at level 20, q at level 50, format "l  ↦{ q '}' ':'  P") : bi_scope.
Notation "l ↦: P " := (∃ v, l ↦ v ∗ P v)%I
  (at level 20, format "l  ↦:  P") : bi_scope.

Definition heap_mapsto_layout `{!heapG Σ} (l : loc) (q : Qp) (ly : layout) : iProp Σ :=
  (∃ v, ⌜v `has_layout_val` ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗ l ↦{q} v).
Notation "l ↦{ q }| ly |" := (heap_mapsto_layout l q ly)
  (at level 20, q at level 50, format "l  ↦{ q }| ly |") : bi_scope.
Notation "l ↦| ly | " := (heap_mapsto_layout l 1%Qp ly)
  (at level 20, format "l  ↦| ly |") : bi_scope.

Section heap.
  Implicit Types h : heap.

  Lemma to_heapUR_valid h : ✓ to_heapUR h.
  Proof. intros a. rewrite lookup_fmap. by case (h !! a) => // -[?[]?]. Qed.

  Lemma lookup_to_heapUR_None h a :
    h !! a = None → to_heapUR h !! a = None.
  Proof. by rewrite /to_heapUR lookup_fmap=> ->. Qed.

  Lemma to_heapUR_insert a hc h :
    to_heapUR (<[a := hc]> h) = <[a := to_heap_cellR hc]> (to_heapUR h).
  Proof. by rewrite /to_heapUR fmap_insert. Qed.

  Lemma to_heapUR_delete h a :
    to_heapUR (delete a h) = delete a (to_heapUR h).
  Proof. by rewrite /to_heapUR fmap_delete. Qed.
End heap.

Section fntbl.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Lemma fntbl_entry_lookup t f fn :
    fntbl_ctx t -∗ fntbl_entry f fn -∗ ⌜∃ a, f = fn_loc a ∧ t !! a = Some fn⌝.
  Proof.
    rewrite fntbl_entry_eq.
    iIntros "Hctx (%a&->&Hentry)".
    iDestruct (ghost_map_lookup with "Hctx Hentry") as %?.
    by eauto.
  Qed.
End fntbl.

Section alloc_meta.
  Context `{!heapG Σ}.
  Implicit Types am : allocs.

  Lemma alloc_meta_mono id a1 a2 :
    alloc_same_range a1 a2 →
    a1.(al_kind) = a2.(al_kind) →
    alloc_meta id a1 -∗ alloc_meta id a2.
  Proof.
    destruct a1 as [????], a2 as [????] => -[/= <- <-] <-.
    rewrite alloc_meta_eq. iIntros "$".
  Qed.

  Lemma alloc_meta_agree id a1 a2 :
    alloc_meta id a1 -∗ alloc_meta id a2 -∗ ⌜alloc_same_range a1 a2⌝.
  Proof.
    destruct a1 as [????], a2 as [????]. rewrite alloc_meta_eq /alloc_same_range.
    iIntros "H1 H2". by iDestruct (ghost_map_elem_agree with "H1 H2") as %[=->->].
  Qed.

  Lemma alloc_meta_alloc am id al :
    am !! id = None →
    alloc_meta_ctx am ==∗
    alloc_meta_ctx (<[id := al]> am) ∗ alloc_meta id al.
  Proof.
    move => Hid. rewrite alloc_meta_eq. iIntros "Hctx".
    iMod (ghost_map_insert_persist with "Hctx") as "[? $]". { by rewrite lookup_fmap fmap_None. }
    by rewrite -fmap_insert.
  Qed.

  Lemma alloc_meta_to_loc_in_bounds l id (n : nat) al:
    l.1 = ProvAlloc (Some id) →
    al.(al_start) ≤ l.2 ∧ l.2 + n ≤ al_end al →
    allocation_in_range al →
    alloc_meta id al -∗ loc_in_bounds l n.
  Proof.
    iIntros (?[??]?) "Hr". rewrite loc_in_bounds_eq.
    iExists id, al. by iFrame "Hr".
  Qed.

  Lemma alloc_meta_lookup am id al :
    alloc_meta_ctx am -∗
    alloc_meta id al -∗
    ⌜∃ al', am !! id = Some al' ∧ alloc_same_range al al' ∧ al.(al_kind) = al'.(al_kind)⌝.
  Proof.
    rewrite alloc_meta_eq. iIntros "Htbl Hf".
    iDestruct (ghost_map_lookup with "Htbl Hf") as %Hlookup.
    iPureIntro. move: Hlookup. rewrite lookup_fmap fmap_Some => -[[????][?[???]]].
    by eexists _.
  Qed.

  Lemma alloc_meta_ctx_same_range am id al1 al2 :
    am !! id = Some al1 →
    alloc_same_range al1 al2 →
    al1.(al_kind) = al2.(al_kind) →
    alloc_meta_ctx am = alloc_meta_ctx (<[id := al2]> am).
  Proof.
    move => Hid [Heq1 Heq2] Heq3.
    rewrite /alloc_meta_ctx /to_alloc_meta_map fmap_insert insert_id; first done.
    rewrite lookup_fmap Hid /=. destruct al1, al2; naive_solver.
  Qed.

  Lemma alloc_meta_ctx_killed am id al :
    am !! id = Some al →
    alloc_meta_ctx am = alloc_meta_ctx (<[id := killed al]> am).
  Proof. move => ?. by apply: alloc_meta_ctx_same_range. Qed.
End alloc_meta.

Section alloc_alive.
  Context `{!heapG Σ}.
  Implicit Types am : allocs.

  Lemma alloc_alive_alloc am id al :
    am !! id = None →
    alloc_alive_ctx am ==∗
    alloc_alive_ctx (<[id := al]> am) ∗ alloc_alive id (DfracOwn 1) (al.(al_alive)).
  Proof.
    iIntros (?) "Hctx". rewrite alloc_alive_eq.
    iMod (ghost_map_insert with "Hctx") as "[? $]". { by rewrite lookup_fmap fmap_None. }
    by rewrite -fmap_insert.
  Qed.

  Lemma alloc_alive_lookup am id q a:
    alloc_alive_ctx am -∗ alloc_alive id q a -∗ ⌜∃ al, am !! id = Some al ∧ al.(al_alive) = a⌝.
  Proof.
    rewrite /alloc_alive_ctx alloc_alive_eq. iIntros "Hctx Ha".
    iDestruct (ghost_map_lookup with "Hctx Ha") as %Hlookup.
    iPureIntro. move: Hlookup. rewrite lookup_fmap fmap_Some. naive_solver.
  Qed.

  Lemma alloc_alive_kill am id al a:
    alloc_alive_ctx am -∗
    alloc_alive id (DfracOwn 1) a ==∗
    alloc_alive_ctx (<[id := killed al]> am) ∗ alloc_alive id (DfracOwn 1) false.
  Proof.
    rewrite alloc_alive_eq. iIntros "Hctx Ha".
    iMod (ghost_map_update with "Hctx Ha") as "[? $]".
    by rewrite /alloc_alive_ctx/to_alloc_alive_map fmap_insert.
  Qed.
End alloc_alive.

Section loc_in_bounds.
  Context `{!heapG Σ}.

  Lemma loc_in_bounds_split l n m :
    loc_in_bounds l n ∗ loc_in_bounds (l +ₗ n) m ⊣⊢ loc_in_bounds l (n + m).
  Proof.
    rewrite loc_in_bounds_eq. iSplit.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (id al Hl1 ???) "#H1".
      iDestruct "H2" as (?? Hl2 ? Hend ?) "#H2".
      move: Hl1 Hl2 => /= Hl1 Hl2. iExists id, al.
      destruct l. unfold al_end in *. simpl in *. simplify_eq.
      iDestruct (alloc_meta_agree with "H2 H1") as %[? <-].
      iFrame "H1". iPureIntro. rewrite /shift_loc /= in Hend. naive_solver lia.
    - iIntros "H". iDestruct "H" as (id al ????) "#H".
      iSplit; iExists id, al; iFrame "H"; iPureIntro; split_and! => //=; lia.
  Qed.

  Lemma loc_in_bounds_split_mul_S l n m :
    loc_in_bounds l n ∗ loc_in_bounds (l +ₗ n) (n * m) ⊣⊢ loc_in_bounds l (n * S m).
  Proof.
    have ->: (n * S m = n + n * m)%nat by lia.
    etrans; [ by apply loc_in_bounds_split | done ].
  Qed.

  Lemma loc_in_bounds_shorten l n m:
    (m ≤ n)%nat ->
    loc_in_bounds l n -∗ loc_in_bounds l m.
  Proof.
    move => ?. rewrite -(Nat.sub_add m n) // Nat.add_comm -loc_in_bounds_split. iIntros "[$ _]".
  Qed.

  Lemma loc_in_bounds_offset l1 l2 (n m : nat):
    l1.1 = l2.1 →
    l1.2 ≤ l2.2 ->
    l2.2 + m ≤ l1.2 + n ->
    loc_in_bounds l1 n -∗ loc_in_bounds l2 m.
  Proof.
    move => ???. have ->: (l2 = l1 +ₗ (l2.2 - l1.2)).
    { rewrite /shift_loc. destruct l1, l2 => /=. f_equal; [done| lia]. }
    have -> : n = (Z.to_nat (l2.2 - l1.2) + Z.to_nat (n - (l2.2 - l1.2)))%nat by lia.
    rewrite -loc_in_bounds_split. iIntros "[_ Hlib]". rewrite Z2Nat.id; [|lia].
    iApply (loc_in_bounds_shorten with "Hlib"). lia.
  Qed.

  Lemma loc_in_bounds_to_heap_loc_in_bounds l σ n:
    loc_in_bounds l n -∗ state_ctx σ -∗ ⌜heap_state_loc_in_bounds l n σ.(st_heap)⌝.
  Proof.
    rewrite loc_in_bounds_eq.
    iIntros "Hb ((?&?&Hctx&?)&?)". iDestruct "Hb" as (id al ????) "Hb".
    iDestruct (alloc_meta_lookup with "Hctx Hb") as %[al' [?[[??]?]]].
    iExists id, al'. iPureIntro. unfold allocation_in_range, al_end in *.
    naive_solver lia.
  Qed.

  Lemma loc_in_bounds_ptr_in_range l n:
    loc_in_bounds l n -∗ ⌜min_alloc_start ≤ l.2 ∧ l.2 + n ≤ max_alloc_end⌝.
  Proof.
    rewrite loc_in_bounds_eq. iIntros "Hlib".
    iDestruct "Hlib" as (?????[??]) "?". iPureIntro. lia.
  Qed.

  Lemma loc_in_bounds_in_range_uintptr_t l n:
    loc_in_bounds l n -∗ ⌜l.2 ∈ uintptr_t⌝.
  Proof.
    iIntros "Hl". iDestruct (loc_in_bounds_ptr_in_range with "Hl") as %Hrange.
    iPureIntro. move: Hrange.
    rewrite /min_alloc_start /max_alloc_end /bytes_per_addr /bytes_per_addr_log /=.
    move => [??]. split; cbn; first by lia.
    rewrite /max_int /= /int_modulus /bits_per_int /bytes_per_int /=. lia.
  Qed.

  Lemma loc_in_bounds_has_alloc_id l n: loc_in_bounds l n -∗ ⌜∃ aid, l.1 = ProvAlloc (Some aid)⌝.
  Proof.
    rewrite loc_in_bounds_eq. iIntros "H". iDestruct "H" as (id ?????) "H".
    iPureIntro. by exists id.
  Qed.
End loc_in_bounds.

Section heap.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Global Instance heap_mapsto_mbyte_tl l q v : Timeless (heap_mapsto_mbyte l q v).
  Proof.  rewrite heap_mapsto_mbyte_eq. apply _. Qed.

  Global Instance heap_mapsto_mbyte_frac l v :
    Fractional (λ q, heap_mapsto_mbyte l q v)%I.
  Proof.
    intros p q. rewrite heap_mapsto_mbyte_eq. iSplit.
    - iDestruct 1 as (??) "[H1 H2]". iSplitL "H1"; iExists id; by iSplit.
    - iIntros "[H1 H2]". iDestruct "H1" as (??) "H1". iDestruct "H2" as (??) "H2".
      destruct l; simplify_eq/=. iExists _. iSplit; first done. by iSplitL "H1".
  Qed.

  Global Instance heap_mapsto_mbyte_as_fractional l q v:
    AsFractional (heap_mapsto_mbyte l q v) (λ q, heap_mapsto_mbyte l q v)%I q.
  Proof. split; [done|]. apply _. Qed.

  Global Instance heap_mapsto_timeless l q v : Timeless (l↦{q}v).
  Proof.  rewrite heap_mapsto_eq. apply _. Qed.

  Global Instance heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof. rewrite heap_mapsto_eq. apply _. Qed.

  Global Instance heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split; [done|]. apply _. Qed.

  Lemma heap_mapsto_loc_in_bounds l q v:
    l ↦{q} v -∗ loc_in_bounds l (length v).
  Proof. rewrite heap_mapsto_eq. iIntros "[$ _]". Qed.

  Lemma heap_mapsto_has_alloc_id l q v : l ↦{q} v -∗ ⌜∃ aid, l.1 = ProvAlloc (Some aid)⌝.
  Proof.
    iIntros "Hl". iApply loc_in_bounds_has_alloc_id.
    by iApply heap_mapsto_loc_in_bounds.
  Qed.

  Lemma heap_mapsto_loc_in_bounds_0 l q v:
    l ↦{q} v -∗ loc_in_bounds l 0.
  Proof.
    iIntros "Hl". iApply loc_in_bounds_shorten; last first.
    - by iApply heap_mapsto_loc_in_bounds.
    - lia.
  Qed.

  Lemma heap_mapsto_nil l q:
    l ↦{q} [] ⊣⊢ loc_in_bounds l 0.
  Proof. rewrite heap_mapsto_eq/heap_mapsto_def /=. solve_sep_entails. Qed.

  Lemma heap_mapsto_cons_mbyte l b v q:
    l ↦{q} (b::v) ⊣⊢ heap_mapsto_mbyte l q b ∗ loc_in_bounds l 1 ∗ (l +ₗ 1) ↦{q} v.
  Proof.
    rewrite heap_mapsto_eq/heap_mapsto_def /= shift_loc_0. setoid_rewrite shift_loc_assoc.
    have Hn:(∀ n, Z.of_nat (S n) = 1 + n) by lia. setoid_rewrite Hn.
    have ->:(∀ n, S n = 1 + n)%nat by lia.
    rewrite -loc_in_bounds_split.
    solve_sep_entails.
  Qed.

  Lemma heap_mapsto_cons l b v q:
    l ↦{q} (b::v) ⊣⊢ l ↦{q} [b] ∗ (l +ₗ 1) ↦{q} v.
  Proof.
    rewrite heap_mapsto_cons_mbyte !assoc. f_equiv.
    rewrite heap_mapsto_eq/heap_mapsto_def /= shift_loc_0.
    solve_sep_entails.
  Qed.

  Lemma heap_mapsto_app l v1 v2 q:
    l ↦{q} (v1 ++ v2) ⊣⊢ l ↦{q} v1 ∗ (l +ₗ length v1) ↦{q} v2.
  Proof.
    elim: v1 l.
    - move => l /=. rewrite heap_mapsto_nil shift_loc_0.
      iSplit; [ iIntros "Hl" | by iIntros "[_ $]" ].
      iSplit => //. by iApply heap_mapsto_loc_in_bounds_0.
    - move => b v1 IH l /=.
      rewrite heap_mapsto_cons IH assoc -heap_mapsto_cons.
      rewrite shift_loc_assoc.
      by have -> : (∀ n : nat, 1 + n = S n) by lia.
  Qed.

  Lemma heap_mapsto_mbyte_agree l q1 q2 v1 v2 :
    heap_mapsto_mbyte l q1 v1 ∗ heap_mapsto_mbyte l q2 v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_mbyte_eq.
    iIntros "[H1 H2]".
    iDestruct "H1" as (??) "H1". iDestruct "H2" as (??) "H2".
    iCombine "H1 H2" as "H". rewrite own_valid discrete_valid.
    iDestruct "H" as %Hvalid. iPureIntro.
    move: Hvalid => /= /auth_frag_valid /singleton_valid.
    move => -[] /= _ /to_agree_op_inv_L => ?. by simplify_eq.
  Qed.

  Lemma heap_mapsto_agree l q1 q2 v1 v2 :
    length v1 = length v2 →
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    elim: v1 v2 l. 1: by iIntros ([] ??)"??".
    move => ?? IH []//=???[?].
    rewrite !heap_mapsto_cons_mbyte.
    iIntros "[? [_ ?]] [? [_ ?]]".
    iDestruct (IH with "[$] [$]") as %-> => //.
    by iDestruct (heap_mapsto_mbyte_agree with "[$]") as %->.
  Qed.

  Lemma heap_mapsto_layout_has_layout l ly :
    l ↦|ly| -∗ ⌜l `has_layout_loc` ly⌝.
  Proof. iIntros "(% & % & % & ?)". done. Qed.

  Lemma heap_alloc_st l h v aid :
    l.1 = ProvAlloc (Some aid) →
    heap_range_free h l.2 (length v) →
    heap_ctx h ==∗
      heap_ctx (heap_alloc l.2 v aid h) ∗
      ([∗ list] i↦b ∈ v, heap_mapsto_mbyte_st (RSt 0) (l +ₗ i) aid 1 b).
  Proof.
    move => Haid Hfree. destruct l as [? a]. simplify_eq/=.
    have [->|Hv] := decide(v = []); first by iIntros "$ !>" => //=.
    rewrite -big_opL_commute1 // -(big_opL_commute auth_frag) /=.
    iIntros "H". rewrite -own_op. iApply own_update; last done.
    apply auth_update_alloc.
    elim: v a Hfree {Hv} => // b bl IH a Hfree.
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= Z.add_0_r.
    etrans. { apply (IH (a + 1)). move => a' Ha'. apply Hfree => /=. lia. }
    rewrite -insert_singleton_op; last first.
    { rewrite -None_equiv_eq big_opL_commute None_equiv_eq big_opL_None=> l' v' ?.
      rewrite lookup_singleton_None. lia. }
    rewrite /heap_alloc /heap_update -/heap_update.
    rewrite to_heapUR_insert. setoid_rewrite Z.add_assoc.
    apply alloc_local_update; last done. apply lookup_to_heapUR_None.
    rewrite heap_update_lookup_not_in_range /=; last lia.
    apply Hfree => /=. lia.
  Qed.

  Lemma heap_alloc l h v id al :
    l.1 = ProvAlloc (Some id) →
    heap_range_free h l.2 (length v) →
    al.(al_start) = l.2 →
    al.(al_len) = length v →
    allocation_in_range al →
    alloc_meta id al -∗
    alloc_alive id (DfracOwn 1) true -∗
    heap_ctx h ==∗
      heap_ctx (heap_alloc l.2 v id h) ∗
      l ↦ v ∗
      freeable l (length v) al.(al_kind).
  Proof.
    iIntros (Hid Hfree Hstart Hlen Hrange) "#Hr Hal Hctx".
    iMod (heap_alloc_st with "Hctx") as "[$ Hl]" => //.
    iModIntro. rewrite heap_mapsto_eq /heap_mapsto_def.
    rewrite heap_mapsto_mbyte_eq /heap_mapsto_mbyte_def.
    iSplitR "Hal"; last first; last iSplit.
    - rewrite freeable_eq. iExists id. iFrame. iSplit => //.
      by iApply (alloc_meta_mono with "Hr").
    - rewrite loc_in_bounds_eq. iExists id, al. iFrame "Hr".
      rewrite /al_end. iPureIntro. naive_solver lia.
    - iApply (big_sepL_impl with "Hl").
      iIntros (???) "!> H". iExists id. by iFrame.
  Qed.

  Lemma heap_mapsto_mbyte_lookup_q ls l aid h q b:
    heap_ctx h -∗
    heap_mapsto_mbyte_st ls l aid q b -∗
    ⌜∃ n' : nat,
        h !! l.2 = Some (HeapCell aid (match ls with RSt n => RSt (n+n') | WSt => WSt end) b)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heapUR lookup_fmap fmap_Some_equiv.
    move=> [[[aid'' ls'' v'] [Heq[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2 [/Some_pair_included] [_ Hincl]
      /to_agree_included ?; simplify_eq.
    destruct ls as [|n], ls'' as [|n''],
      Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    - by exists O.
    - by eauto.
    - exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_mbyte_lookup_1 ls l aid h b:
    heap_ctx h -∗
    heap_mapsto_mbyte_st ls l aid 1%Qp b -∗
    ⌜h !! l.2 = Some (HeapCell aid ls b)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heapUR lookup_fmap fmap_Some_equiv.
    move=> [[[aid'' ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma heap_mapsto_lookup_q flk l h q v:
    (∀ n, flk (RSt n) : Prop) →
    heap_ctx h -∗ l ↦{q} v -∗ ⌜heap_lookup_loc l v flk h⌝.
  Proof.
    iIntros (?) "Hh Hl".
    iInduction v as [|b v] "IH" forall (l) => //.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq /=.
    iDestruct "Hl" as "[Hb [_ Hl]]". iDestruct "Hb" as (? Heq) "Hb".
    rewrite /heap_lookup_loc /=. iSplit; last by iApply ("IH" with "Hh Hl").
    iDestruct (heap_mapsto_mbyte_lookup_q with "Hh Hb") as %[n Hn].
    by iExists _, _.
  Qed.

  Lemma heap_mapsto_lookup_1 (flk : lock_state → Prop) l h v:
    flk (RSt 0%nat) →
    heap_ctx h -∗ l ↦ v -∗ ⌜heap_lookup_loc l v flk h⌝.
  Proof.
    iIntros (?) "Hh Hl".
    iInduction v as [|b v] "IH" forall (l) => //.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq /=.
    iDestruct "Hl" as "[Hb [_ Hl]]". iDestruct "Hb" as (? Heq) "Hb".
    rewrite /heap_lookup_loc /=. iSplit; last by iApply ("IH" with "Hh Hl").
    iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as %Hl.
    by iExists _, _.
  Qed.

  Lemma heap_read_mbyte_vs h n1 n2 nf l aid q b:
    h !! l.2 = Some (HeapCell aid (RSt (n1 + nf)) b) →
    heap_ctx h -∗ heap_mapsto_mbyte_st (RSt n1) l aid q b
    ==∗ heap_ctx (<[l.2:=HeapCell aid (RSt (n2 + nf)) b]> h)
        ∗ heap_mapsto_mbyte_st (RSt n2) l aid q b.
  Proof.
    intros Hσv. do 2 apply wand_intro_r. rewrite left_id -!own_op to_heapUR_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heapUR lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma heap_read_na h l q v :
    heap_ctx h -∗ l ↦{q} v ==∗
      ⌜heap_lookup_loc l v (λ st, ∃ n, st = RSt n) h⌝ ∗
      heap_ctx (heap_upd l v (λ st, if st is Some (RSt n) then RSt (S n) else WSt) h) ∗
      ∀ h2, heap_ctx h2 ==∗ ⌜heap_lookup_loc l v (λ st, ∃ n, st = RSt (S n)) h2⌝ ∗
        heap_ctx (heap_upd l v (λ st, if st is Some (RSt (S n)) then RSt n else WSt) h2) ∗ l ↦{q} v.
  Proof.
    iIntros "Hh Hv".
    iDestruct (heap_mapsto_lookup_q with "Hh Hv") as %Hat. 2: iSplitR => //. 1: by naive_solver.
    iInduction (v) as [|b v] "IH" forall (l Hat) => //=.
    { iFrame. by iIntros "!#" (?) "$ !#". }
    rewrite ->heap_mapsto_cons_mbyte, heap_mapsto_mbyte_eq.
    iDestruct "Hv" as "[Hb [? Hl]]". iDestruct "Hb" as (? Heq) "Hb".
    move: Hat. rewrite /heap_lookup_loc Heq /= => -[[? [? [Hin [?[n ?]]]]] ?]; simplify_eq/=.
    iMod ("IH" with "[] Hh Hl") as "{IH}[Hh IH]".
    { iPureIntro => /=. by destruct l; simplify_eq/=. }
    iMod (heap_read_mbyte_vs _ 0 1 with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range // /shift_loc /=. lia. }
    iModIntro. iSplitL "Hh".
    { iStopProof. f_equiv. symmetry. apply partial_alter_to_insert.
      rewrite heap_update_lookup_not_in_range /shift_loc /= ?Hin ?Heq //; lia. }
    iIntros (h2) "Hh". iDestruct (heap_mapsto_mbyte_lookup_q with "Hh Hb") as %[n' Hn].
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]". iSplitR.
    { rewrite /shift_loc /= Z.add_1_r Heq in Hat. iPureIntro. naive_solver. }
    iMod (heap_read_mbyte_vs _ 1 0 with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range // /shift_loc /=. lia. }
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq. iModIntro. iFrame.
    iSplitL; [ iStopProof | done ].
    f_equiv. symmetry. apply partial_alter_to_insert.
    rewrite heap_update_lookup_not_in_range /shift_loc /= ?Hn ?Heq //. lia.
  Qed.

  Lemma heap_write_mbyte_vs h st1 st2 l aid b b':
    h !! l.2 = Some (HeapCell aid st1 b) →
    heap_ctx h -∗ heap_mapsto_mbyte_st st1 l aid 1%Qp b
    ==∗ heap_ctx (<[l.2:=HeapCell aid st2 b']> h) ∗ heap_mapsto_mbyte_st st2 l aid 1%Qp b'.
  Proof.
    intros Hσv. do 2 apply wand_intro_r. rewrite left_id -!own_op to_heapUR_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heapUR lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write f h l v v':
    length v = length v' → f (Some (RSt 0)) = RSt 0 →
    heap_ctx h -∗ l ↦ v ==∗ heap_ctx (heap_upd l v' f h) ∗ l ↦ v'.
  Proof.
    iIntros (Hlen Hf) "Hh Hmt".
    iInduction (v) as [|v b] "IH" forall (l v' Hlen); destruct v' => //; first by iFrame.
    move: Hlen => [] Hlen. rewrite !heap_mapsto_cons_mbyte !heap_mapsto_mbyte_eq.
    iDestruct "Hmt" as "[Hb [$ Hl]]". iDestruct "Hb" as (? Heq) "Hb".
    iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as % Hin; auto.
    iMod ("IH" with "[//] Hh Hl") as "[Hh $]".
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range /shift_loc //=. lia. }
    iModIntro => /=. iSplitR "Hb"; last (iExists _; by iFrame).
    iClear "IH". iStopProof. f_equiv => /=. symmetry.
    apply: partial_alter_to_insert.
    rewrite heap_update_lookup_not_in_range /shift_loc /= ?Heq ?Hin ?Hf //. lia.
  Qed.

  Lemma heap_write_na h l v v' :
    length v = length v' →
    heap_ctx h -∗ l ↦ v ==∗
      ⌜heap_lookup_loc l v (λ st, st = RSt 0) h⌝ ∗
      heap_ctx (heap_upd l v (λ _, WSt) h) ∗
      ∀ h2, heap_ctx h2 ==∗ ⌜heap_lookup_loc l v (λ st, st = WSt) h2⌝ ∗
        heap_ctx (heap_upd l v' (λ _, RSt 0) h2) ∗ l ↦ v'.
  Proof.
    iIntros (Hlen) "Hh Hv".
    iDestruct (heap_mapsto_lookup_1 with "Hh Hv") as %Hat. 2: iSplitR => //. 1: by naive_solver.
    iInduction (v) as [|b v] "IH" forall (l v' Hat Hlen) => //=; destruct v' => //.
    { iFrame. by iIntros "!#" (?) "$ !#". }
    move: Hlen => -[] Hlen.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq.
    iDestruct "Hv" as "[Hb [? Hl]]". iDestruct "Hb" as (? Heq) "Hb".
    move: Hat. rewrite /heap_lookup_loc Heq /= => -[[? [? [Hin [??]]]] ?]; simplify_eq/=.
    iMod ("IH" with "[] [] Hh Hl") as "{IH}[Hh IH]"; [|done|].
    { iPureIntro => /=. by destruct l; simplify_eq/=. }
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range /shift_loc /= ?Hin ?Heq //=. lia. }
    iSplitL "Hh". { rewrite /heap_upd /=. erewrite partial_alter_to_insert; first done.
                    rewrite heap_update_lookup_not_in_range; last lia. by rewrite Heq Hin. }
    iIntros "!#" (h2) "Hh". iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as %Hn.
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]". iSplitR.
    { rewrite /shift_loc /= Z.add_1_r Heq in Hat. iPureIntro. naive_solver. }
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range /shift_loc /= ?Heq ?Hin //=. lia. }
    rewrite /heap_upd !Heq /=. erewrite partial_alter_to_insert; last done.
    rewrite Z.add_1_r Heq. iFrame.
    rewrite heap_update_lookup_not_in_range; last lia. rewrite Hn /=. iFrame.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq. by iFrame.
  Qed.

  Lemma heap_free_free_st l h v aid :
    l.1 = ProvAlloc (Some aid) →
    heap_ctx h ∗ ([∗ list] i↦b ∈ v, heap_mapsto_mbyte_st (RSt 0) (l +ₗ i) aid 1 b) ==∗
      heap_ctx (heap_free l.2 (length v) h).
  Proof.
    move => Haid. destruct l as [? a]. simplify_eq/=.
    have [->|Hv] := decide(v = []); first by iIntros "[$ _]".
    rewrite -big_opL_commute1 // -(big_opL_commute auth_frag) /=.
    iIntros "H". rewrite -own_op. iApply own_update; last done.
    apply auth_update_dealloc.
    elim: v h a {Hv} => // b bl IH h a.
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= Z.add_0_r.

    apply local_update_total_valid=> _ Hvalid _.
    have ? : (([^op list] k↦y ∈ bl, {[a + (1 + k) := (1%Qp, to_lock_stateR (RSt 0%nat), to_agree (aid, y))]} : heapUR) !! a = None). {
      move: (Hvalid a). rewrite lookup_op lookup_singleton.
      by move=> /(cmra_discrete_valid_iff 0%nat) /exclusiveN_Some_l.
    }
    rewrite -insert_singleton_op //. etrans.
    { apply (delete_local_update _ _ a (1%Qp, to_lock_stateR (RSt 0%nat), to_agree (aid, b))).
      by rewrite lookup_insert. }
    rewrite delete_insert // -to_heapUR_delete (heap_free_delete _ a).
    setoid_rewrite Z.add_assoc. by apply IH.
  Qed.

  Lemma heap_free_free l v h :
    heap_ctx h -∗ l ↦ v ==∗ heap_ctx (heap_free l.2 (length v) h).
  Proof.
    iIntros "Hctx Hl".
    iDestruct (heap_mapsto_has_alloc_id with "Hl") as %[??].
    iMod (heap_free_free_st with "[$Hctx Hl]"); [done| |done].
    rewrite heap_mapsto_eq /heap_mapsto_def. iDestruct "Hl" as "[_ Hl]".
    iApply (big_sepL_impl with "Hl"). iIntros (???) "!> H".
    rewrite heap_mapsto_mbyte_eq /heap_mapsto_mbyte_def /=.
    iDestruct "H" as (?) "[% H]". by destruct l; simplify_eq/=.
  Qed.
End heap.

Section alloc_alive.
  Context `{!heapG Σ} `{!BiFUpd (iPropI Σ)}.

  Lemma alloc_alive_loc_mono (l1 l2 : loc) :
    l1.1 = l2.1 →
    alloc_alive_loc l1 -∗ alloc_alive_loc l2.
  Proof. rewrite alloc_alive_loc_eq /alloc_alive_loc_def => ->. by iIntros "$". Qed.

  Lemma heap_mapsto_alive_strong l :
    (|={⊤, ∅}=> (∃ q v, ⌜length v ≠ 0%nat⌝ ∗ l ↦{q} v)) -∗ alloc_alive_loc l.
  Proof.
    rewrite alloc_alive_loc_eq. move: l => [? a]. iIntros ">(%q&%v&%&?)". iModIntro.
    iRight. iExists a, q, _. iFrame. by destruct v.
  Qed.

  Lemma heap_mapsto_alive l q v:
    length v ≠ 0%nat →
    l ↦{q} v -∗ alloc_alive_loc l.
  Proof.
    iIntros (?) "Hl". iApply heap_mapsto_alive_strong.
    iApply fupd_mask_intro; [set_solver|]. iIntros "?".
    iExists _, _. by iFrame.
  Qed.

  Lemma alloc_global_alive l:
    alloc_global l -∗ alloc_alive_loc l.
  Proof.
    rewrite alloc_global_eq alloc_alive_loc_eq. iIntros "(%id&%&Ha)".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "_". iLeft. eauto.
  Qed.

  Lemma alloc_alive_loc_to_block_alive l σ:
    alloc_alive_loc l -∗ state_ctx σ ={⊤, ∅}=∗ ⌜block_alive l σ.(st_heap)⌝.
  Proof.
    rewrite alloc_alive_loc_eq. iIntros ">[H|H]".
    - iDestruct "H" as (???) "Hl". iIntros "((Hinv&_&_&Hctx)&_) !>".
      iExists _. iSplit => //.
      iDestruct (alloc_alive_lookup with "Hctx Hl") as %[?[??]]. iPureIntro.
      eexists _. naive_solver.
    - iIntros "(((?&Halive&?&?)&Hctx&?&?)&?) !>".
      iDestruct "H" as (????) "H".
      iDestruct (heap_mapsto_lookup_q (λ _, True) with "Hctx H") as %Hlookup => //.
      destruct v => //. destruct Hlookup as [[id [?[?[??]]]]?].
      iExists id. iSplit; first done. iDestruct "Halive" as %Halive.
      iPureIntro. apply: (Halive _ (HeapCell _ _ _)). done.
  Qed.

  Lemma alloc_alive_loc_to_valid_ptr l σ:
    loc_in_bounds l 0 -∗ alloc_alive_loc l -∗ state_ctx σ ={⊤, ∅}=∗ ⌜valid_ptr l σ.(st_heap)⌝.
  Proof.
    iIntros "Hin Ha Hσ".
    iDestruct (loc_in_bounds_to_heap_loc_in_bounds with "Hin Hσ") as %?.
    by iMod (alloc_alive_loc_to_block_alive with "Ha Hσ") as %?.
  Qed.
End alloc_alive.

Section alloc_new_blocks.
  Context `{!heapG Σ}.

  Lemma heap_alloc_new_block_upd σ1 l v kind σ2:
    alloc_new_block σ1 kind l v σ2 →
    heap_state_ctx σ1 ==∗ heap_state_ctx σ2 ∗ l ↦ v ∗ freeable l (length v) kind.
  Proof.
    move => []; clear. move => σ l aid kind v alloc Haid ???; subst alloc.
    iIntros "Hctx". iDestruct "Hctx" as (Hinv) "(Hhctx&Hrctx&Hsctx)".
    iMod (alloc_meta_alloc  with "Hrctx") as "[$ #Hb]" => //.
    iMod (alloc_alive_alloc with "Hsctx") as "[$ Hs]" => //.
    iDestruct (alloc_meta_to_loc_in_bounds l aid (length v) with "[Hb]")
      as "#Hinb" => //; [done|..].
    iMod (heap_alloc with "Hb Hs Hhctx") as "[Hhctx [Hv Hal]]" => //.
    iModIntro. iFrame. iPureIntro. by eapply alloc_new_block_invariant.
  Qed.

  Lemma heap_alloc_new_blocks_upd σ1 ls vs kind σ2:
    alloc_new_blocks σ1 kind ls vs σ2 →
    heap_state_ctx σ1 ==∗
      heap_state_ctx σ2 ∗
      [∗ list] l; v ∈ ls; vs, l ↦ v ∗ freeable l (length v) kind.
  Proof.
    move => alloc.
    iInduction alloc as [σ|] "IH"; first by iIntros "$ !>". iIntros "Hσ".
    iMod (heap_alloc_new_block_upd with "Hσ") as "(Hσ&Hl)"; [done|..].
    iFrame. by iApply "IH".
  Qed.
End alloc_new_blocks.

Section free_blocks.
  Context `{!heapG Σ}.

  Lemma heap_free_block_upd σ1 l ly kind:
    l ↦|ly| -∗
    freeable l (ly_size ly) kind -∗
    heap_state_ctx σ1 ==∗ ∃ σ2, ⌜free_block σ1 kind l ly σ2⌝ ∗ heap_state_ctx σ2.
  Proof.
    iIntros "Hl Hfree (Hinv&Hhctx&Hrctx&Hsctx)". iDestruct "Hinv" as %Hinv.
    rewrite freeable_eq. iDestruct "Hfree" as (aid Haid) "[#Hrange Hkill]".
    iDestruct "Hl" as (v Hv ?) "Hl".
    iDestruct (alloc_alive_lookup with "Hsctx Hkill") as %[[????k] [??]].
    iDestruct (alloc_meta_lookup with "Hrctx Hrange") as %[al'' [?[[??]?]]]. simplify_eq/=.
    iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0) with "Hhctx Hl") as %? => //.
    iExists _. iSplitR. { iPureIntro. by econstructor. }
    iMod (heap_free_free with "Hhctx Hl") as "Hhctx". rewrite Hv. iFrame => /=.
    iMod (alloc_alive_kill _ _ ({| al_start := l.2; al_len := ly_size ly; al_alive := true; al_kind := k |}) with "Hsctx Hkill") as "[$ Hd]".
    erewrite alloc_meta_ctx_same_range; [iFrame |done..].
    iPureIntro. eapply free_block_invariant => //. by eapply FreeBlock.
  Qed.

  Lemma heap_free_blocks_upd ls σ1 kind:
    ([∗ list] l ∈ ls, l.1 ↦|l.2| ∗ freeable l.1 (ly_size l.2) kind ) -∗
    heap_state_ctx σ1 ==∗ ∃ σ2, ⌜free_blocks σ1 kind ls σ2⌝ ∗ heap_state_ctx σ2.
  Proof.
    iInduction ls as [|[l ly] ls] "IH" forall (σ1).
    { iIntros "_ ? !>". iExists σ1. iFrame. iPureIntro. by constructor. }
    iIntros "[[Hl Hf] Hls] Hσ" => /=.
    iMod (heap_free_block_upd with "Hl Hf Hσ") as (σ2 Hfree) "Hσ".
    iMod ("IH" with "Hls Hσ") as (??) "Hσ".
    iExists _. iFrame. iPureIntro. by econstructor.
  Qed.
End free_blocks.
