From iris.algebra Require Import list.
From refinedc.typing Require Export type.
From refinedc.typing Require Import programs singleton bytes int own.
From refinedc.typing Require Import type_options.

Section array.
  Context `{typeG Σ}.
  (*** arrays *)
  Program Definition array (ly : layout) (tys : list type) : type := {|
    ty_has_op_type ot mt := ot = UntypedOp (mk_array_layout ly (length tys)) ∧ mt = MCNone ∧ layout_wf ly ∧ Forall (λ ty, ty.(ty_has_op_type) (UntypedOp ly) MCNone) tys;
    ty_own β l := (
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l (ly_size ly * length tys)%nat ∗
      [∗ list] i ↦ ty ∈ tys, (l offset{ly}ₗ i) ◁ₗ{β} ty
    )%I;
    ty_own_val v :=
      (⌜v `has_layout_val` (mk_array_layout ly (length tys))⌝ ∗
       [∗ list] v';ty∈reshape (replicate (length tys) (ly_size ly)) v;tys, (v' ◁ᵥ ty))%I;
  |}.
  Next Obligation.
    iIntros (ly tys l E He) "($&$&Ha)". iApply big_sepL_fupd. iApply (big_sepL_impl with "Ha").
    iIntros "!#" (???). by iApply ty_share.
  Qed.
  Next Obligation. by iIntros (ly tys ot mt l [-> ?]) "[% _]". Qed.
  Next Obligation. by iIntros (ly tys ot mt v [-> ?]) "(?&_)". Qed.
  Next Obligation.
    move => ly tys ot mt l [? [? [? ]]]. iIntros (Hlys) "(_&#Hb&Htys)". subst.
    iInduction (tys) as [|ty tys] "IH" forall (l Hlys); csimpl.
    { iExists []. iSplitR => //.
      - iApply heap_mapsto_nil; first by iApply (loc_in_bounds_shorten with "Hb"); lia.
      - iSplit => //. iPureIntro. rewrite /has_layout_val/ly_size/=. lia. }
    move: Hlys. intros (?&?)%Forall_cons. csimpl.
    rewrite offset_loc_0. iDestruct "Htys" as "[Hty Htys]".
    iDestruct (loc_in_bounds_split_mul_S with "Hb") as "[Hb1 Hb2]".
    iDestruct (ty_deref with "Hty") as (v') "[Hl Hty]"; [done|].
    iDestruct (ty_size_eq with "Hty") as %Hszv; [done|].
    setoid_rewrite offset_loc_S.
    iDestruct ("IH" $! (l offset{ly}ₗ 1) with "[//] [Hb2] Htys") as (vs') "(Hl' & Hsz & Htys)".
    { by rewrite /offset_loc Z.mul_1_r. }
    iDestruct "Hsz" as %Hsz. iExists (v' ++ vs').
    rewrite /has_layout_val heap_mapsto_app Hszv offset_loc_1 take_app_length' // drop_app_length' // length_app Hszv Hsz.
    iFrame. iPureIntro. rewrite /ly_size/= -/(ly_size _). lia.
  Qed.
  Next Obligation.
    move => ly tys ot mt l v [-> [? [? ]]]. iIntros (Hlys Hl) "Hl".
    iDestruct 1 as (Hv) "Htys". iSplit => //.
    iInduction (tys) as [|ty tys] "IH" forall (l v Hlys Hv Hl); csimpl in *.
    { rewrite Nat.mul_0_r right_id. by iApply heap_mapsto_loc_in_bounds_0. }
    move: Hlys. intros [? ?]%Forall_cons. iDestruct "Htys" as "[Hty Htys]".
    rewrite -{1}(take_drop (ly_size ly) v).
    rewrite offset_loc_0 heap_mapsto_app length_take_le ?Hv; last by repeat unfold ly_size => /=; lia.
    iDestruct "Hl" as "[Hl Hl']".
    iDestruct (heap_mapsto_loc_in_bounds with "Hl") as "#Hb1".
    iDestruct (ty_ref with "[] Hl Hty") as "$" => //.
    setoid_rewrite offset_loc_S. rewrite offset_loc_1.
    iDestruct ("IH" with "[//] [] [] Hl' Htys") as "[#Hb2 $]".
    { iPureIntro. rewrite /has_layout_val length_drop Hv. by repeat unfold ly_size => /=; lia. }
    { iPureIntro. by apply has_layout_loc_ly_mult_offset. }
    iApply loc_in_bounds_split_mul_S. rewrite length_take min_l; first by eauto.
    rewrite Hv. repeat unfold ly_size => /=; lia.
  Qed.
  Next Obligation. iIntros (??????[?[-> ?]]) "?". done. Qed.

  Global Instance array_le : Proper ((=) ==> Forall2 (⊑) ==> (⊑)) array.
  Proof.
    move => ? sl -> tys1 tys2 Htys. constructor.
    - move => β l; rewrite/ty_own/=.
      f_equiv. f_equiv; first by rewrite ->Htys.
      elim: Htys l => // ???????? /=. f_equiv; [solve_proper|].
      by setoid_rewrite offset_loc_S.
    - move => v; rewrite/ty_own_val/=.
      f_equiv. { f_equiv; first by rewrite ->Htys. }
      elim: Htys v => // ???? Hty Htys IH v /=. f_equiv. { solve_proper. }
      apply: IH.
  Qed.
  Global Instance array_proper : Proper ((=) ==> Forall2 (≡) ==> (≡)) array.
  Proof. move => ??-> ?? Heq. apply type_le_equiv_list; [by apply array_le|done]. Qed.

  Global Instance array_loc_in_bounds ly β tys : LocInBounds (array ly tys) β (ly_size ly * length tys).
  Proof. constructor. iIntros (?) "(?&$&?)". Qed.

  Lemma array_get_type (i : nat) ly tys ty l β:
    tys !! i = Some ty →
    l ◁ₗ{β} array ly tys -∗ (l offset{ly}ₗ i) ◁ₗ{β} ty ∗ l ◁ₗ{β} array ly (<[ i := place (l offset{ly}ₗ i)]>tys).
  Proof.
    rewrite !/(ty_own (array _ _))/=. iIntros (Hi) "($&Hb&Ha)".
    iInduction (i) as [|i] "IH" forall (l tys Hi);
    destruct tys as [|ty' tys] => //; simpl in *; simplify_eq;
    iDestruct "Ha" as "[$ Ha]".
    { unfold place; by iFrame. }
    rewrite offset_loc_S. setoid_rewrite offset_loc_S.
    iDestruct (loc_in_bounds_split_mul_S with "Hb") as "[Hb1 Hb2]".
    rewrite /offset_loc Z.mul_1_r.
    iDestruct ("IH" with "[//] [Hb2] Ha") as "[$[Hb2 $]]" => //.
    iApply loc_in_bounds_split_mul_S. iFrame.
  Qed.

  Lemma array_put_type (i : nat) ly tys ty l β:
    (l offset{ly}ₗ i) ◁ₗ{β} ty -∗ l ◁ₗ{β} array ly tys -∗ l ◁ₗ{β} array ly (<[ i := ty ]>tys).
  Proof.
    rewrite !/(ty_own (array _ _))/=. iIntros "Hl ($&Hb&Ha)".
    destruct (decide (i < length tys)%nat) as [Hlt |]; last first.
    { rewrite list_insert_ge => //; last by lia. iFrame. }
    iInduction (i) as [|i] "IH" forall (l tys Hlt);
    destruct tys as [|ty' tys] => //; simpl in *; simplify_eq; eauto.
    - iFrame. by iDestruct "Ha" as "[_ $]".
    - rewrite offset_loc_S. setoid_rewrite offset_loc_S.
      iDestruct "Ha" as "[$ Ha]".
      iDestruct (loc_in_bounds_split_mul_S with "Hb") as "[Hb1 Hb2]".
      rewrite /offset_loc Z.mul_1_r.
      iDestruct ("IH" with "[] Hl [Hb2] Ha") as "[Hb2 $]" => //.
      { iPureIntro. lia. }
      iApply loc_in_bounds_split_mul_S. iFrame.
  Qed.

  Global Instance array_alloc_alive ly tys β P `{!TCExists (λ ty, AllocAlive ty β P) tys} :
    AllocAlive (array ly tys) β P.
  Proof.
    revert select (TCExists _ _).
    rewrite TCExists_Exists Exists_exists => -[x [/(list_elem_of_lookup_1 _ _) [i Hx] ?]].
    constructor. iIntros (l) "HP Hl".
    iDestruct (array_get_type with "Hl") as "[Hl _]"; [done|].
    iDestruct (alloc_alive_alive with "HP Hl") as "Hl".
    by iApply (alloc_alive_loc_mono with "Hl").
  Qed.

  Lemma subsume_array_alloc_alive A M l ly tys β T :
    (⌜0 < length tys⌝ ∗ (∀ ty, ⌜tys !! 0%nat = Some ty⌝ -∗ l ◁ₗ{β} ty -∗ ‖M‖ alloc_alive_loc l ∗ ∃ x, T x))
    ⊢ subsume (l ◁ₗ{β} array ly tys) M (λ x : A, alloc_alive_loc l) T.
  Proof.
    iIntros "[% HT]". destruct tys => //=. iIntros "(%&?&[Hty Htys])".
    rewrite offset_loc_0. iMod ("HT" with "[//] Hty") as "[? [% ?]]".
    iModIntro. iFrame.
  Qed.
  Definition subsume_array_alloc_alive_inst := [instance subsume_array_alloc_alive].
  Global Existing Instance subsume_array_alloc_alive_inst | 10.
  (*** array_ptr *)
  Program Definition array_ptr (ly : layout) (base : loc) (idx : Z) (len : nat) : type := {|
    ty_own β l := (
      ⌜l = base offset{ly}ₗ idx⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      ⌜0 ≤ idx ≤ len⌝ ∗
      loc_in_bounds base (ly_size (mk_array_layout ly len))
    )%I;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ := True%I;
  |}.
  Solve Obligations with try done.
  Next Obligation. iIntros (ly base idx len l E ?) "(%&%&$)". done. Qed.

  Global Instance array_ptr_loc_in_bounds ly base idx β len : LocInBounds (array_ptr ly base idx len) β ((len - Z.to_nat idx) * ly_size ly).
  Proof.
    constructor. iIntros (?) "(->&%&%&Hl)".
    iApply (loc_in_bounds_offset with "Hl") => /=; unfold addr in *; [done|lia|].
    rewrite /mk_array_layout{3}/ly_size/=. nia.
  Qed.
  (*** sized_array *)
  Program Definition sized_array (ly : layout) (tys : list type) (len: nat) : type := {|
    ty_has_op_type ot mt := ot = UntypedOp (mk_array_layout ly (length tys)) ∧ mt = MCNone ∧ layout_wf ly ∧ Forall (λ ty, ty.(ty_has_op_type) (UntypedOp ly) MCNone) tys ∧ len = length tys;
    ty_own β l := (
      ⌜l `has_layout_loc` ly⌝ ∗
      ⌜length tys = len⌝ ∗
      loc_in_bounds l (ly_size ly * length tys)%nat ∗
      ([∗ list] i ↦ ty ∈ tys, (l offset{ly}ₗ i) ◁ₗ{β} ty)
    )%I;
    ty_own_val v := (
      ⌜v `has_layout_val` (mk_array_layout ly (length tys))⌝ ∗
      ⌜length tys = len⌝ ∗
      ([∗ list] v';ty∈reshape (replicate (length tys) (ly_size ly)) v;tys, (v' ◁ᵥ ty))
    )%I;
  |}.
  Next Obligation.
    iIntros (ly tys len l E He) "($&$&Hloc&Ha)".
    iFrame.
    iApply big_sepL_fupd. iApply (big_sepL_impl with "Ha").
    iIntros "!#" (???). by iApply ty_share.
  Qed.
  Next Obligation. by iIntros (ly tys len ot mt l [-> ?]) "[% _]". Qed.
  Next Obligation. by iIntros (ly tys len ot mt v [-> ?]) "(?&_)". Qed.
  Next Obligation.
    move => ly tys len ot mt l [? [? [? ]]]. iIntros ([Hlys Hlen]) "(_&_&#Hb&Htys)". subst.
    iInduction (tys) as [|ty tys] "IH" forall (l Hlys); csimpl.
    { iExists []. iSplitR => //.
      - iApply heap_mapsto_nil; first by iApply (loc_in_bounds_shorten with "Hb"); lia.
      - iSplit => //. iPureIntro. rewrite /has_layout_val/ly_size/=. lia. }
    move: Hlys.
    intros (?&?)%Forall_cons. csimpl.
    rewrite offset_loc_0. iDestruct "Htys" as "[Hty Htys]".
    iDestruct (loc_in_bounds_split_mul_S with "Hb") as "[Hb1 Hb2]".
    iDestruct (ty_deref with "Hty") as (v') "[Hl Hty]"; [done|].
    iDestruct (ty_size_eq with "Hty") as %Hszv; [done|].
    setoid_rewrite offset_loc_S.
    iDestruct ("IH" $! (l offset{ly}ₗ 1) with "[//] [Hb2] Htys")
      as (vs') "(Hl' & Hsz & Hlen & Htys)".
    { by rewrite /offset_loc Z.mul_1_r. }
    iDestruct "Hsz" as %Hsz. iExists (v' ++ vs').
    rewrite /has_layout_val heap_mapsto_app Hszv offset_loc_1 take_app_length' //
      drop_app_length' // length_app Hszv Hsz. iFrame. iSplitR => //.
    iPureIntro. rewrite /ly_size/= -/(ly_size _). lia.
  Qed.
  Next Obligation.
    move => ly tys len ot mt l v [-> [? [? ]]]. iIntros ([Hlys _] Hl) "Hl".
    iDestruct 1 as (Hv Hlen) "Htys". iSplit => //.
    iInduction (tys) as [|ty tys] "IH" forall (l v len Hlys Hv Hl Hlen); csimpl in *.
    { iFrame. iSplitR => //. rewrite Nat.mul_0_r. iFrame. by iApply heap_mapsto_loc_in_bounds_0. }
    decompose_Forall. iDestruct "Htys" as "[Hty Htys]".
    rewrite -{1}(take_drop (ly_size ly) v).
    rewrite offset_loc_0 heap_mapsto_app length_take_le ?Hv; last by repeat unfold ly_size => /=; lia.
    iDestruct "Hl" as "[Hl Hl']".
    iDestruct (heap_mapsto_loc_in_bounds with "Hl") as "#Hb1".
    iDestruct (ty_ref with "[] Hl Hty") as "$" => //.
    setoid_rewrite offset_loc_S. rewrite offset_loc_1.
    iDestruct ("IH" with "[//] [] [] [//] Hl' Htys") as "[_ [#Hb2 Ha]]".
    { iPureIntro. rewrite /has_layout_val length_drop Hv. by repeat unfold ly_size => /=; lia. }
    { iPureIntro. by apply has_layout_loc_ly_mult_offset. }
    iSplitR => //. iFrame.
    iApply loc_in_bounds_split_mul_S. rewrite length_take min_l; first by eauto.
    rewrite Hv. repeat unfold ly_size => /=; lia.
  Qed.
  Next Obligation. iIntros (???????[?[-> ?]]) "?". done. Qed.

  (*** typing rules *)

  Lemma array_replicate_uninit_equiv l β ly n:
    layout_wf ly →
    l ◁ₗ{β} array ly (replicate n (uninit ly)) ⊣⊢ l ◁ₗ{β} uninit (mk_array_layout ly n).
  Proof.
    rewrite /ty_own/= => ?. iSplit.
    - iInduction n as [|n] "IH" forall (l) => /=; iIntros "(%&Hlib&Htys)".
      { iExists []. rewrite heap_mapsto_own_state_nil Nat.mul_0_r Forall_nil.
        iFrame "Hlib". iPureIntro. rewrite /has_layout_val/ly_size/=. naive_solver lia. }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      iDestruct "Htys" as "[Hty Htys]".
      iDestruct (loc_in_bounds_split_mul_S with "Hlib") as "[#Hlib1 Hlib2]".
      iDestruct ("IH" with "[Hlib2 Htys]") as (v2 Hv2 ? _) "Hv2".
      { iFrame. iPureIntro. revert select (layout_wf _). revert select (_ `has_layout_loc` _).
        rewrite /has_layout_loc /layout_wf /aligned_to. case_match => //. destruct l as [? a].
        move => /= [? ->] [? ->]. eexists. by rewrite -Z.mul_add_distr_r. }
      rewrite {2}/ty_own/=. iDestruct "Hty" as (v1 Hv1 Hl1 _) "Hv1".
      iExists (v1 ++ v2). rewrite heap_mapsto_own_state_app Hv1 /has_layout_val length_app Hv1 Hv2.
      iFrame. rewrite Forall_forall. iPureIntro. split_and! => //.
      rewrite {2 3}/ly_size/=. lia.
    - iDestruct 1 as (v Hv Hl _) "Hl". iSplit => //.
      iInduction n as [|n] "IH" forall (v l Hv Hl) => /=.
      { rewrite Nat.mul_0_r right_id.
        iApply loc_in_bounds_shorten; last by iApply heap_mapsto_own_state_loc_in_bounds. lia. }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      rewrite -(take_drop (ly.(ly_size)) v) heap_mapsto_own_state_app.
      iDestruct "Hl" as "[Hl Hr]". rewrite length_take_le ?Hv; last by repeat unfold ly_size => /=; lia.
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "#Hbl".
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hr") as "#Hbr".
      iDestruct ("IH" with "[] [] Hr") as "[Hb HH]".
      { iPureIntro. rewrite /has_layout_val length_drop Hv. repeat unfold ly_size => /=; lia. }
      { iPureIntro. by apply has_layout_loc_ly_mult_offset. }
      iSplitR.
      + iClear "IH". iApply loc_in_bounds_split_mul_S.
        rewrite length_take min_l; last first.
        { rewrite Hv. repeat unfold ly_size => /=; lia. }
        iFrame "Hbl". rewrite length_replicate length_drop Hv.
        destruct ly as [k?]. repeat unfold ly_size => /=.
        have ->: (k * n = k * S n - k)%nat by lia. done.
      + iSplitL "Hl"; last done. iExists _. iFrame. iPureIntro. rewrite Forall_forall. split_and! => //.
        rewrite /has_layout_val length_take_le ?Hv; repeat unfold ly_size => /=; lia.
  Qed.

  Lemma simplify_hyp_uninit_array ly l β n M T:
    ⌜layout_wf ly⌝ ∗ (l ◁ₗ{β} array ly (replicate n (uninit ly)) -∗ ‖M‖ T)
    ⊢ simplify_hyp (l ◁ₗ{β} uninit (mk_array_layout ly n)) M T.
  Proof. iIntros "[% HT] Hl". iApply "HT". rewrite array_replicate_uninit_equiv // {1}/ly_size/=. Qed.
  Definition simplify_hyp_uninit_array_inst := [instance simplify_hyp_uninit_array with 50%N].
  Global Existing Instance simplify_hyp_uninit_array_inst.

  Lemma simplify_goal_uninit_array ly l β n M T:
    ⌜layout_wf ly⌝ ∗ l ◁ₗ{β} array ly (replicate n (uninit ly)) ∗ T
    ⊢ simplify_goal M (l ◁ₗ{β} uninit (mk_array_layout ly n)) T.
  Proof. iIntros "[% [? $]] !>". rewrite array_replicate_uninit_equiv //. Qed.
  Definition simplify_goal_uninit_array_inst := [instance simplify_goal_uninit_array with 50%N].
  Global Existing Instance simplify_goal_uninit_array_inst.

  Lemma subsume_array_array_ptr A M β l ly idx len tys T:
    subsume (l ◁ₗ{β} array ly tys) M (λ x : A, l ◁ₗ{β} array_ptr ly l (idx x) (len x)) T :-
      inhale l ◁ₗ{β} array ly tys;
      ‖M‖ ∃ x : A, exhale ⌜idx x = 0⌝;
      exhale ⌜len x = length tys⌝;
      {T x}.
  Proof.
    iIntros "Hsub Harr". iDestruct "Harr" as "[% [#? Hlist]]".
     iMod ("Hsub" with "[Hlist]") as (? Hoffset Hlen) "HT". { by iFrame "# ∗". }
    iModIntro. iFrame. rewrite Hoffset Hlen. unfold array_ptr; simpl_type.
    unfold ly_size at 2; simpl. iFrame "#". repeat iSplit; iPureIntro;
      [ by rewrite offset_loc_0 | done | done | lia ].
  Qed.
  Definition subsume_array_array_ptr_inst := [instance subsume_array_array_ptr].
  Global Existing Instance subsume_array_array_ptr_inst | 10.

  (* TODO: generalize this rule, maybe similar to [subsume_array_uninit]? *)
  Lemma subsume_uninit_array_replicate A M l β n (ly1 : layout) ly2 T:
    (∃ x, ⌜layout_wf ly2⌝ ∗ ⌜ly1 = mk_array_layout ly2 n⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} uninit ly1) M (λ x : A, l ◁ₗ{β} array ly2 (replicate n (uninit ly2))) T.
  Proof. iIntros "(%&%&->&?) ? !>". iExists _. iFrame. by rewrite array_replicate_uninit_equiv. Qed.
  Definition subsume_uninit_array_replicate_inst := [instance subsume_uninit_array_replicate].
  Global Existing Instance subsume_uninit_array_replicate_inst.

  Lemma subsume_array_uninit A M l β tys ly1 ly2 T:
    (l ◁ₗ{β} array ly2 tys -∗
      ‖M‖ ⌜layout_wf ly2⌝ ∗ l ◁ₗ{β} array ly2 (replicate (length tys) (uninit ly2)) ∗
      ∃ x, ⌜ly1 x = mk_array_layout ly2 (length tys)⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} array ly2 tys) M (λ x : A, l ◁ₗ{β} uninit (ly1 x)) T.
  Proof.
    iIntros "Hsub ?". iMod ("Hsub" with "[$]") as (?) "[? [% [%Heq ?]]]".
    iModIntro. iFrame. by rewrite Heq array_replicate_uninit_equiv.
  Qed.
  Definition subsume_array_uninit_inst := [instance subsume_array_uninit].
  Global Existing Instance subsume_array_uninit_inst.

  Lemma subsume_array A M ly1 ly2 tys1 tys2 l β T:
    (⌜ly1 = ly2⌝ ∗ ∀ id,
       subsume (sep_list id type [] tys1 (λ i ty, (l offset{ly1}ₗ i) ◁ₗ{β} ty)) M
         (λ x, sep_list id type [] (tys2 x) (λ i ty, (l offset{ly1}ₗ i) ◁ₗ{β} ty)) T)
    ⊢ subsume (l ◁ₗ{β} array ly1 tys1) M (λ x : A, l ◁ₗ{β} array ly2 (tys2 x)) T.
  Proof.
    unfold sep_list. iIntros "[-> H] ($&Hb&H1)".
    iMod ("H" $! {|sep_list_len := length tys1|} with "[$H1]") as (?) "[[%Heq ?] ?]"; [done|].
    iModIntro. simpl in *. rewrite -Heq. iExists _. iFrame.
  Qed.
  Definition subsume_array_inst := [instance subsume_array].
  Global Existing Instance subsume_array_inst.

  Lemma type_place_array l β ly1 it v tyv tys ly2 K T:
  typed_place (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array ly2 tys) T :-
     inhale v ◁ᵥ tyv;
     ∃ i : Z,
     exhale ⌜ly1 = ly2⌝;
     exhale v ◁ᵥ i @ int it;
     exhale ⌜0 ≤ i⌝;
     exhale ⌜i < length tys⌝;
     ∀ ty : type,
     inhale ⌜tys !! Z.to_nat i = Some ty⌝;
     {typed_place K (l offset{ly2}ₗ i) β ty
        (λ (l2 : loc) (β2 : own_state) (ty2 : type) (typ : type → type),
           T l2 β2 ty2 (λ t : type, array ly2 (<[Z.to_nat i:=typ t]> tys)))}.
  Proof.
    iIntros "HT" (Φ) "(%&#Hb&Hl) HΦ" => /=. iIntros "Hv".
    iDestruct ("HT" with "Hv") as (i ->) "HP". unfold int; simpl_type.
    iDestruct ("HP") as (Hv) "HP".
    iDestruct "HP" as (? Hlen) "HP".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat i). 1: lia.
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hb"); simpl; [done| destruct l => /=; lia | destruct l => /=; nia]. }
    iIntros "!#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hl Hc]" => //. rewrite Z2Nat.id//.
    iApply ("HP" $! ty with "[//] Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]".
    iSplitR => //. iSplitR; first by rewrite length_insert. by iApply "Hc".
  Qed.
  Definition type_place_array_inst := [instance type_place_array].
  Global Existing Instance type_place_array_inst.

  Lemma type_bin_op_offset_array l β ly it v tys i T:
    (* TODO: Should we make layout_wf ly part of array such that we don't need to require it here? *)
    ⌜layout_wf ly⌝ ∗ ⌜0 ≤ i ≤ length tys⌝ ∗ (l ◁ₗ{β} array ly tys -∗ T (val_of_loc (l offset{ly}ₗ i)) ((l offset{ly}ₗ i) @ &own (array_ptr ly l i (length tys))))
    ⊢ typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array ly tys) (PtrOffsetOp ly) (IntOp it) PtrOp T.
  Proof.
    iIntros "[% [% HT]]". unfold int; simpl_type.
    iIntros "%Hv (%&#Hlib&Hl)" (Φ) "HΦ".
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done| destruct l => /=; lia | destruct l => /=; nia]. }
    iModIntro. iApply "HΦ"; [|iApply "HT"; iFrame; by iSplit].
    unfold frac_ptr; simpl_type. iSplit; [done|]. iSplit; [done|].
    iSplit; [| by iSplit].
    iPureIntro. by apply: has_layout_loc_offset_loc.
  Qed.
  Definition type_bin_op_offset_array_inst := [instance type_bin_op_offset_array].
  Global Existing Instance type_bin_op_offset_array_inst.

  Lemma type_bin_op_offset_array_ptr l β ly it v i idx (len : nat) base T:
    ⌜layout_wf ly⌝ ∗ ⌜0 ≤ idx + i ≤ len⌝ ∗ (l ◁ₗ{β} array_ptr ly base idx len -∗ T (val_of_loc (base offset{ly}ₗ (idx + i))) ((base offset{ly}ₗ (idx + i)) @ &own (array_ptr ly base (idx + i) len)))
    ⊢ typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array_ptr ly base idx len) (PtrOffsetOp ly) (IntOp it) PtrOp T.
  Proof.
    iIntros "[% [% HT]]". unfold int; simpl_type.
    iIntros "%Hv (->&%&%&#Hlib)" (Φ) "HΦ".
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; unfold addr in *; [done|nia|].
      rewrite {3}/ly_size/=. nia. }
    rewrite offset_loc_offset_loc.
    iModIntro. iApply "HΦ"; [|iApply "HT"]; unfold frac_ptr; simpl_type; iFrame "Hlib"; iPureIntro; [|done].
    split_and! => //; try lia. rewrite -offset_loc_offset_loc.
    by apply has_layout_loc_offset_loc.
  Qed.
  Definition type_bin_op_offset_array_ptr_inst := [instance type_bin_op_offset_array_ptr].
  Global Existing Instance type_bin_op_offset_array_ptr_inst.

  Lemma type_bin_op_neg_offset_array_ptr l β ly it v i idx (len : nat) base T:
    ⌜layout_wf ly⌝ ∗ ⌜0 ≤ idx - i ≤ len⌝ ∗ (l ◁ₗ{β} array_ptr ly base idx len -∗ T (val_of_loc (base offset{ly}ₗ (idx - i))) ((base offset{ly}ₗ (idx - i)) @ &own (array_ptr ly base (idx - i) len)))
    ⊢ typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array_ptr ly base idx len) (PtrNegOffsetOp ly) (IntOp it) PtrOp T.
  Proof.
    iIntros "[% [% HT]]". unfold int; simpl_type.
    iIntros "%Hv (->&%&%&#Hlib)" (Φ) "HΦ".
    iApply wp_ptr_neg_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; unfold addr in *; [done|nia|].
      rewrite {3}/ly_size/=. nia. }
    rewrite offset_loc_offset_loc Z.add_opp_r.
    iModIntro. iApply "HΦ"; [|iApply "HT"]; unfold frac_ptr; simpl_type; iFrame "Hlib"; iPureIntro; [|done].
    split_and! => //; try lia. rewrite -Z.add_opp_r -offset_loc_offset_loc.
    by apply has_layout_loc_offset_loc.
  Qed.
  Definition type_bin_op_neg_offset_array_ptr_inst := [instance type_bin_op_neg_offset_array_ptr].
  Global Existing Instance type_bin_op_neg_offset_array_ptr_inst.

  Lemma type_write_array_ptr l base β ot v ty ly idx (len : nat) T:
    typed_write_end false ⊤ ot v ty l β (array_ptr ly base idx len) T :-
      ∃ tys,
      exhale base ◁ₗ{β} array ly tys;
      exhale ⌜idx < length tys⌝ ;
      exhale ⌜len = length tys ⌝;
      ∀ tyl,
      inhale ⌜tys !! Z.to_nat idx = Some tyl⌝;
      tyv ← {typed_write_end false ⊤ ot v ty l β tyl };
      inhale base ◁ₗ{β} array ly (<[(Z.to_nat idx):=tyv]> tys);
      {T (array_ptr ly base idx len) }.
  Proof.
    iIntros "HT". iApply typed_write_end_mono_strong; [done|]. iIntros "Hv Hptr !>".
    rewrite !/(ty_own (array_ptr _ _ _ _))/=. iDestruct "Hptr" as "(-> & % & % & Hb)".
    liFromSyntax. iDestruct "HT" as (tys) "(Harr & % & % & HT)".
    rewrite !/(ty_own (array _ _))/=. iDestruct "Harr" as "[% [#Hinb Hcontents]]".
    have [|tyl ?]:= lookup_lt_is_Some_2 tys (Z.to_nat idx); [lia|].
    iDestruct (big_sepL_insert_acc with "Hcontents") as "[Hl Hc]" => //.
    rewrite Z2Nat.id//; [|lia]. iDestruct ("HT" with "[//]") as "HT".
    iFrame "Hv Hl". iExists True%I. iSplit; [done|]. iApply (typed_write_end_wand with "HT").
    iIntros (ty') "Harr _ Hoffset !>". iExists _. iSplitL "Hb"; last first.
    - iApply "Harr". rewrite !/(ty_own (array _ _))/=. iSplit; [done|].
      rewrite length_insert. iFrame "#". by iApply "Hc".
    - by iFrame.
  Qed.
  Definition type_write_array_ptr_inst := [instance type_write_array_ptr].
  Global Existing Instance type_write_array_ptr_inst | 10.

  Lemma type_read_array_ptr l base β ot mc ly idx (len : nat) T:
    typed_read_end false ⊤ l β (array_ptr ly base idx len) ot mc T :-
      ∃ tys,
      exhale base ◁ₗ{β} array ly tys;
      exhale ⌜idx < length tys ⌝;
      exhale ⌜len = length tys ⌝;
      ∀ ty,
      inhale ⌜tys !! Z.to_nat idx = Some ty⌝;
      v, tyl, tyv ← {typed_read_end false ⊤ l β ty ot mc };
      inhale base ◁ₗ{β} array ly (<[(Z.to_nat idx):=tyl]> tys);
      {T v (array_ptr ly base idx len) tyv }.
  Proof.
    iIntros "HT". iApply typed_read_end_mono_strong; [done|]. iIntros "H !>".
    rewrite !/(ty_own (array_ptr _ _ _ _))/=. iDestruct "H" as "(->&%&%&Hb)".
    liFromSyntax. iDestruct "HT" as (tys) "(Harr&%&->&HT)".
    rewrite !/(ty_own (array _ _))/=. iDestruct "Harr" as "[% [#Hinb Hcontents]]".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat idx); [lia|].
    iDestruct (big_sepL_insert_acc with "Hcontents") as "[Hl Hc]" => //.
    rewrite Z2Nat.id//; [|lia]. iDestruct ("HT" with "[//]") as "HT".
    iFrame "Hl". iExists True%I. iSplit; [done|]. iApply (typed_read_end_wand with "HT").
    iIntros (v ty1 ty2) "Hupdate ? Hoffset Hv !>".
    iDestruct ("Hc" with "Hoffset") as "Hc". rewrite !/(ty_own (array _ _))/=.
    rewrite length_insert. iFrame. iExists _. iSplitR; last first.
    - iApply "Hupdate"; by iFrame.
    - by do 3 (iSplit; [done|]).
  Qed.
  Definition type_read_array_ptr_inst := [instance type_read_array_ptr].
  Global Existing Instance type_read_array_ptr_inst | 10.

  Lemma type_bin_op_diff_array_ptr_array l1 β l2 ly idx (len : nat) tys T:
    (l1 ◁ₗ{β} array_ptr ly l2 idx len -∗
    l2 ◁ₗ{β} array ly tys -∗
    ⌜0 < ly.(ly_size)⌝ ∗
    ⌜0 < length tys⌝ ∗
    ⌜idx ≤ max_int ptrdiff_t⌝ ∗
    (alloc_alive_loc l2 ∗ True) ∧
    (T (i2v idx ptrdiff_t) (idx @ int ptrdiff_t)))
    ⊢ typed_bin_op l1 (l1 ◁ₗ{β} array_ptr ly l2 idx len) l2 (l2 ◁ₗ{β} array ly tys) (PtrDiffOp ly) PtrOp PtrOp T.
  Proof.
    iIntros "HT (->&%&%&#Hlib) Hl2" (Φ) "HΦ".
    iDestruct ("HT" with "[$Hlib//] Hl2") as (? ? ?) "HT".
    have /(val_of_Z_is_Some None) [vo Hvo] : idx ∈ ptrdiff_t. {
      split; [|done].
      rewrite /min_int/=/int_half_modulus/=/bits_per_int/bytes_per_int/=/bits_per_byte. lia.
    }
    rewrite /i2v Hvo/=.
    iApply wp_ptr_diff; [by apply: val_to_of_loc|by apply: val_to_of_loc| |done|done| | |].
    { rewrite /= Z.add_simpl_l Z.mul_comm Z.div_mul //. lia. }
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; unfold addr in *; [done|nia|].
      rewrite {2}/ly_size/=. nia. }
    { iApply (loc_in_bounds_shorten with "Hlib"). lia. }
    iSplit. {
      iApply alloc_alive_loc_mono; [simpl; done|].
      iDestruct "HT" as "[[$ _] _]".
    }
    iDestruct "HT" as "[_ HT]".
    iModIntro. iApply "HΦ"; [|iApply "HT"].
    unfold int; simpl_type. iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_bin_op_diff_array_ptr_array_inst := [instance type_bin_op_diff_array_ptr_array].
  Global Existing Instance type_bin_op_diff_array_ptr_array_inst.

  Lemma subsume_array_ptr_alloc_alive A M β l ly base idx len T:
    (alloc_alive_loc base ∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} array_ptr ly base idx len) M (λ x : A, alloc_alive_loc l) T.
  Proof.
    iIntros "[Halive [% ?]] (->&?) !>".
    iExists _. iFrame. by iApply (alloc_alive_loc_mono with "Halive").
  Qed.
  Definition subsume_array_ptr_alloc_alive_inst := [instance subsume_array_ptr_alloc_alive].
  Global Existing Instance subsume_array_ptr_alloc_alive_inst | 10.

  Lemma simpl_goal_array_ptr ly base idx1 idx2 (len : nat) β M T:
     simplify_goal M ((base offset{ly}ₗ idx1) ◁ₗ{β} array_ptr ly base idx2 len) T :-
     exhale ⌜idx1 = idx2⌝;
     exhale ⌜(base offset{ly}ₗ idx1) `has_layout_loc` ly⌝;
     exhale ⌜0 ≤ idx1 ≤ len⌝;
     exhale loc_in_bounds base (ly_size (mk_array_layout ly len));
     {T}.
  Proof. by iIntros "(->&%&%&$&$) !>". Qed.
  Definition simpl_goal_array_ptr_inst := [instance simpl_goal_array_ptr with 50%N].
  Global Existing Instance simpl_goal_array_ptr_inst.

  Lemma subsume_array_ptr A M ly1 ly2 base1 base2 idx1 idx2 len1 len2 l β T:
    (∃ x, ⌜ly1 = ly2 x⌝ ∗ ⌜base1 = base2 x⌝ ∗ ⌜idx1 = idx2 x⌝ ∗ ⌜len1 = len2 x⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} array_ptr ly1 base1 idx1 len1) M
        (λ x : A, l ◁ₗ{β} array_ptr (ly2 x) (base2 x) (idx2 x) (len2 x)) T.
  Proof. iIntros "(%&->&->&->&->&?) ? !>". iExists _. iFrame. Qed.
  Definition subsume_array_ptr_inst := [instance subsume_array_ptr].
  Global Existing Instance subsume_array_ptr_inst.

  (*
  TODO: The following rule easily leads to diverging if the hypothesis is simplified before it is introduced into the context.
  Lemma simplify_array_ptr_hyp_learn_loc l β ly base idx len T:
    (⌜l = base offset{ly}ₗ idx⌝ -∗ l ◁ₗ{β} array_ptr ly base idx len -∗ T
    ⊢ simplify_hyp (l ◁ₗ{β} array_ptr ly base idx len) T.
  Proof. iIntros "HT [% #Hlib]". iApply "HT" => //. by iSplit. Qed.
  Global Instance simplify_array_ptr_hyp_learn_loc_inst l β ly base idx len `{!TCUnless (TCFastDone (l = base offset{ly}ₗ idx))}:
    SimplifyHyp _ (Some 0%N) | 10 :=
    λ T, i2p (simplify_array_ptr_hyp_learn_loc l β ly base idx len T).
*)

  Lemma simplify_hyp_array_ptr ly l β base idx len M T:
     simplify_hyp (l ◁ₗ{β} array_ptr ly base idx len) M T :-
     inhale ⌜l = base offset{ly}ₗ idx⌝;
     inhale ⌜(base offset{ly}ₗ idx) `has_layout_loc` ly⌝;
     inhale loc_in_bounds base (ly_size (mk_array_layout ly len));
     ‖M‖ ∃ tys : list type,
     exhale base ◁ₗ{β} array ly tys;
     exhale ⌜0 ≤ idx < length tys⌝;
     ∀ ty : type,
     inhale ⌜tys !! Z.to_nat idx = Some ty⌝;
     inhale base ◁ₗ{β} array ly (<[Z.to_nat idx:=place l]> tys);
     inhale l ◁ₗ{β} ty;
     ‖M‖ return T.
  Proof.
    iIntros "HT (->&%&%&?)".
    iMod ("HT" with "[//] [//] [$]") as (tys) "(Harray&%&HT)".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat idx). 1: lia.
    iDestruct (array_get_type (Z.to_nat idx) with "Harray") as "[Hty Harray]"; [done|].
    rewrite Z2Nat.id; [|lia].
    by iApply ("HT" with "[//] Harray Hty").
  Qed.
  Definition simplify_hyp_array_ptr_inst := [instance simplify_hyp_array_ptr with 50%N].
  Global Existing Instance simplify_hyp_array_ptr_inst | 50.

(*** sized_array typing rules *)
  Lemma sized_array_replicate_uninit_equiv l β ly n:
    layout_wf ly →
    l ◁ₗ{β} sized_array ly (replicate n (uninit ly)) n ⊣⊢ l ◁ₗ{β} uninit (mk_array_layout ly n).
  Proof.
    rewrite /ty_own/= => ?. iSplit.
    - iInduction n as [|n] "IH" forall (l) => /=; iIntros "(%&%&Hlib&Htys)". {
        iExists []. rewrite heap_mapsto_own_state_nil Nat.mul_0_r Forall_nil.
        iFrame "Hlib". iPureIntro. rewrite /has_layout_val/ly_size/=. naive_solver lia.
      }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      iDestruct "Htys" as "[Hty Htys]".
      iDestruct (loc_in_bounds_split_mul_S with "Hlib") as "[#Hlib1 Hlib2]".
      iDestruct ("IH" with "[Hlib2 Htys]") as (v2 Hv2 ? _) "Hv2".
      { iFrame. iPureIntro. revert select (layout_wf _). revert select (_ `has_layout_loc` _).
        rewrite /has_layout_loc /layout_wf /aligned_to. case_match => //.
        - move => /= [? ->] [? ->]. eexists.
          + rewrite -Z.mul_add_distr_r. by apply Z.divide_factor_r.
          + destruct l as [? a]. lia.
        - intros. split => //. lia.
      }
      rewrite {2}/ty_own/=. iDestruct "Hty" as (v1 Hv1 Hl1 _) "Hv1".
      iExists (v1 ++ v2). rewrite heap_mapsto_own_state_app Hv1 /has_layout_val length_app Hv1 Hv2.
      iFrame. rewrite Forall_forall. iPureIntro. split_and! => //.
      rewrite {2 3}/ly_size/=. lia.
    - iDestruct 1 as (v Hv Hl _) "Hl". iSplit => //.
      iInduction n as [|n] "IH" forall (v l Hv Hl) => /=. {
        rewrite Nat.mul_0_r. iSplitR => //. iSplitL => //.
        iApply loc_in_bounds_shorten; last by iApply heap_mapsto_own_state_loc_in_bounds. lia.
      }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      rewrite -(take_drop (ly.(ly_size)) v) heap_mapsto_own_state_app.
      iDestruct "Hl" as "[Hl Hr]". rewrite length_take_le ?Hv; last by repeat unfold ly_size => /=; lia.
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "#Hbl".
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hr") as "#Hbr".
      iDestruct ("IH" with "[] [] Hr") as "[%Hlen [Hb Hh]]".
      { iPureIntro. rewrite /has_layout_val length_drop Hv. repeat unfold ly_size => /=; lia. }
      { iPureIntro. by apply has_layout_loc_ly_mult_offset. }
      iSplitR; [by iPureIntro; lia|]. iSplitR.
      + iApply loc_in_bounds_split_mul_S.
        rewrite length_take min_l; last first.
        { rewrite Hv. repeat unfold ly_size => /=; lia. }
        iFrame "Hbl". rewrite length_replicate length_drop Hv.
        destruct ly as [k?]. repeat unfold ly_size => /=.
        have ->: (k * n = k * S n - k)%nat by lia. done.
      + iSplitL "Hl"; [|done]. iExists _. iFrame. iPureIntro. rewrite Forall_forall.
        split_and! => //. rewrite /has_layout_val length_take_le ?Hv; repeat unfold ly_size => /=; lia.
  Qed.

  (* The following rules conflict with `array` and are removed for the time being *)
  (* Lemma simplify_hyp_uninit_sized_array ly l β n T: *)
  (*   ⌜layout_wf ly⌝ ∗ (l ◁ₗ{β} sized_array ly (replicate n (uninit ly)) n -∗ T) *)
  (*   ⊢ simplify_hyp (l ◁ₗ{β} uninit (mk_array_layout ly n)) T. *)
  (* Proof. iIntros "[% HT] Hl". iApply "HT". rewrite sized_array_replicate_uninit_equiv // {1}/ly_size/=. Qed. *)
  (* Definition simplify_hyp_uninit_sized_array_inst := [instance simplify_hyp_uninit_sized_array with 50%N]. *)
  (* Global Existing Instance simplify_hyp_uninit_sized_array_inst. *)

  (* Lemma simplify_goal_uninit_sized_array ly l β n T: *)
  (*   ⌜layout_wf ly⌝ ∗ l ◁ₗ{β} sized_array ly (replicate n (uninit ly)) n ∗ T *)
  (*   ⊢ simplify_goal (l ◁ₗ{β} uninit (mk_array_layout ly n)) T. *)
  (* Proof. iIntros "[% [? $]]". rewrite sized_array_replicate_uninit_equiv //. Qed. *)
  (* Definition simplify_goal_uninit_sized_array_inst := [instance simplify_goal_uninit_sized_array with 50%N]. *)
  (* Global Existing Instance simplify_goal_uninit_sized_array_inst. *)

  Lemma subsume_sized_array_array_ptr A M β l ly idx alen len tys T:
    (l ◁ₗ{β} sized_array ly tys alen -∗ ‖M‖ ∃ x, ⌜idx x = 0⌝ ∗ ⌜len x = length tys⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} sized_array ly tys alen)
        M (λ x : A, l ◁ₗ{β} array_ptr ly l (idx x) (len x)) T.
  Proof.
    iIntros "Hsub Harr". iDestruct "Harr" as "[% [% [#? Hlist]]]".
    iMod ("Hsub" with "[Hlist]") as (? Hoffset Hlen) "HT". { by iFrame "# ∗". }
    iModIntro. iFrame. rewrite Hoffset Hlen. unfold array_ptr; simpl_type.
    unfold ly_size at 2; simpl. iFrame "#". repeat iSplit; iPureIntro;
      [ by rewrite offset_loc_0 | done | done | lia ].
  Qed.
  Definition subsume_sized_array_array_ptr_inst := [instance subsume_sized_array_array_ptr].
  Global Existing Instance subsume_sized_array_array_ptr_inst | 10.

  (* TODO: generalize this rule, maybe similar to [subsume_array_uninit]? *)
  Lemma subsume_uninit_sized_array_replicate A M l β n (ly1 : layout) ly2 T:
    (∃ x, ⌜layout_wf ly2⌝ ∗ ⌜ly1 = mk_array_layout ly2 n⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} uninit ly1) M (λ x : A, l ◁ₗ{β} sized_array ly2 (replicate n (uninit ly2)) n)  T.
  Proof. iIntros "(%&%&->&?) ? !>". iExists _. iFrame. by rewrite sized_array_replicate_uninit_equiv. Qed.
  Definition subsume_uninit_sized_array_replicate_inst := [instance subsume_uninit_sized_array_replicate].
  Global Existing Instance subsume_uninit_sized_array_replicate_inst.

  Lemma subsume_sized_array_uninit A M l β tys ly1 ly2 len T:
    (l ◁ₗ{β} sized_array ly2 tys len -∗
      ‖M‖ ⌜layout_wf ly2⌝ ∗ l ◁ₗ{β} sized_array ly2 (replicate (length tys) (uninit ly2)) len ∗
      ∃ x, ⌜ly1 x = mk_array_layout ly2 (length tys)⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} sized_array ly2 tys len) M (λ x : A, l ◁ₗ{β} uninit (ly1 x)) T.
  Proof.
    iIntros "Hsub Harr". iMod ("Hsub" with "[Harr]") as (?) "[Harr [% [%Heq HT]]]".
    { iDestruct "Harr" as "[%Hly [%Hlen [#Hlib Htys]]]". repeat iSplit => //. }
    iModIntro. iFrame. rewrite Heq -sized_array_replicate_uninit_equiv => //.
    iDestruct "Harr" as "(Hly&%Hlen&Hloc&Hlist)".
    iFrame. iPureIntro. by rewrite length_replicate.
  Qed.
  Definition subsume_sized_array_uninit_inst := [instance subsume_sized_array_uninit].
  Global Existing Instance subsume_sized_array_uninit_inst.

  Lemma type_place_sized_array l β ly1 it v tyv tys ly2 len K T:
  typed_place (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (sized_array ly2 tys len) T :-
     inhale v ◁ᵥ tyv;
     ∃ i : Z,
     exhale ⌜ly1 = ly2⌝;
     exhale v ◁ᵥ i @ int it;
     exhale ⌜0 ≤ i⌝;
     exhale ⌜i < length tys⌝;
     ∀ ty : type,
     inhale ⌜tys !! Z.to_nat i = Some ty⌝;
     {typed_place K (l offset{ly2}ₗ i) β ty
        (λ (l2 : loc) (β2 : own_state) (ty2 : type) (typ : type → type),
           T l2 β2 ty2 (λ t : type, sized_array ly2 (<[Z.to_nat i:=typ t]> tys) len))}.
  Proof.
    iIntros "HT" (Φ) "(%&%Hlenty&#Hb&Hl) HΦ" => /=. iIntros "Hv".
    iDestruct ("HT" with "Hv") as (i ->) "HP". unfold int; simpl_type.
    iDestruct ("HP") as (Hv ? Hlen) "HP".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat i). 1: lia.
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hb"); simpl; [done| destruct l => /=; lia | destruct l => /=; nia]. }
    iIntros "!#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hl Hc]" => //. rewrite Z2Nat.id//.
    iApply ("HP" $! ty with "[//] Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[Hoffs $]".
    iSplitR => //. iSplitR; first by rewrite length_insert.
    iSplitR; [by rewrite length_insert | by iApply "Hc"].
  Qed.
  Definition type_place_sized_array_inst := [instance type_place_sized_array].
  Global Existing Instance type_place_sized_array_inst.

  Lemma type_bin_op_offset_sized_array l β ly it v tys len i T:
    (* TODO: Should we make layout_wf ly part of array such that we don't need to require it here? *)
    ⌜layout_wf ly⌝ ∗ ⌜0 ≤ i ≤ length tys⌝ ∗ (l ◁ₗ{β} sized_array ly tys len -∗ T (val_of_loc (l offset{ly}ₗ i)) ((l offset{ly}ₗ i) @ &own (array_ptr ly l i len)))
    ⊢ typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} sized_array ly tys len) (PtrOffsetOp ly) (IntOp it) PtrOp T.
  Proof.
    iIntros "[% [% HT]]". unfold int; simpl_type.
    iIntros "%Hv (%&%&#Hlib&Hlen)" (Φ) "HΦ".
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done| destruct l => /=; lia | destruct l => /=; nia]. }
    iModIntro. iApply "HΦ" ; [|iApply "HT"; by do 3 iSplitR => //].
    unfold frac_ptr; simpl_type. iSplit; [done|]. iSplit; [done|].
    iSplitR.
    - iPureIntro. by apply: has_layout_loc_offset_loc.
    - subst len. iSplitR => //.
  Qed.
  Definition type_bin_op_offset_sized_array_inst := [instance type_bin_op_offset_sized_array].
  Global Existing Instance type_bin_op_offset_sized_array_inst.


  Lemma type_bin_op_diff_array_ptr_sized_array l1 β l2 ly idx (len : nat) tys T:
    (l1 ◁ₗ{β} array_ptr ly l2 idx len -∗
    l2 ◁ₗ{β} sized_array ly tys len -∗
    ⌜0 < ly.(ly_size)⌝ ∗
    ⌜0 < length tys⌝ ∗
    ⌜idx ≤ max_int ptrdiff_t⌝ ∗
    (alloc_alive_loc l2 ∗ True) ∧
    (T (i2v idx ptrdiff_t) (idx @ int ptrdiff_t)))
    ⊢ typed_bin_op l1 (l1 ◁ₗ{β} array_ptr ly l2 idx len) l2 (l2 ◁ₗ{β} sized_array ly tys len) (PtrDiffOp ly) PtrOp PtrOp T.
  Proof.
    iIntros "HT (->&%&%&#Hlib) Hl2" (Φ) "HΦ".
    iDestruct ("HT" with "[$Hlib//] Hl2") as (? ? ?) "HT".
    have /(val_of_Z_is_Some None) [vo Hvo] : idx ∈ ptrdiff_t. {
      split; [|done].
      rewrite /min_int/=/int_half_modulus/=/bits_per_int/bytes_per_int/=/bits_per_byte. lia.
    }
    rewrite /i2v Hvo/=.
    iApply wp_ptr_diff; [by apply: val_to_of_loc|by apply: val_to_of_loc| |done|done| | |].
    { rewrite /= Z.add_simpl_l Z.mul_comm Z.div_mul //. lia. }
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; unfold addr in *; [done|nia|].
      rewrite {2}/ly_size/=. nia. }
    { iApply (loc_in_bounds_shorten with "Hlib"). lia. }
    iSplit.
    { iApply alloc_alive_loc_mono; [simpl; done|]. iDestruct "HT" as "[[$ _] _]". }
    iDestruct "HT" as "[_ HT]".
    iModIntro. iApply "HΦ"; [|iApply "HT"].
    unfold int; simpl_type. iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_bin_op_diff_array_ptr_sized_array_inst := [instance type_bin_op_diff_array_ptr_sized_array].
  Global Existing Instance type_bin_op_diff_array_ptr_sized_array_inst.

  Lemma split_array β p l (offs:nat) ly ls:
    p ◁ₗ{β} array ly ls -∗
    l ◁ₗ{β} array_ptr ly p offs (length ls) -∗
    p ◁ₗ{β} array ly (take offs ls) ∗ l ◁ₗ{β} array ly (drop offs ls).
  Proof.
    iIntros "[%Hply [#Hpbounds Hplist]] [%Hloffs [%Hlly [%Hoffslen _]]]".
    have Hmin: ((offs `min` length ls)=offs)%nat by lia.
    rewrite (big_sepL_take_drop _ _ offs).
    have -> : (length ls = (offs + (length ls - offs))%nat) by lia.
    rewrite Nat.mul_add_distr_l.
    iDestruct (loc_in_bounds_split with "Hpbounds") as "[#Hbtake #Hbdrop]".
    iDestruct "Hplist" as "[Htake Hdrop]". iSplitR "Hdrop".
    - iSplitR => //; last iFrame. by rewrite length_take Hmin.
    - iSplitR => //. rewrite length_drop Hloffs. iSplitR.
      + by replace (Z.of_nat (ly_size ly * offs)) with ((Z.of_nat (ly_size ly)) * (Z.of_nat (offs))) by lia.
      + iApply big_sepL_mono => //. intros => //=. rewrite offset_loc_offset_loc.
        by replace (Z.of_nat (offs + k)) with (Z.of_nat offs + Z.of_nat k) by lia.
  Qed.

  Lemma split_sized_array β p ly ls (len: nat) (offs: nat):
    layout_wf ly →
    offs ≤ length ls →
    p ◁ₗ{β} sized_array ly ls len -∗
    offset_loc p ly offs ◁ₗ{β} sized_array ly (drop offs ls) (len - offs) ∗
    p ◁ₗ{β} sized_array ly (take offs ls) offs .
  Proof.
    iIntros "%Hlwf %Hleq (%Hly&%Hlen&#Hbounds&Hlist)".
    have Hmin: ((offs `min` length ls)=offs)%nat. {
      destruct (decide (offs ≤ length ls)); [lia|].
      destruct n; lia.
    }
    rewrite (big_sepL_take_drop _ _ offs).
    have Heq: (length ls = (offs + (length ls - offs))%nat) by lia.
    rewrite Heq Nat.mul_add_distr_l.
    iDestruct (loc_in_bounds_split with "Hbounds") as "[#Hbtake #Hbdrop]".
    iDestruct "Hlist" as "[Htake Hdrop]". iSplitR "Htake".
    - iSplitR; first by iPureIntro; apply has_layout_loc_offset_loc => //.
      rewrite length_drop. iSplit; first by iPureIntro; rewrite Hlen.
      iSplitR => //.
      + by replace (Z.of_nat (ly_size ly * offs))
        with ((Z.of_nat (ly_size ly)) * (Z.of_nat (offs))) by lia.
      + iApply big_sepL_mono => //. intros => //=. rewrite offset_loc_offset_loc.
        by replace (Z.of_nat (offs + k)) with (Z.of_nat offs + Z.of_nat k) by lia.
    - iSplitR => //. rewrite length_take Hmin. iSplit; first by iPureIntro.
      iSplitR => //.
  Qed.

  Lemma merge_sized_array_concat β p ly ls1 ls2 (len: nat) (offs: nat):
    offs ≤ len →
    p ◁ₗ{β} sized_array ly ls1 offs -∗
    offset_loc p ly offs ◁ₗ{β} sized_array ly ls2 (len - offs) -∗
    p ◁ₗ{β} sized_array ly (ls1 ++ ls2) len.
  Proof.
    iIntros "%Hoffs (%Hly1&%Hlen1&#Hb1&Hlist1) (%Hly2&%Hlen2&#Hb2&Hlist2)".
    have Hlen: len = length (ls1 ++ ls2).
    { rewrite length_app. lia. }
    iSplitR => //. iSplitR "Hlist1 Hlist2"; first by iPureIntro.
    iSplitR.
    - rewrite length_app Nat.mul_add_distr_l -loc_in_bounds_split.
      iSplitR => //. rewrite Hlen1. unfold offset_loc.
      by replace (Z.of_nat (ly_size ly * offs))
        with ((Z.of_nat (ly_size ly)) * (Z.of_nat (offs))) by lia.
    - rewrite big_sepL_app. iSplitL "Hlist1" => //.
      iApply big_sepL_mono => //. intros => //=.
      rewrite offset_loc_offset_loc Hlen1.
      by replace (Z.of_nat (offs + k)) with (Z.of_nat offs + Z.of_nat k) by lia.
  Qed.

  Lemma merge_sized_array β p ly ls (len offs: nat):
    offs ≤ len →
    p ◁ₗ{β} sized_array ly (take offs ls) offs -∗
    offset_loc p ly offs ◁ₗ{β} sized_array ly (drop offs ls) (len - offs) -∗
    p ◁ₗ{β} sized_array ly ls len.
  Proof.
    iIntros (Hoffs) "Hl Hr".
    iDestruct (merge_sized_array_concat with "Hl Hr") as "H" => //.
    by rewrite take_drop.
  Qed.

  Lemma subsume_sized_array_split A M ly1 ly2 tys1 tys2 (len1: nat) (len2: nat) l β T:
    subsume (l ◁ₗ{β} sized_array ly1 tys1 len1) M (λ x : A, l ◁ₗ{β} sized_array ly2 (tys2 x) len2) T
      where `{!CanSolve (len2 < len1)} :-
        (* Check that layout is well-formed *)
        exhale ⌜ layout_wf ly1 ⌝;

        (* Check that layouts are identical *)
        exhale ⌜ ly1 = ly2 ⌝;

        (* add the second part of the array to context  *)
        inhale offset_loc l ly1 len2 ◁ₗ{β} sized_array ly1 (drop len2 tys1) (len1 - len2);

        (* subsume between equal sizes *)
        inhale l ◁ₗ{β} sized_array ly1 (take len2 tys1) len2;

        ‖M‖ ∃ x, exhale l ◁ₗ{β} sized_array ly2 (tys2 x) len2;
        return (T x).
  Proof.
    liFromSyntax.
    iIntros (Hleneq) "[%Hwf [%Hlyeq Hwand]] Harr".
    unfold CanSolve in Hleneq.
    iDestruct "Harr" as "(%Hly&%Hlen&#Hbounds&Hlist)".
    iPoseProof (split_sized_array _ _ _ tys1 len1 len2) as "Hsplit"; [done|lia|].
    iDestruct ("Hsplit" with "[Hbounds Hlist]") as "[Harr1' Harr2']"; first by do 3 iSplitR => //.
    iSpecialize ("Hwand" with "Harr1' Harr2'"). iFrame.
  Qed.
  Definition subsume_sized_array_split_inst := [instance subsume_sized_array_split].
  Global Existing Instance subsume_sized_array_split_inst | 10.

  Lemma subsume_array_ptr_sized_array A M β l p ly idx len alen lst T:
    subsume (l ◁ₗ{β} array_ptr ly p idx len) M
        (λ x : A, l ◁ₗ{β} sized_array ly (lst x) (alen x)) T :-
        (* Check that layout is well-formed *)
        exhale ⌜ layout_wf ly ⌝;

        (* Find array the pointer is pointing to  *)
        ∃ ls, exhale p ◁ₗ{β} sized_array ly ls len;

        (* add the first part of the array to context  *)
        inhale p ◁ₗ{β} sized_array ly (take (Z.to_nat idx) ls) (Z.to_nat idx);

        (* Subsume the second part of the array to the wanted layout *)
        x ← (l ◁ₗ{β} sized_array ly (drop (Z.to_nat idx) ls) (len - Z.to_nat idx)) :‖M‖>
              (λ x, l ◁ₗ{β} sized_array ly (lst x) (alen x));
        return (T x).
  Proof.
    liFromSyntax.
    iIntros "(%Hwf&%ls&Harr&Hmw) (%Hloc&%Hly&%Hidxlen&Hboundslen)".
    iDestruct "Harr" as "(%Hly1&%Hlen1&#Hbounds1&Hlist1)".
    iDestruct ((split_sized_array _ _ _ ls len (Z.to_nat idx)) with "[Hbounds1 Hlist1]") as "[Hr Hl]" => //.
    - subst. lia.
    - do 3 iSplitR => //.
    - iApply ("Hmw" with "[Hboundslen Hl] [Hr]").
      + iSplitR => //.
        have Hmin: ((Z.to_nat idx `min` length ls) = (Z.to_nat idx))%nat by lia.
        iSplitR => //.
        * rewrite length_take Hmin. by iPureIntro.
        * iDestruct "Hl" as "(%Hlly&%Hllen&#Hlbounds&Hllist)". iSplit => //.
      + iSplitR => //.
        iDestruct "Hr" as "(%Hlly&%Hllen&#Hlbounds&Hllist)".
        replace (Z.of_nat (Z.to_nat idx)) with idx by lia.
        iSplitR => //. iSplitR => //.
        * rewrite length_drop Nat.mul_sub_distr_l Hloc => //.
        * rewrite Hloc. iApply big_sepL_mono => //.
          intros => //.
  Qed.
  Definition subsume_array_ptr_sized_array_inst := [instance subsume_array_ptr_sized_array].
  Global Existing Instance subsume_array_ptr_sized_array_inst | 10.

  (* Two sized arrays with same lengths *)
  Lemma subsume_sized_array A M ly1 ly2 tys1 tys2 len1 len2 l β T:
    subsume (l ◁ₗ{β} sized_array ly1 tys1 len1) M (λ x : A, l ◁ₗ{β} sized_array ly2 (tys2 x) len2) T
      where `{!CanSolve (len1 = len2)} :-
      exhale ⌜ ly1 = ly2 ⌝;
      ∀ id,
      x ← (sep_list id type [] tys1 (λ i ty, (l offset{ly1}ₗ i) ◁ₗ{β} ty)) :‖M‖>
          (λ x, sep_list id type [] (tys2 x) (λ i ty, (l offset{ly1}ₗ i) ◁ₗ{β} ty));
      return (T x).
  Proof.
    liFromSyntax.
    iIntros (Hleneq) "[%Hlyeq Hsl] Harr". subst. unfold CanSolve in Hleneq.
    iDestruct "Harr" as "(%Hly&%Hlen&#Hbounds&Hlist)".
    set sl_id := (Build_sep_list_id len2). unfold subsume.
    iSpecialize ("Hsl" $! sl_id)%I.
    unfold sep_list. subst len2.
    iMod ("Hsl" with "[Hlist]") as (x) "[[%Hlen2 Hlist] HT]".
    { iSplitR => //. }
    iModIntro. iExists x. rewrite !/(ty_own (sized_array _ _ _))/=.
    iFrame. iSplitR; [by iPureIntro|].
    iSplit; [by iPureIntro|].
    simpl in Hlen2. by replace (length tys1) with (length (tys2 x)) by lia.
  Qed.
  Definition subsume_sized_array_inst := [instance subsume_sized_array].
  Global Existing Instance subsume_sized_array_inst | 8.

  (* merge rule *)
  Lemma subsume_sized_array_merge A M ly1 ly2 tys1 tys2 (len1: nat) (len2: nat) l β T:
    subsume (l ◁ₗ{β} sized_array ly1 tys1 len1) M (λ x : A, l ◁ₗ{β} sized_array ly2 (tys2 x) len2) T
      where `{!CanSolve (len1 ≤ len2)} :-
        (* Check that layouts are identical *)
        exhale ⌜ ly1 = ly2 ⌝;

        (* Get right part of array *)
        ∃ tys, exhale offset_loc l ly1 len1 ◁ₗ{β} sized_array ly1 (tys) (len2 - len1);

        (* Subsume *)
        inhale (l ◁ₗ{β} sized_array ly1 (tys1 ++ tys) len2);

        ‖M‖ ∃ x, exhale l ◁ₗ{β} sized_array ly2 (tys2 x) len2;
        return (T x).
  Proof.
    liFromSyntax.
    iIntros (Hlen) "[%Hly [% [Hdrop Hsubs]]] Harr". unfold CanSolve in Hlen.
    iApply "Hsubs". iApply (merge_sized_array_concat with "[Harr]") => //.
  Qed.
  Definition subsume_sized_array_merge_inst := [instance subsume_sized_array_merge].
  Global Existing Instance subsume_sized_array_merge_inst | 10.

  (* Write to sized_array pointer *)
  Lemma type_write_sized_array l β ot v ty ly tys (len : nat) T:
    typed_write_end false ⊤ ot v ty l β (sized_array ly tys len) T :-
      (* Don't write OOB *)
      exhale ⌜0 < len⌝;
      exhale ⌜len = length tys ⌝;
      (* For all tyl at the specified index *)
      ∀ tyl,
      inhale ⌜tys !! Z.to_nat 0 = Some tyl⌝;
      tyv ← {typed_write_end false ⊤ ot v ty l β tyl };
      {T (sized_array ly (<[(Z.to_nat 0) := tyv]> tys) len) }.
  Proof.
    liFromSyntax. iIntros "[%Hlen [%Hlength H2]]". subst.
    have Hlen2 : (0 < length tys)%nat by lia.
    iApply typed_write_end_mono_strong; [done|].
    iIntros "Hv Hasgn !>".
    iDestruct "Hasgn" as "(%H1&%_&#Hbounds&Hl)".
    have [|ty1 Hlookup] := lookup_lt_is_Some_2 tys (Z.to_nat 0); [lia|].
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hasgn Hy]" => //.
    rewrite offset_loc_0. iDestruct ("H2" with "[//]") as "Hwrite".
    iFrame "Hv Hasgn". iExists True%I. iSplit; [done|].
    iApply (typed_write_end_wand with "Hwrite").
    iIntros (ty3) "HT _ Hl !>". iExists _. iSplitR "HT"; last by iFrame.
    iSplit => //. rewrite length_insert. iSplit => //.
    iDestruct ("Hy" with "Hl") as "Hsep". by iFrame.
  Qed.
  Definition type_write_sized_array_inst := [instance type_write_sized_array].
  Global Existing Instance type_write_sized_array_inst | 10.

  (* Read from sized_array pointer *)
  Lemma type_read_sized_array l β ot mc ly (len : nat) tys T:
    typed_read_end false ⊤ l β (sized_array ly tys len) ot mc T :-
      (* Don't read OOB *)
      exhale ⌜0 < len⌝;
      exhale ⌜len = length tys⌝;
      (* For all ty at the _specified index_ *)
      ∀ ty,
      inhale ⌜tys !! Z.to_nat 0 = Some ty⌝;
      (* Convert to typed_read of the VALUE, function call *)
      v, tyl, tyv ← {typed_read_end false ⊤ l β ty ot mc };
      {T v (sized_array ly (<[(Z.to_nat 0):=tyl]> tys) len) tyv }.
  Proof.
    liFromSyntax. iIntros "[%Hlen [%Hlength H2]]". subst.
    have Hlen2 : (0 < length tys)%nat by lia.
    iApply typed_read_end_mono_strong; [done|]. iIntros "H !>".
    rewrite !/(ty_own (sized_array _ _ _))/=. iDestruct "H" as "(%H1&%_&#Hbounds&Hl)".
    have [|ty Hlookup] := lookup_lt_is_Some_2 tys (Z.to_nat 0); [lia|].
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hasgn Hy]" => //.
    rewrite offset_loc_0. iDestruct ("H2" with "[//]") as "Hread".
    iFrame "Hasgn". iExists True%I. iSplit; [done|].
    iApply (typed_read_end_wand with "Hread").
    iIntros (v ty1 ty2) "Hupdate _ Hoffset Hv !>".
    iDestruct ("Hy" with "Hoffset") as "Hsep".
    rewrite !/(ty_own (sized_array _ _ _))/=.
    iFrame. rewrite !/(ty_own (sized_array _ _ _))/=.
    rewrite length_insert. do 2 iSplit => //. by iFrame.
  Qed.
  Definition type_read_sized_array_inst := [instance type_read_sized_array].
  Global Existing Instance type_read_sized_array_inst | 10.

End array.

Notation "sized_array< ty , tys , len >" := (sized_array ty tys len)
  (only printing, format "'sized_array<' ty ,  tys , len '>'") : printing_sugar.
Notation "array< ty , tys >" := (array ty tys)
  (only printing, format "'array<' ty ,  tys '>'") : printing_sugar.
Global Typeclasses Opaque array.
Global Typeclasses Opaque array_ptr.
Global Typeclasses Opaque sized_array.
