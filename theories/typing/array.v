From iris.algebra Require Import list.
From refinedc.typing Require Export type.
From refinedc.typing Require Import programs singleton bytes int own.
Set Default Proof Using "Type".

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
    rewrite /has_layout_val heap_mapsto_app Hszv offset_loc_1 take_app_alt // drop_app_alt // app_length Hszv Hsz.
    iFrame. iPureIntro. rewrite /ly_size/= -/(ly_size _). lia.
  Qed.
  Next Obligation.
    move => ly tys ot mt l v [-> [? [? ]]]. iIntros (Hlys Hl) "Hl".
    iDestruct 1 as (Hv) "Htys". iSplit => //.
    iInduction (tys) as [|ty tys] "IH" forall (l v Hlys Hv Hl); csimpl in *.
    { rewrite Nat.mul_0_r right_id. by iApply heap_mapsto_loc_in_bounds_0. }
    move: Hlys. intros [? ?]%Forall_cons. iDestruct "Htys" as "[Hty Htys]".
    rewrite -{1}(take_drop (ly_size ly) v).
    rewrite offset_loc_0 heap_mapsto_app take_length_le ?Hv; last by repeat unfold ly_size => /=; lia.
    iDestruct "Hl" as "[Hl Hl']".
    iDestruct (heap_mapsto_loc_in_bounds with "Hl") as "#Hb1".
    iDestruct (ty_ref with "[] Hl Hty") as "$" => //.
    setoid_rewrite offset_loc_S. rewrite offset_loc_1.
    iDestruct ("IH" with "[//] [] [] Hl' Htys") as "[#Hb2 $]".
    { iPureIntro. rewrite /has_layout_val drop_length Hv. by repeat unfold ly_size => /=; lia. }
    { iPureIntro. by apply has_layout_loc_ly_mult_offset. }
    iApply loc_in_bounds_split_mul_S. rewrite take_length min_l; first by eauto.
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
    iDestruct "Ha" as "[$ Ha]"; first by iFrame.
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
    rewrite TCExists_Exists Exists_exists => -[x [/(elem_of_list_lookup_1 _ _) [i Hx] ?]].
    constructor. iIntros (l) "HP Hl".
    iDestruct (array_get_type with "Hl") as "[Hl _]"; [done|].
    iDestruct (alloc_alive_alive with "HP Hl") as "Hl".
    by iApply (alloc_alive_loc_mono with "Hl").
  Qed.

  Lemma subsume_array_alloc_alive l ly tys β T :
    (⌜0 < length tys⌝ ∗ (∀ ty, ⌜tys !! 0%nat = Some ty⌝ -∗ l ◁ₗ{β} ty -∗ alloc_alive_loc l ∗ T)) -∗
    subsume (l ◁ₗ{β} array ly tys) (alloc_alive_loc l) T.
  Proof.
    iIntros "[% HT]". destruct tys => //=. iIntros "(%&?&[Hty Htys])".
    rewrite offset_loc_0. iDestruct ("HT" with "[//] Hty") as "[$ $]".
  Qed.
  Global Instance subsume_array_alloc_alive_inst l ly tys β:
    Subsume (l ◁ₗ{β} array ly tys) (alloc_alive_loc l) | 10 :=
    λ T, i2p (subsume_array_alloc_alive l ly tys β T).
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
        rewrite /has_layout_loc /layout_wf /aligned_to. destruct l as [? a].
        move => /= [? ->] [? ->]. eexists. by rewrite -Z.mul_add_distr_r. }
      rewrite {2}/ty_own/=. iDestruct "Hty" as (v1 Hv1 Hl1 _) "Hv1".
      iExists (v1 ++ v2). rewrite heap_mapsto_own_state_app Hv1 /has_layout_val app_length Hv1 Hv2.
      iFrame. rewrite Forall_forall. iPureIntro. split_and! => //.
      rewrite {2 3}/ly_size/=. lia.
    - iDestruct 1 as (v Hv Hl _) "Hl". iSplit => //.
      iInduction n as [|n] "IH" forall (v l Hv Hl) => /=.
      { rewrite Nat.mul_0_r right_id.
        iApply loc_in_bounds_shorten; last by iApply heap_mapsto_own_state_loc_in_bounds. lia. }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      rewrite -(take_drop (ly.(ly_size)) v) heap_mapsto_own_state_app.
      iDestruct "Hl" as "[Hl Hr]". rewrite take_length_le ?Hv; last by repeat unfold ly_size => /=; lia.
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "#Hbl".
      iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hr") as "#Hbr".
      iDestruct ("IH" with "[] [] Hr") as "[Hb HH]".
      { iPureIntro. rewrite /has_layout_val drop_length Hv. repeat unfold ly_size => /=; lia. }
      { iPureIntro. by apply has_layout_loc_ly_mult_offset. }
      iSplitR.
      + iClear "IH". iApply loc_in_bounds_split_mul_S.
        rewrite take_length min_l; last first.
        { rewrite Hv. repeat unfold ly_size => /=; lia. }
        iFrame "Hbl". rewrite replicate_length drop_length Hv.
        destruct ly as [k?]. repeat unfold ly_size => /=.
        have ->: (k * n = k * S n - k)%nat by lia. done.
      + iSplitL "Hl"; last done. iExists _. iFrame. iPureIntro. rewrite Forall_forall. split_and! => //.
        rewrite /has_layout_val take_length_le ?Hv; repeat unfold ly_size => /=; lia.
  Qed.

  Lemma simplify_hyp_uninit_array ly l β T n:
    (⌜layout_wf ly⌝ ∗ (l ◁ₗ{β} array ly (replicate n (uninit ly)) -∗ T)) -∗
    simplify_hyp (l ◁ₗ{β} uninit (mk_array_layout ly n)) T.
  Proof. iIntros "[% HT] Hl". iApply "HT". rewrite array_replicate_uninit_equiv // {1}/ly_size/=. Qed.
  Global Instance simplify_hyp_uninit_array_inst ly l β n:
    SimplifyHypPlace l β (uninit (mk_array_layout ly n)) (Some 50%N) :=
    λ T, i2p (simplify_hyp_uninit_array ly l β T n).

  Lemma simplify_goal_uninit_array ly l β T n:
    (⌜layout_wf ly⌝ ∗ T (l ◁ₗ{β} array ly (replicate n (uninit ly)))) -∗
     simplify_goal (l ◁ₗ{β} uninit (mk_array_layout ly n)) T.
  Proof. iIntros "[% HT]". iExists _. iFrame. iIntros "?". rewrite array_replicate_uninit_equiv //. Qed.
  Global Instance simplify_goal_uninit_array_inst ly l β n:
    SimplifyGoalPlace l β (uninit (mk_array_layout ly n)) (Some 50%N) :=
    λ T, i2p (simplify_goal_uninit_array ly l β T n).

  Lemma subsume_uninit_array_replicate l β T n (ly1 : layout) ly2:
    ⌜layout_wf ly2⌝ ∗ ⌜ly1 = mk_array_layout ly2 n⌝ ∗ T -∗
    subsume (l ◁ₗ{β} uninit ly1) (l ◁ₗ{β} array ly2 (replicate n (uninit ly2))) T.
  Proof. iIntros "(%&->&$) ?". by rewrite array_replicate_uninit_equiv. Qed.
  Global Instance subsume_uninit_array_replicate_inst l β n ly1 ly2:
    SubsumePlace l β (uninit ly1) (array ly2 (replicate n (uninit ly2))) :=
    λ T, i2p (subsume_uninit_array_replicate l β T n ly1 ly2).

  Lemma subsume_array_replicate_uninit l β T n (ly1 : layout) ly2:
    ⌜layout_wf ly2⌝ ∗ ⌜ly1 = mk_array_layout ly2 n⌝ ∗ T -∗
    subsume (l ◁ₗ{β} array ly2 (replicate n (uninit ly2))) (l ◁ₗ{β} uninit ly1)  T.
  Proof. iIntros "(%&->&$) ?". by rewrite array_replicate_uninit_equiv. Qed.
  Global Instance subsume_array_replicate_uninit_inst l β n ly1 ly2:
    SubsumePlace l β (array ly2 (replicate n (uninit ly2))) (uninit ly1) :=
    λ T, i2p (subsume_array_replicate_uninit l β T n ly1 ly2).

  Lemma subsume_array ly1 ly2 tys1 tys2 l β T:
    ⌜ly1 = ly2⌝ ∗ subsume_list type [] tys1 tys2 (λ i ty, (l offset{ly1}ₗ i) ◁ₗ{β} ty) T -∗
      subsume (l ◁ₗ{β} array ly1 tys1) (l ◁ₗ{β} array ly2 tys2) T.
  Proof. iIntros "[-> H] ($&Hb&H1)". by iDestruct ("H" with "H1") as (->) "[$ $]". Qed.
  Global Instance subsume_array_inst ly1 ly2 tys1 tys2 l β:
    SubsumePlace l β (array ly1 tys1) (array ly2 tys2) | 100 :=
    λ T, i2p (subsume_array ly1 ly2 tys1 tys2 l β T).

  Lemma type_place_array l β T ly1 it v tyv tys ly2 K:
    (∃ i, ⌜ly1 = ly2⌝ ∗ subsume (v ◁ᵥ tyv) (v ◁ᵥ i @ int it) (⌜0 ≤ i⌝ ∗ ⌜i < length tys⌝ ∗
     ∀ ty, ⌜tys !! Z.to_nat i = Some ty⌝ -∗
    typed_place K (l offset{ly2}ₗ i) β ty (λ l2 β2 ty2 typ, T l2 β2 ty2 (λ t, array ly2 (<[Z.to_nat i := typ t]>tys))))) -∗
    typed_place (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array ly2 tys) T.
  Proof.
    iDestruct 1 as (i ->) "HP". iIntros (Φ) "(%&#Hb&Hl) HΦ" => /=. iIntros "Hv".
    unfold int; simpl_type.
    iDestruct ("HP" with "Hv") as (Hv) "HP".
    iDestruct "HP" as (? Hlen) "HP".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat i). 1: lia.
    iApply wp_ptr_offset => //; [by apply val_to_of_loc | | ].
    { iApply (loc_in_bounds_offset with "Hb"); simpl; [done| destruct l => /=; lia | destruct l => /=; nia]. }
    iIntros "!#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hl Hc]" => //. rewrite Z2Nat.id//.
    iApply ("HP" $! ty with "[//] Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]".
    iSplitR => //. iSplitR; first by rewrite insert_length. by iApply "Hc".
  Qed.
  Global Instance type_place_array_inst l β ly1 it v tyv tys ly2 K:
    TypedPlace (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array ly2 tys):=
    λ T, i2p (type_place_array l β T ly1 it v tyv tys ly2 K).

  Lemma type_bin_op_offset_array l β T ly it v tys i:
    (* TODO: Should we make layout_wf ly part of array such that we don't need to require it here? *)
    (⌜layout_wf ly⌝ ∗ ⌜0 ≤ i ≤ length tys⌝ ∗ (l ◁ₗ{β} array ly tys -∗ T (val_of_loc (l offset{ly}ₗ i)) ((l offset{ly}ₗ i) @ &own (array_ptr ly l i (length tys))))) -∗
    typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array ly tys) (PtrOffsetOp ly) (IntOp it) PtrOp T.
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
  Global Instance type_bin_op_offset_array_inst (l : loc) β ly it v tys i:
    TypedBinOp v (v ◁ᵥ i @ int it)%I l (l ◁ₗ{β} array ly tys) (PtrOffsetOp ly) (IntOp it) PtrOp :=
    λ T, i2p (type_bin_op_offset_array l β T ly it v tys i).

  Lemma type_bin_op_offset_array_ptr l β T ly it v i idx (len : nat) base:
    (⌜layout_wf ly⌝ ∗ ⌜0 ≤ idx + i ≤ len⌝ ∗ (l ◁ₗ{β} array_ptr ly base idx len -∗ T (val_of_loc (base offset{ly}ₗ (idx + i))) ((base offset{ly}ₗ (idx + i)) @ &own (array_ptr ly base (idx + i) len)))) -∗
     typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array_ptr ly base idx len) (PtrOffsetOp ly) (IntOp it) PtrOp T.
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
  Global Instance type_bin_op_offset_array_ptr_inst (l : loc) β ly it v i idx (len : nat) base:
    TypedBinOp v (v ◁ᵥ i @ int it)%I l (l ◁ₗ{β} array_ptr ly base idx len) (PtrOffsetOp ly) (IntOp it) PtrOp :=
    λ T, i2p (type_bin_op_offset_array_ptr l β T ly it v i idx len base).

  Lemma type_bin_op_neg_offset_array_ptr l β T ly it v i idx (len : nat) base:
    (⌜layout_wf ly⌝ ∗ ⌜0 ≤ idx - i ≤ len⌝ ∗ (l ◁ₗ{β} array_ptr ly base idx len -∗ T (val_of_loc (base offset{ly}ₗ (idx - i))) ((base offset{ly}ₗ (idx - i)) @ &own (array_ptr ly base (idx - i) len)))) -∗
     typed_bin_op v (v ◁ᵥ i @ int it) l (l ◁ₗ{β} array_ptr ly base idx len) (PtrNegOffsetOp ly) (IntOp it) PtrOp T.
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
  Global Instance type_bin_op_neg_offset_array_ptr_inst (l : loc) β ly it v i idx (len : nat) base:
    TypedBinOp v (v ◁ᵥ i @ int it)%I l (l ◁ₗ{β} array_ptr ly base idx len) (PtrNegOffsetOp ly) (IntOp it) PtrOp :=
    λ T, i2p (type_bin_op_neg_offset_array_ptr l β T ly it v i idx len base).

  Lemma type_bin_op_diff_array_ptr_array l1 β l2 T ly idx (len : nat) tys:
    (l1 ◁ₗ{β} array_ptr ly l2 idx len -∗
     l2 ◁ₗ{β} array ly tys -∗
     ⌜0 < ly.(ly_size)⌝ ∗
     ⌜0 < length tys⌝ ∗
     ⌜idx ≤ max_int ptrdiff_t⌝ ∗
     (alloc_alive_loc l2 ∗ True) ∧
     (T (i2v idx ptrdiff_t) (idx @ int ptrdiff_t))) -∗
     typed_bin_op l1 (l1 ◁ₗ{β} array_ptr ly l2 idx len) l2 (l2 ◁ₗ{β} array ly tys) (PtrDiffOp ly) PtrOp PtrOp T.
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
  Global Instance type_bin_op_diff_array_ptr_array_inst (l1 : loc) β l2 ly idx (len : nat) tys:
    TypedBinOp l1 (l1 ◁ₗ{β} array_ptr ly l2 idx len)%I l2 (l2 ◁ₗ{β} array ly tys) (PtrDiffOp ly) PtrOp PtrOp :=
    λ T, i2p (type_bin_op_diff_array_ptr_array l1 β l2 T ly idx len tys).


  Lemma subsume_array_ptr_alloc_alive β l ly base idx len T:
    alloc_alive_loc base ∗ T -∗
    subsume (l ◁ₗ{β} array_ptr ly base idx len) (alloc_alive_loc l) T.
  Proof. iIntros "[Halive $] (->&?)". by iApply (alloc_alive_loc_mono with "Halive"). Qed.
  Global Instance subsume_array_ptr_alloc_alive_inst β l ly base idx len :
    Subsume (l ◁ₗ{β} array_ptr ly base idx len) (alloc_alive_loc l) | 10 :=
    λ T, i2p (subsume_array_ptr_alloc_alive β l ly base idx len T).

  Lemma simpl_goal_array_ptr ly base idx1 idx2 len β T:
    T (⌜idx1 = idx2⌝ ∗ ⌜(base offset{ly}ₗ idx1) `has_layout_loc` ly⌝ ∗ ⌜0 ≤ idx1 ≤ Z.of_nat len⌝ ∗
                   loc_in_bounds base (ly_size (mk_array_layout ly len))) -∗
      simplify_goal ((base offset{ly}ₗ idx1) ◁ₗ{β} array_ptr ly base idx2 len)  T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros "(->&%&%&$)". Qed.
  Global Instance simpl_goal_array_ptr_inst ly base idx1 idx2 len β:
    SimplifyGoalPlace (base offset{ly}ₗ idx1) β (array_ptr ly base idx2 len) (Some 50%N) :=
    λ T, i2p (simpl_goal_array_ptr ly base idx1 idx2 len β T).

  Lemma subsume_array_ptr ly1 ly2 base1 base2 idx1 idx2 len1 len2 l β T:
    ⌜ly1 = ly2⌝ ∗ ⌜base1 = base2⌝ ∗ ⌜idx1 = idx2⌝ ∗ ⌜len1 = len2⌝ ∗ T -∗
      subsume (l ◁ₗ{β} array_ptr ly1 base1 idx1 len1) (l ◁ₗ{β} array_ptr ly2 base2 idx2 len2) T.
  Proof. by iIntros "(->&->&->&->&$) $". Qed.
  Global Instance subsume_array_ptr_inst ly1 ly2 base1 base2 idx1 idx2 len1 len2 l β:
    SubsumePlace l β (array_ptr ly1 base1 idx1 len1) (array_ptr ly2 base2 idx2 len2) :=
    λ T, i2p (subsume_array_ptr ly1 ly2 base1 base2 idx1 idx2 len1 len2 l β T).

  (*
  TODO: The following rule easily leads to diverging if the hypothesis is simplified before it is introduced into the context.
  Lemma simplify_array_ptr_hyp_learn_loc l β ly base idx len T:
    (⌜l = base offset{ly}ₗ idx⌝ -∗ l ◁ₗ{β} array_ptr ly base idx len -∗ T) -∗
    simplify_hyp (l ◁ₗ{β} array_ptr ly base idx len) T.
  Proof. iIntros "HT [% #Hlib]". iApply "HT" => //. by iSplit. Qed.
  Global Instance simplify_array_ptr_hyp_learn_loc_inst l β ly base idx len `{!TCUnless (TCFastDone (l = base offset{ly}ₗ idx))}:
    SimplifyHypPlace l β (array_ptr ly base idx len) (Some 0%N) | 10 :=
    λ T, i2p (simplify_array_ptr_hyp_learn_loc l β ly base idx len T).
*)

  Lemma simplify_hyp_array_ptr ly l β base idx len T:
    (⌜l = (base offset{ly}ₗ idx)⌝ -∗
      ⌜(base offset{ly}ₗ idx) `has_layout_loc` ly⌝ -∗
      loc_in_bounds base (ly_size (mk_array_layout ly len)) -∗
      ∃ tys, base ◁ₗ{β} array ly tys ∗ ⌜0 ≤ idx < length tys⌝ ∗ (
      ∀ ty, ⌜tys !! Z.to_nat idx = Some ty⌝ -∗ base ◁ₗ{β} array ly (<[Z.to_nat idx := place l]>tys) -∗
        l ◁ₗ{β} ty -∗ T)) -∗
    simplify_hyp (l ◁ₗ{β} array_ptr ly base idx len) T.
  Proof.
    iIntros "HT (->&%&%&?)".
    iDestruct ("HT" with "[//] [//] [$]") as (tys) "(Harray&%&HT)".
    have [|ty ?]:= lookup_lt_is_Some_2 tys (Z.to_nat idx). 1: lia.
    iDestruct (array_get_type (Z.to_nat idx) with "Harray") as "[Hty Harray]"; [done|].
    rewrite Z2Nat.id; [|lia].
    by iApply ("HT" with "[//] Harray Hty").
  Qed.
  Global Instance simplify_hyp_array_ptr_inst ly l β base idx len:
    SimplifyHypPlace l β (array_ptr ly base idx len) (Some 50%N) | 50 :=
    λ T, i2p (simplify_hyp_array_ptr ly l β base idx len T).
End array.

Notation "array< ty , tys >" := (array ty tys)
  (only printing, format "'array<' ty ,  tys '>'") : printing_sugar.
Global Typeclasses Opaque array.
Global Typeclasses Opaque array_ptr.
