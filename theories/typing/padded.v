From refinedc.typing Require Export type.
From refinedc.typing Require Import programs bytes int own struct.
From refinedc.typing Require Import type_options.

Section padded.
  Context `{!typeG Σ}.

  Program Definition padded (ty : type) (lyty ly : layout) : type := {|
    ty_has_op_type ot mt := ot = UntypedOp ly ∧ ty.(ty_has_op_type) (UntypedOp lyty) MCNone ;
    ty_own β l :=
      (⌜lyty ⊑ ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l ly.(ly_size) ∗
      l ◁ₗ{β} ty ∗ (l +ₗ lyty.(ly_size)) ◁ₗ{β} uninit (ly_offset ly lyty.(ly_size)))%I;
    ty_own_val v := (∃ v1 v2, ⌜lyty ⊑ ly⌝ ∗ ⌜v = v1 ++ v2⌝ ∗ v1 ◁ᵥ ty ∗ v2 ◁ᵥ uninit (ly_offset ly lyty.(ly_size)))%I;
  |}.
  Next Obligation.
    iDestruct 1 as "[$ [$ [$ [HT Hl]]]]".
    iMod (ty_share with "HT") as "$" => //.
    by iApply ty_share.
  Qed.
  Next Obligation. iIntros (?????? [-> ?]) "[_ [$ _]]". Qed.
  Next Obligation.
    iIntros (ty lyty ly ot mt v [-> ?]). iDestruct 1 as (v1 v2 [??] ->) "[Hv1 Hv2]".
    iDestruct (ty_size_eq with "Hv1") as %Heq1; [done|].
    iDestruct (ty_size_eq _ (UntypedOp _) MCNone with "Hv2") as %Heq2; [done|].
    iPureIntro. rewrite /has_layout_val length_app Heq1 Heq2 {2}/ly_size/=. lia.
  Qed.
  Next Obligation.
    iIntros (ty lyty ly ot mt l [-> ?]). iDestruct 1 as ([??] ?) "[_ [Hl Hpad]]".
    iDestruct (ty_deref with "Hl") as (v1) "[Hmt1 Hv1]"; [done|].
    iDestruct (ty_size_eq with "Hv1") as %Heq1; [done|].
    iDestruct (ty_deref _ (UntypedOp _) MCNone with "Hpad") as (v2) "[Hmt2 Hv2]"; [done|].
    iExists (v1 ++ v2). rewrite heap_mapsto_app Heq1. by iFrame.
  Qed.
  Next Obligation.
    iIntros (ty lyty ly ot mt l v [-> ?] Hly) "Hmt". iDestruct 1 as (v1 v2 [??] ->) "[Hv1 Hv2]".
    iDestruct (ty_size_eq with "Hv1") as %Heq1; [done|].
    iDestruct (ty_size_eq _ (UntypedOp _) MCNone with "Hv2") as %Heq2; [done|].
    iDestruct (heap_mapsto_loc_in_bounds with "Hmt") as "#Hb".
    rewrite heap_mapsto_app Heq1.
    iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iDestruct (ty_ref with "[%] Hmt1 Hv1") as "$"; [done| by apply: has_layout_loc_trans|].
    iDestruct (ty_ref _ (UntypedOp _) MCNone with "[%] Hmt2 Hv2") as "$" => //. { by apply: has_layout_ly_offset. }
    iSplit => //. iSplit => //. iApply loc_in_bounds_shorten; last done.
    rewrite length_app Heq1 Heq2 /ly_size /= -!/(ly_size _). lia.
  Qed.
  Next Obligation. iIntros (ty lyty ly v ot mt st ?). apply mem_cast_compat_Untyped. destruct ot; naive_solver. Qed.

  Global Instance padded_le : Proper ((⊑) ==> (=) ==> (=) ==> (⊑)) padded.
  Proof. solve_type_proper. Qed.
  Global Instance padded_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) padded.
  Proof. solve_type_proper. Qed.

  Global Instance loc_in_bounds_padded ty lyty ly β: LocInBounds (padded ty lyty ly) β (ly_size ly).
  Proof.
    constructor. by iIntros (l) "(_&_&H&_)".
  Qed.

  Global Program Instance learn_align_padded β ty ly lyty
    : LearnAlignment β (padded ty lyty ly) (Some (ly_align ly)).
  Next Obligation. by iIntros (β ty ly lyty l) "(_&%&_)". Qed.

  Lemma simpl_padded_hyp_eq_layout l β ty ly1 ly2 `{!TCFastDone (ly1.(ly_size) = ly2.(ly_size))} T:
    (l ◁ₗ{β} ty -∗ T)
    ⊢ simplify_hyp (l ◁ₗ{β} padded ty ly1 ly2) T.
  Proof. iIntros "HT (?&?&?&?&?)". by iApply "HT". Qed.
  Definition simpl_padded_hyp_eq_layout_inst := [instance simpl_padded_hyp_eq_layout with 0%N].
  Global Existing Instance simpl_padded_hyp_eq_layout_inst.
  (* TODO: should this also work for Shr? *)
  Lemma simpl_padded_goal_eq_layout l ty ly T:
    ⌜ty.(ty_has_op_type) (UntypedOp ly) MCNone⌝ ∗ l ◁ₗ ty ∗ T
    ⊢ simplify_goal (l ◁ₗ padded ty ly ly) T.
  Proof.
    iIntros "[% [Hl $]]". iDestruct (ty_aligned with "Hl") as %?; [done|].
    do 2 iSplit => //. iDestruct (movable_loc_in_bounds with "Hl") as "#Hb"; [done|]. iFrame "Hl Hb".
    iExists []. rewrite heap_mapsto_own_state_nil.
    iSplit. { iPureIntro. rewrite /has_layout_val/ly_offset/ly_size /=. lia. }
    iSplit. { iPureIntro. by apply: has_layout_ly_offset. }
    rewrite -{1}(Nat.add_0_r (ly_size _)) -loc_in_bounds_split.
    by iDestruct "Hb" as "[_$]".
  Qed.
  Definition simpl_padded_goal_eq_layout_inst := [instance simpl_padded_goal_eq_layout with 0%N].
  Global Existing Instance simpl_padded_goal_eq_layout_inst.

  (* we deliberately introduce a fresh location l because otherwise l
  and l' could get confused and we might have two l ◁ₗ ... for the
  same l in the context. (one with padded (l @ place) ...
  and one with the type in the padded *)
  Lemma type_place_padded K l β1 ty lyty ly T:
    (∀ l', typed_place K l' β1 ty (λ l2 ty2 β typ, T l2 ty2 β (λ t, padded (typ t) lyty ly)))
    ⊢ typed_place K l β1 (padded ty lyty ly) T.
  Proof.
    iIntros "HP" (Φ) "(% & % & Hb & Hl & Hpad) HΦ" => /=.
    iApply ("HP" with "Hl"). iIntros (l2 β2 ty2 typ R) "Hl2 Hc".
    iApply ("HΦ" with "Hl2"). iIntros (ty') "Hl2".
    iMod ("Hc" with "Hl2") as "[$ $]". by iFrame.
  Qed.
  (* This should have a lower priority than type_place_id *)
  Definition type_place_padded_inst := [instance type_place_padded].
  Global Existing Instance type_place_padded_inst | 50.

  (* Only works for Own since ty might have interior mutability, but
  uninit ty assumes that the values are frozen *)
  Lemma subsume_padded_uninit A l ly1 ly2 lyty ty T:
    (⌜ty.(ty_has_op_type) (UntypedOp lyty) MCNone⌝ ∗ ∀ v, v ◁ᵥ ty -∗
     subsume (l ◁ₗ uninit ly1) (λ x, l ◁ₗ uninit (ly2 x)) T)
    ⊢ subsume (l ◁ₗ padded ty lyty ly1) (λ x : A, l ◁ₗ uninit (ly2 x)) T.
  Proof.
    iIntros "[% HT]". iDestruct 1 as ([? ?] ?) "(Hb & Hl & Hr)".
    iDestruct (ty_deref with "Hl") as (v1) "[Hl Hv1]"; [done|].
    iDestruct (ty_size_eq with "Hv1") as %Hlen1; [done|].
    iDestruct (ty_deref _ (UntypedOp _) MCNone with "Hr") as (v2) "[Hr Hv2]"; [done|].
    iDestruct (ty_size_eq _ (UntypedOp _) MCNone with "Hv2") as %Hlen2; [done|].
    iApply ("HT" with "Hv1"). iExists (v1 ++ v2).
    rewrite /= heap_mapsto_own_state_app /has_layout_val length_app Forall_forall Hlen1 Hlen2.
    iFrame. iPureIntro; split_and! => //.
    rewrite /= /ly_offset {2}/ly_size. lia.
  Qed.
  Definition subsume_padded_uninit_inst := [instance subsume_padded_uninit].
  Global Existing Instance subsume_padded_uninit_inst.

  Lemma subsume_uninit_padded A l β ly lyty T:
    (∃ x, ⌜lyty x ⊑ ly⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} uninit ly) (λ x : A, l ◁ₗ{β} padded (uninit (lyty x)) (lyty x) ly) T.
  Proof.
    iDestruct 1 as (? [? ?]) "?". iIntros "Hl". iExists _. iFrame.
    iDestruct (bytewise_loc_in_bounds with "Hl") as "#$".
    iDestruct (split_bytewise with "Hl") as "[Hl $]" => //.
    rewrite /ty_own/=. iDestruct "Hl" as (????) "Hl".
    iSplit; first done. iSplit; first done. iExists _; iFrame.
    iSplit; first done. iSplit; last by rewrite Forall_forall.
    iPureIntro. by apply: has_layout_loc_trans.
  Qed.
  Definition subsume_uninit_padded_inst := [instance subsume_uninit_padded].
  Global Existing Instance subsume_uninit_padded_inst.

  Lemma type_place_padded_uninit_struct K l β sl n ly T:
    ⌜(layout_of sl) ⊑ ly⌝ ∗
      typed_place (GetMemberPCtx sl n :: K) l β (padded (struct sl (uninit <$> omap (λ '(n, ly), const ly <$> n) sl.(sl_members))) sl ly) T
    ⊢ typed_place (GetMemberPCtx sl n :: K) l β (uninit ly) T.
  Proof.
    iIntros "[% HT]" (Φ) "Hl".
    iDestruct (apply_subsume_place_true with "Hl []") as "Hl".
    { iApply (subsume_uninit_padded _ _ _ _ (λ _, sl)). by iExists tt. }
    iApply "HT". iDestruct "Hl" as "[$ [$ [$ [Hl $]]]]". by rewrite uninit_struct_equiv.
  Qed.
  Definition type_place_padded_uninit_struct_inst := [instance type_place_padded_uninit_struct].
  Global Existing Instance type_place_padded_uninit_struct_inst.

  Lemma padded_focus l β ty1 ly lyty:
    (l ◁ₗ{β} padded ty1 lyty ly) -∗
    (l ◁ₗ{β} ty1 ∗ (∀ ty2, l ◁ₗ{β} ty2 -∗ l ◁ₗ{β} padded ty2 lyty ly)).
  Proof. iIntros "(?&?&?&?&?)". iFrame. iIntros (?) "$". Qed.

  (* If lyty is the same, then ly also must be the same. *)
  Lemma padded_mono A l β ty1 ty2 ly1 ly2 lyty T:
    (l ◁ₗ{β} ty1 -∗ ∃ x, ⌜ly1 = ly2 x⌝ ∗ l ◁ₗ{β} (ty2 x) ∗ T x)
    ⊢ subsume (l ◁ₗ{β} padded ty1 lyty ly1) (λ x : A, l ◁ₗ{β} padded (ty2 x) lyty (ly2 x)) T.
  Proof.
    iIntros "HT Hl".
    iDestruct (padded_focus with "Hl") as "[Hl Hpad]".
    iDestruct ("HT" with "[$]") as (? ->) "[? HT]".
    iExists _. iFrame "HT". by iApply "Hpad".
  Qed.
  Definition padded_mono_inst := [instance padded_mono].
  Global Existing Instance padded_mono_inst.

  Lemma split_padded n l β ly1 lyty ty:
    (n ≤ ly1.(ly_size))%nat →
    (lyty.(ly_size) ≤ n)%nat →
    l ◁ₗ{β} padded ty lyty ly1 -∗
      l ◁ₗ{β} padded ty lyty (ly_set_size ly1 n) ∗ (l +ₗ n) ◁ₗ{β} (uninit (ly_offset ly1 n)).
  Proof.
    iIntros (? ?). iDestruct 1 as ([??]?) "(#Hb&$&Hl)".
    (* iDestruct (split_uninit with "Hl") as "[? ?]". *)
    rewrite {1}/ty_own/=. iDestruct "Hl" as (v Hv Hl _) "Hmt".
    rewrite -[v](take_drop (n - lyty.(ly_size))%nat) heap_mapsto_own_state_app.
    iDestruct "Hmt" as "[Hmt1 Hmt2]". iSplitL "Hmt1".
    - iSplit => //. iSplit; first by iPureIntro; apply: has_layout_loc_trans.
      iSplit. { iApply loc_in_bounds_shorten; last done. rewrite /ly_size /= -/(ly_size _). lia. }
      iExists _. iFrame. iPureIntro. rewrite Forall_forall. split_and! => //.
      rewrite /has_layout_val length_take_le // Hv. rewrite {2}/ly_size/=. lia.
    - rewrite shift_loc_assoc length_take_le. 2: rewrite Hv {2}/ly_size/=; lia.
      have ->: (ly_size lyty + (n - ly_size lyty)%nat) = n by lia.
      iExists _. iFrame. iPureIntro. rewrite Forall_forall.
      split_and! => //; last by apply has_layout_ly_offset.
      rewrite /has_layout_val length_drop Hv {1 4}/ly_size/=. lia.
  Qed.


  Lemma type_add_padded v2 β ly lyty ty (p : loc) (n : Z) it T:
    (⌜n ∈ it⌝ -∗ ⌜0 ≤ n⌝ ∗ ⌜Z.to_nat n ≤ ly.(ly_size)⌝%nat ∗ ⌜lyty.(ly_size) ≤ Z.to_nat n⌝%nat ∗ (p ◁ₗ{β} padded ty lyty (ly_set_size ly (Z.to_nat n)) -∗ v2 ◁ᵥ n @ int it -∗
          T (val_of_loc (p +ₗ n)) ((p +ₗ n) @ &frac{β} (uninit (ly_offset ly (Z.to_nat n))))))
    ⊢ typed_bin_op v2 (v2 ◁ᵥ n @ int it) p (p ◁ₗ{β} padded ty lyty ly) (PtrOffsetOp u8) (IntOp it) PtrOp T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT" (Hint) "Hp". iIntros (Φ) "HΦ".
    move: (Hint) => /val_to_Z_in_range?.
    iDestruct ("HT" with "[//]") as (???) "HT".
    iDestruct (split_padded (Z.to_nat n) with "Hp") as "[H1 H2]"; [lia..|].
    rewrite -!(offset_loc_sz1 u8)// Z2Nat.id; [|lia].
    iDestruct (loc_in_bounds_in_bounds with "H2") as "#?".
    iApply wp_ptr_offset; [ by apply val_to_of_loc | done | |].
    { iApply loc_in_bounds_shorten; [|done]; lia. }
    iModIntro. iApply ("HΦ" with "[H2]"). 2: iApply ("HT" with "H1 []").
    - unfold frac_ptr; simpl_type. by iFrame.
    - by iPureIntro.
  Qed.
  Definition type_add_padded_inst := [instance type_add_padded].
  Global Existing Instance type_add_padded_inst.


  Lemma annot_to_uninit_padded l ty ly lyty T:
    (⌜ty.(ty_has_op_type) (UntypedOp lyty) MCNone⌝ ∗ (l ◁ₗ uninit ly -∗ T))
    ⊢ typed_annot_stmt ToUninit l (l ◁ₗ padded ty lyty ly) T.
  Proof.
    iIntros "[% HT] Hl". iApply step_fupd_intro => //. iModIntro.
    iDestruct (ty_aligned _ _ MCNone with "Hl") as %?; [done|].
    iDestruct (ty_deref _ _ MCNone with "Hl") as (v) "[Hmt Hv]"; [done|].
    iDestruct (ty_size_eq _ _ MCNone with "Hv") as %?; [done|].
    iApply ("HT").
    iExists v. rewrite Forall_forall. by iFrame.
  Qed.
  Definition annot_to_uninit_padded_inst := [instance annot_to_uninit_padded].
  Global Existing Instance annot_to_uninit_padded_inst.

End padded.
Notation "padded< ty , lyty , ly >" := (padded ty lyty ly)
  (only printing, format "'padded<' ty ,  lyty ,  ly '>'") : printing_sugar.

Global Typeclasses Opaque padded.
