From lithium Require Import simpl_classes.
From caesium Require Export bitfield.
From refinedc.typing Require Export type.
From refinedc.typing Require Import programs boolean int.
From refinedc.typing Require Import type_options.

Section bitfield_raw.
  Context `{!typeG Σ}.

  Program Definition bitfield_raw_type (it : int_type) (bv : Z) : type := {|
    ty_has_op_type ot mt := is_int_ot ot it;
    ty_own β l := (l ◁ₗ{β} bv @ int it)%I;
    ty_own_val v := (v ◁ᵥ bv @ int it)%I
  |}%I.
  Next Obligation.
    intros. by iApply ty_share.
  Qed.
  Next Obligation.
    intros. iIntros "Hl". by iApply (ty_aligned with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_size_eq with "Hv").
  Qed.
  Next Obligation.
    intros. iIntros "Hl". by iApply (ty_deref with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hly Hl Hv". by iApply (ty_ref with "Hly Hl Hv").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_memcast_compat with "Hv").
  Qed.

  Definition bitfield_raw (it : int_type) : rtype _ :=
    RType (bitfield_raw_type it).

  Global Program Instance bitfield_raw_copyable bv it : Copyable (bv @ bitfield_raw it).
  Next Obligation. move => ???. unfold bitfield_raw; simpl_type. apply _. Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (copy_shr_acc with "Hl").
  Qed.

End bitfield_raw.
Notation "bitfield_raw< it >" := (bitfield_raw it) (only printing, format "'bitfield_raw<' it '>'") : printing_sugar.

Section bitfield.

  Class BitfieldDesc (R : Type) : Type := {
    bitfield_it : int_type;
    bitfield_repr : R → Z;
    bitfield_wf : R → Prop;
  }.

  Context `{!typeG Σ}.

  Program Definition bitfield_type (R : Type) `{BitfieldDesc R} (bv : R) : type := {|
    ty_has_op_type ot mt := is_int_ot ot bitfield_it;
    ty_own β l := (l ◁ₗ{β} bitfield_repr bv @ bitfield_raw bitfield_it)%I;
    ty_own_val v := (v ◁ᵥ bitfield_repr bv @ int bitfield_it)%I
  |}%I.
  Next Obligation.
    intros. by iApply ty_share.
  Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (ty_aligned with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_size_eq with "Hv").
  Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (ty_deref with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hly Hl Hv". by iApply (ty_ref with "Hly Hl Hv").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_memcast_compat with "Hv").
  Qed.

  Definition bitfield (R : Type) `{BitfieldDesc R} : rtype _ :=
    RType (bitfield_type R).

  Global Program Instance bitfield_copyable R `{BitfieldDesc R} bv : Copyable (bv @ bitfield R).
  Next Obligation. move => ????. unfold bitfield; simpl_type. apply _. Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (copy_shr_acc with "Hl").
  Qed.
End bitfield.
Notation "bitfield< R >" := (bitfield R) (only printing, format "'bitfield<' R '>'") : printing_sugar.

Global Typeclasses Opaque bitfield_raw_type bitfield_raw.
Global Typeclasses Opaque bitfield_type bitfield.

Section programs.
  Context `{!typeG Σ}.

  (* int ↔ bitfield_raw *)

  Lemma subsume_val_int_bitfield_raw A M it v n bv T :
    (∃ x, ⌜n = bv x⌝ ∗ T x) ⊢ subsume (v ◁ᵥ n @ int it) M (λ x : A, v ◁ᵥ (bv x) @ bitfield_raw it) T.
  Proof. iIntros "[% [-> ?]] ? !>". iExists _. by iFrame. Qed.
  Definition subsume_val_int_bitfield_raw_inst := [instance subsume_val_int_bitfield_raw].
  Global Existing Instance subsume_val_int_bitfield_raw_inst.

  Lemma subsume_val_bitfield_raw_int A M it v n bv T :
    (∃ x, ⌜bv = n x⌝ ∗ T x) ⊢ subsume (v ◁ᵥ bv @ bitfield_raw it) M (λ x : A, v ◁ᵥ (n x) @ int it) T.
  Proof. iIntros "[% [-> ?]] ? !>". iExists _. by iFrame. Qed.
  Definition subsume_val_bitfield_raw_int_inst := [instance subsume_val_bitfield_raw_int].
  Global Existing Instance subsume_val_bitfield_raw_int_inst.

  (* typing rules for bitfield_raw *)

  Lemma type_arithop_bitfield_raw bv1 bv2 op bv it v1 v2
    (Hop : int_arithop_result it bv1 bv2 op = Some bv) T:
    (⌜bv1 ∈ it⌝ -∗ ⌜bv2 ∈ it⌝ -∗ ⌜int_arithop_sidecond it bv1 bv2 bv op⌝ ∗
      (li_tactic (normalize_bitfield bv) (λ norm, T (i2v norm it) (norm @ bitfield_raw it))))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ bv1 @ bitfield_raw it) v2 (v2 ◁ᵥ bv2 @ bitfield_raw it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2". unfold li_tactic, normalize_bitfield.
    iApply type_val_expr_mono_strong.
    iApply (type_arithop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "[% ?]".
    iSplitR => //. iExists _. iFrame. unfold bitfield_raw; simpl_type.
    iIntros "$". by iExists tt.
  Qed.
  Definition type_and_bitfield_raw_inst bv1 bv2 :=
    [instance type_arithop_bitfield_raw bv1 bv2 AndOp (Z.land bv1 bv2)].
  Global Existing Instance type_and_bitfield_raw_inst.
  Definition type_or_bitfield_raw_inst bv1 bv2 :=
    [instance type_arithop_bitfield_raw bv1 bv2 OrOp (Z.lor bv1 bv2)].
  Global Existing Instance type_or_bitfield_raw_inst.
  Definition type_xor_bitfield_raw_inst bv1 bv2 :=
    [instance type_arithop_bitfield_raw bv1 bv2 XorOp (Z.lxor bv1 bv2)].
  Global Existing Instance type_xor_bitfield_raw_inst.
  Definition type_shl_bitfield_raw_inst bv1 bv2 :=
    [instance type_arithop_bitfield_raw bv1 bv2 ShlOp (bv1 ≪ bv2)].
  Global Existing Instance type_shl_bitfield_raw_inst.
  Definition type_shr_bitfield_raw_inst bv1 bv2 :=
    [instance type_arithop_bitfield_raw bv1 bv2 ShrOp (bv1 ≫ bv2)].
  Global Existing Instance type_shr_bitfield_raw_inst.

  Lemma type_not_bitfield_raw bv it v T:
    let bv' := if it_signed it then Z.lnot bv else Z_lunot (bits_per_int it) bv in
    (⌜bv ∈ it⌝ -∗ T (i2v bv' it) (bv' @ bitfield_raw it))
    ⊢ typed_un_op v (v ◁ᵥ bv @ bitfield_raw it)%I (NotIntOp) (IntOp it) T.
  Proof.
    iIntros (?) "HT Hv".
    iApply type_val_expr_mono_strong.
    iApply (type_not_int with "[HT] Hv") => //.
    iIntros "Hbv".
    iDestruct ("HT" with "Hbv") as "?".
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
    by iExists tt.
  Qed.
  Definition type_not_bitfield_raw_inst := [instance type_not_bitfield_raw].
  Global Existing Instance type_not_bitfield_raw_inst.

  Lemma type_relop_bitfield_raw bv1 bv2 op b it v1 v2
    (Hop : match op with
           | EqOp rit => Some (bool_decide (bv1 = bv2), rit)
           | NeOp rit => Some (bool_decide (bv1 ≠ bv2), rit)
           | LtOp rit => Some (bool_decide (bv1 < bv2), rit)
           | GtOp rit => Some (bool_decide (bv1 > bv2), rit)
           | LeOp rit => Some (bool_decide (bv1 <= bv2), rit)
           | GeOp rit => Some (bool_decide (bv1 >= bv2), rit)
           | _ => None
           end = Some (b, i32)) T :
    (⌜bv1 ∈ it⌝ -∗ ⌜bv2 ∈ it⌝ -∗ T (i2v (bool_to_Z b) i32) (b @ boolean i32))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ bv1 @ bitfield_raw it) v2 (v2 ◁ᵥ bv2 @ bitfield_raw it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2".
    iApply type_val_expr_mono_strong.
    iApply (type_relop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "?".
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
    by iExists tt.
  Qed.
  Definition type_eq_bitfield_raw_inst bv1 bv2 :=
    [instance type_relop_bitfield_raw bv1 bv2 (EqOp i32) (bool_decide (bv1 = bv2))].
  Global Existing Instance type_eq_bitfield_raw_inst.
  Definition type_ne_bitfield_raw_inst bv1 bv2 :=
    [instance type_relop_bitfield_raw bv1 bv2 (NeOp i32) (bool_decide (bv1 ≠ bv2))].
  Global Existing Instance type_ne_bitfield_raw_inst.

  (* bitfield_raw with int *)

  Lemma type_arithop_bitfield_raw_int bv n op bv' it v1 v2
    (Hop : int_arithop_result it bv n op = Some bv') T:
    (⌜bv ∈ it⌝ -∗ ⌜n ∈ it⌝ -∗ ⌜int_arithop_sidecond it bv n bv' op⌝ ∗
      (li_tactic (normalize_bitfield bv') (λ norm, T (i2v norm it) (norm @ bitfield_raw it))))
     ⊢ typed_bin_op v1 (v1 ◁ᵥ bv @ bitfield_raw it) v2 (v2 ◁ᵥ n @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2". unfold li_tactic, normalize_bitfield.
    iApply type_val_expr_mono_strong.
    iApply (type_arithop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "[% ?]".
    iSplitR => //.
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
    by iExists tt.
  Qed.
  Definition type_shl_bitfield_raw_int_inst bv n :=
    [instance type_arithop_bitfield_raw_int bv n ShlOp (bv ≪ n)].
  Global Existing Instance type_shl_bitfield_raw_int_inst.
  Definition type_shr_bitfield_raw_int_inst bv n :=
    [instance type_arithop_bitfield_raw_int bv n ShrOp (bv ≫ n)].
  Global Existing Instance type_shr_bitfield_raw_int_inst.

  Lemma type_arithop_int_bitfield_raw n bv op bv' it v1 v2
    (Hop : int_arithop_result it n bv op = Some bv') T:
    (⌜n ∈ it⌝ -∗ ⌜bv ∈ it⌝ -∗ ⌜int_arithop_sidecond it n bv bv' op⌝ ∗
      (li_tactic (normalize_bitfield bv') (λ norm, T (i2v norm it) (norm @ bitfield_raw it))))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ n @ int it) v2 (v2 ◁ᵥ bv @ bitfield_raw it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2". unfold li_tactic, normalize_bitfield.
    iApply type_val_expr_mono_strong.
    iApply (type_arithop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "[% ?]".
    iSplitR => //.
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
    by iExists tt.
  Qed.
  Definition type_and_int_bitfield_raw_inst n bv :=
    [instance type_arithop_int_bitfield_raw n bv AndOp (Z.land n bv)].
  Global Existing Instance type_and_int_bitfield_raw_inst.

  Lemma type_bitfield_raw_is_false it v1 v2 bv T :
    (∃ a b, ⌜bv = bf_cons a 1 (bool_to_Z b) bf_nil⌝ ∗ ⌜0 ≤ a⌝ ∗ T (i2v (bool_to_Z (negb b)) i32) ((bool_to_Z (negb b) @ int i32)))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ 0 @ int it) v2 (v2 ◁ᵥ bv @ bitfield_raw it) (EqOp i32) (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2".
    iDestruct "HT" as (a b Hbv ?) "HT".
    iApply type_val_expr_mono_strong.
    iApply (type_relop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "_ _".
    have -> : negb b = bool_decide (0 = bv).
    { rewrite (bool_decide_ext _ (bv = 0)) //.
      rewrite Hbv (bool_decide_ext _ (b = false)); last by apply bf_cons_bool_singleton_false_iff.
      by destruct b. }
    iExists _. iFrame. unfold boolean, int; simpl_type.
    iIntros "(%n&%&%Heq) !>". move: Heq => /= ?. subst n. done.
  Qed.
  Definition type_bitfield_raw_is_false_inst := [instance type_bitfield_raw_is_false].
  Global Existing Instance type_bitfield_raw_is_false_inst.

  Lemma type_bitfield_raw_is_true it v1 v2 bv T :
    (∃ a b, ⌜bv = bf_cons a 1 (bool_to_Z b) bf_nil⌝ ∗ ⌜0 ≤ a⌝ ∗ T (i2v (bool_to_Z b) i32) ((bool_to_Z b) @ int i32))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ 0 @ int it) v2 (v2 ◁ᵥ bv @ bitfield_raw it) (NeOp i32) (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2".
    iDestruct "HT" as (a b Hbv ?) "HT".
    iApply type_val_expr_mono_strong.
    iApply (type_relop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "_ _".
    have -> : b = bool_decide (0 ≠ bv).
    { rewrite (bool_decide_ext _ (bv ≠ 0)) //.
      rewrite Hbv (bool_decide_ext _ (b = true)); last by apply bf_cons_bool_singleton_true_iff.
      by destruct b. }
    iExists _. iFrame. unfold boolean, int; simpl_type.
    iIntros "(%n&%&%Heq) !>". move: Heq => /= ?. subst n. done.
  Qed.
  Definition type_bitfield_raw_is_true_inst := [instance type_bitfield_raw_is_true].
  Global Existing Instance type_bitfield_raw_is_true_inst.

  Lemma type_if_bitfield_raw it n v T1 T2:
    case_if (n ≠ 0)
      (li_trace (TraceIfInt n, true) T1)
      (li_trace (TraceIfInt n, false) T2)
    ⊢ typed_if (IntOp it) v (v ◁ᵥ n @ bitfield_raw it) T1 T2.
  Proof. unfold bitfield_raw; simpl_type. apply type_if_int. Qed.
  Definition type_if_bitfield_raw_inst := [instance type_if_bitfield_raw].
  Global Existing Instance type_if_bitfield_raw_inst.

  (* typing rules for bitfield: unfold to bitfield_raw *)

  Lemma simplify_hyp_place_bitfield l β R `{BitfieldDesc R} bv M T :
    (l ◁ₗ{β} bitfield_repr bv @ bitfield_raw bitfield_it -∗ ‖M‖ T)
    ⊢ simplify_hyp (l ◁ₗ{β} bv @ bitfield R) M T.
  Proof. done. Qed.
  Definition simplify_hyp_place_bitfield_inst := [instance simplify_hyp_place_bitfield with 0%N].
  Global Existing Instance simplify_hyp_place_bitfield_inst.

  Lemma simplify_goal_place_bitfield l β R `{BitfieldDesc R} bv M T :
    l ◁ₗ{β} bitfield_repr bv @ bitfield_raw bitfield_it ∗ T
    ⊢ simplify_goal M (l ◁ₗ{β} bv @ bitfield R) T.
  Proof. by iIntros "? !>". Qed.
  Definition simplify_goal_place_bitfield_inst := [instance simplify_goal_place_bitfield with 0%N].
  Global Existing Instance simplify_goal_place_bitfield_inst.

  Lemma simplify_hyp_val_bitfield v R `{BitfieldDesc R} bv M T :
    (v ◁ᵥ bitfield_repr bv @ bitfield_raw bitfield_it -∗ ‖M‖ T)
    ⊢ simplify_hyp (v ◁ᵥ bv @ bitfield R) M T.
  Proof. done. Qed.
  Definition simplify_hyp_val_bitfield_inst := [instance simplify_hyp_val_bitfield with 0%N].
  Global Existing Instance simplify_hyp_val_bitfield_inst.

  Lemma simplify_goal_val_bitfield v R `{BitfieldDesc R} bv M T :
    v ◁ᵥ bitfield_repr bv @ bitfield_raw bitfield_it ∗ T
    ⊢ simplify_goal M (v ◁ᵥ bv @ bitfield R) T.
  Proof. iIntros "? !>". done. Qed.
  Definition simplify_goal_val_bitfield_inst := [instance simplify_goal_val_bitfield with 0%N].
  Global Existing Instance simplify_goal_val_bitfield_inst.

End programs.
