From refinedc.typing Require Export type.
From refinedc.typing Require Import programs own intptr singleton int.
From refinedc.typing Require Import type_options.

Section tagged_ptr.
  Context `{!typeG Σ}.

  Program Definition tagged_ptr_type (β : own_state) (align : nat) (ty : type) (r : loc * Z) : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β' l :=
      ⌜l `has_layout_loc` void*⌝ ∗
      ⌜r.1 `aligned_to` align⌝ ∗
      ⌜0 ≤ r.2 < align⌝ ∗
      l ↦[β'] (r.1 +ₗ r.2) ∗
      loc_in_bounds r.1 align ∗
      r.1 ◁ₗ{own_state_min β' β} ty;
      ty_own_val v :=
        ⌜v = val_of_loc (r.1 +ₗ r.2)⌝ ∗
        ⌜r.1 `aligned_to` align⌝ ∗
        ⌜0 ≤ r.2 < align⌝ ∗
        loc_in_bounds r.1 align ∗
        r.1 ◁ₗ{β} ty;
  |}%I.
  Next Obligation.
    iIntros (β ??????) "($&$&$&Hl&$&H)". rewrite left_id.
    iMod (heap_mapsto_own_state_share with "Hl") as "$".
    destruct β => //=. by iApply ty_share.
  Qed.
  Next Obligation. iIntros (???????->%is_ptr_ot_layout) "($&_)". Qed.
  Next Obligation. iIntros (???????->%is_ptr_ot_layout) "(->&_)". done. Qed.
  Next Obligation. iIntros (????????) "(%&%&%&?&?)". rewrite left_id. eauto with iFrame. Qed.
  Next Obligation. iIntros (????????->%is_ptr_ot_layout?) "? (->&%&%&?)". by iFrame. Qed.
  Next Obligation.
    iIntros (β align ty l v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[-> ?]". iPureIntro. naive_solver.
  Qed.

  Global Instance tagged_ptr_type_le : Proper ((=) ==> (=) ==> (⊑) ==> (=) ==> (⊑)) tagged_ptr_type.
  Proof. solve_type_proper. Qed.
  Global Instance tagged_ptr_type_proper : Proper ((=) ==> (=) ==> (≡) ==> (=) ==> (≡)) tagged_ptr_type.
  Proof. solve_type_proper. Qed.

  Definition tagged_ptr (β : own_state) (align : nat) (ty : type) : rtype _ :=
    RType (tagged_ptr_type β align ty).

  Global Instance tagged_ptr_loc_in_bounds r ty align β1 β2 :
    LocInBounds (r @ tagged_ptr β1 align ty) β2 bytes_per_addr.
  Proof.
    constructor. iIntros (?) "(_&_&_&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed.

  Global Instance tagged_ptr_related_to_frac_ptr A v r β n ty:
     RelatedTo (λ x : A, v ◁ᵥ r @ tagged_ptr (β x) (n x) (ty x))%I | 1 :=
     {| rt_fic := FindValOrLoc v r.1 |}.

  Lemma subsume_tagged_ptr A M v r1 r2 n1 n2 β1 β2 ty1 ty2 T:
    (r1.1 ◁ₗ{β1} ty1 -∗ ‖M‖ ∃ x, ⌜r1 = r2 x⌝ ∗ ⌜n1 = n2 x⌝ ∗ ⌜β1 = β2 x⌝ ∗ (r2 x).1 ◁ₗ{β2 x} ty2 x ∗ T x)
    ⊢ subsume (v ◁ᵥ r1 @ tagged_ptr β1 n1 ty1) M (λ x : A, v ◁ᵥ (r2 x) @ tagged_ptr (β2 x) (n2 x) (ty2 x)) T.
  Proof.
    iIntros "HT (?&?&?&?&?)".
    iDestruct ("HT" with "[$]") as ">(%&->&->&->&?&HT)".
    iModIntro. iExists _. iFrame.
  Qed.
  Definition subsume_tagged_ptr_inst := [instance subsume_tagged_ptr].
  Global Existing Instance subsume_tagged_ptr_inst.

  Lemma subsume_frac_ptr_tagged_ptr A M l β (v : val) r n ty1 ty2 m `{!LearnAlignment β ty1 m} T:
    (l ◁ₗ{β} ty1 -∗ ⌜if m is Some m' then l `aligned_to` m' else True⌝ -∗
      ‖M‖ ∃ x, ⌜l = (r x).1⌝ ∗ ⌜v = (r x).1 +ₗ (r x).2⌝ ∗ ⌜l `aligned_to` (n x)⌝ ∗ ⌜0 ≤ (r x).2 < (n x)⌝ ∗
       loc_in_bounds l (n x) ∗ l ◁ₗ{β} (ty2 x) ∗ T x)
    ⊢ subsume (l ◁ₗ{β} ty1) M (λ x : A, v ◁ᵥ (r x) @ tagged_ptr β (n x) (ty2 x)) T.
  Proof.
    iIntros "HT Hl".
    iDestruct (learnalign_learn with "Hl") as %?.
    iDestruct ("HT" with "Hl [//]") as ">(%&->&->&%&%&?&?&HT)".
    iModIntro. iExists _. by iFrame.
  Qed.
  Definition subsume_frac_ptr_tagged_ptr_inst := [instance subsume_frac_ptr_tagged_ptr].
  Global Existing Instance subsume_frac_ptr_tagged_ptr_inst.

  Lemma simplify_hyp_tagged_ptr_0 v r β n ty `{!CanSolve (r.2 = 0)} M T:
    (v ◁ᵥ r.1 @ frac_ptr β ty -∗ ‖M‖ T)
    ⊢ simplify_hyp (v ◁ᵥ r @ tagged_ptr β n ty) M T.
  Proof.
    unfold CanSolve in *. destruct r as [l ?]. simpl in *. simplify_eq.
    iIntros "HT (->&%&%&?&?)". iApply "HT". rewrite /= shift_loc_0. unfold frac_ptr; simpl_type. by iFrame.
  Qed.
  Definition simplify_hyp_tagged_ptr_0_inst := [instance simplify_hyp_tagged_ptr_0 with 0%N].
  Global Existing Instance simplify_hyp_tagged_ptr_0_inst.

  Lemma type_cast_tagged_ptr_intptr_val (v : val) (r : loc * Z) β (align : nat) it ty T:
    (⌜v = r.1 +ₗ r.2⌝ -∗
     ⌜aligned_to r.1 align⌝ -∗
     ⌜0 ≤ r.2 < align⌝ -∗
     ⌜min_alloc_start ≤ r.1.2 ∧ r.1.2 + align ≤ max_alloc_end⌝ -∗
     loc_in_bounds r.1 align -∗
     r.1 ◁ₗ{β} ty -∗
     v ◁ᵥ r @ tagged_ptr β align (place r.1) -∗
     ⌜(r.1.2 + r.2)%Z ∈ it⌝ ∗
     ((alloc_alive_loc r.1 ∗ True) ∧
     ∀ v, T v ((r.1 +ₗ r.2) @ intptr it)))
    ⊢ typed_un_op v (v ◁ᵥ r @ tagged_ptr β align ty) (CastOp (IntOp it)) PtrOp T.
  Proof.
    iIntros "HT (->&%&%&#Hlib&Hp)" (Φ) "HΦ".
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %Hrange.
    iDestruct (loc_in_bounds_has_alloc_id with "Hlib") as %[aid ?].
    iDestruct ("HT" with "[//] [//] [//] [//] [$] [$] []") as ([??]%(val_of_Z_is_Some (Some aid))) "HT".
    { iFrame "Hlib". unfold place; done. }
    iApply wp_cast_ptr_int; [by apply val_to_of_loc|done|done|].
    iSplit.
    { iDestruct "HT" as "[[HT _] _]". by iApply (alloc_alive_loc_mono with "HT"). }
    iDestruct "HT" as "[_ HT]". iApply ("HΦ" with "[] HT").
    iExists _. repeat iSplit; try iPureIntro.
    - done.
    - by apply: val_to_of_Z.
    - by apply: val_of_Z_to_prov.
    - iApply (loc_in_bounds_offset with "Hlib") => /=; [done | |]; unfold addr in *; lia.
  Qed.
  Definition type_cast_tagged_ptr_intptr_val_inst := [instance type_cast_tagged_ptr_intptr_val].
  Global Existing Instance type_cast_tagged_ptr_intptr_val_inst.

  Lemma type_copy_aid_tagged_ptr v1 a it v2 r β align ty T:
    (v1 ◁ᵥ a @ int it -∗
     v2 ◁ᵥ r @ tagged_ptr β align ty -∗
     ⌜r.1.2 ≤ a ≤ r.1.2 + align⌝ ∗
     (alloc_alive_loc r.1 ∗ True) ∧
     T (val_of_loc (r.1.1, a)) (value PtrOp (val_of_loc (r.1.1, a))))
    ⊢ typed_copy_alloc_id v1 (v1 ◁ᵥ a @ int it) v2 (v2 ◁ᵥ r @ tagged_ptr β align ty) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT %Hv1 (->&%&%&#Hlib&Hp)" (Φ) "HΦ".
    iDestruct ("HT" with "[//] [$Hlib $Hp]") as ([??]) "HT"; [done|].
    rewrite !right_id.
    iApply wp_copy_alloc_id; [ done | by rewrite val_to_of_loc |  | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done | done | etrans; [|done]; lia]. }
    iSplit.
    - iDestruct "HT" as "[Halloc _]". by iApply (alloc_alive_loc_mono with "Halloc").
    - iDestruct "HT" as "[_ HT]". iApply ("HΦ" with "[] HT").
      unfold value; simpl_type. iSplit => //. iPureIntro. apply: mem_cast_id_loc.
  Qed.
  Definition type_copy_aid_tagged_ptr_inst := [instance type_copy_aid_tagged_ptr].
  Global Existing Instance type_copy_aid_tagged_ptr_inst.
End tagged_ptr.
Global Typeclasses Opaque tagged_ptr_type tagged_ptr.

Notation "&tagged< align , ty >" :=
  (tagged_ptr Own align ty)
  (only printing, format "'&tagged<' align , ty '>'") : printing_sugar.
Notation "tagged_ptr< β , align , ty >" :=
  (tagged_ptr β align ty)
  (only printing, format "'tagged_ptr<' β , align , ty '>'") : printing_sugar.

Notation "&tagged" := (tagged_ptr Own) (format "&tagged") : bi_scope.
