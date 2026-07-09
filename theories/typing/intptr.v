From refinedc.typing Require Export type.
From refinedc.typing Require Import programs own singleton int.
From refinedc.typing Require Import type_options.

Section intptr.
  Context `{!typeG Σ}.

  Program Definition intptr_type (it : int_type) (p : loc) : type := {|
    ty_has_op_type ot mt := is_int_ot ot it;
    ty_own β l := ∃ v aid, ⌜p.1 = ProvAlloc (Some aid)⌝ ∗ ⌜val_to_Z v it = Some p.2⌝ ∗
                      ⌜val_to_byte_prov v = Some aid⌝ ∗ ⌜l `has_layout_loc` it⌝ ∗
                      loc_in_bounds p 0 ∗ l ↦[β] v;
      ty_own_val v := ∃ aid, ⌜p.1 = ProvAlloc (Some aid)⌝ ∗ ⌜val_to_Z v it = Some p.2⌝ ∗
                      ⌜val_to_byte_prov v = Some aid⌝ ∗ loc_in_bounds p 0;
  |}%I.
  Next Obligation.
    iIntros (it p l ??) "(%v&%aid&%Haid&%Hv&%&%Hl&#?&H)". iExists v, aid.
    do 5 (iSplitR; first done). by iApply heap_mapsto_own_state_share.
  Qed.
  Next Obligation. iIntros (?????->%is_int_ot_layout) "(%aid&%&%&%&%&$&_)". Qed.
  Next Obligation. iIntros (?????->%is_int_ot_layout) "(%aid&%&%&?) !%". by apply: val_to_Z_length. Qed.
  Next Obligation. iIntros (??????) "(%v&%&%&%&%&%&Hl&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (??????->%is_int_ot_layout?) "Hl (%&%&%&%&?)". iExists _, _. eauto with iFrame. Qed.
  Next Obligation.
    iIntros (???????). apply: mem_cast_compat_int; [naive_solver|].
    iIntros "(%&%&%&%&?)". iPureIntro. naive_solver.
  Qed.

  Definition intptr (it : int_type) : rtype _ := RType (intptr_type it).

  Lemma intptr_loc_in_bounds l β p it:
     l ◁ₗ{β} p @ intptr it -∗ loc_in_bounds l (bytes_per_int it).
  Proof.
    iIntros "(%&%&%&%Hv&%&%&?&Hl)". move: Hv => /val_to_Z_length <-.
    by iApply heap_mapsto_own_state_loc_in_bounds.
  Qed.

  Global Instance loc_in_bounds_intptr p it β: LocInBounds (p @ intptr it) β (bytes_per_int it).
  Proof.
    constructor. iIntros (l) "Hl".
    iDestruct (intptr_loc_in_bounds with "Hl") as "Hlib".
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.

  Lemma ty_own_intptr_in_range l β p it : l ◁ₗ{β} p @ intptr it -∗ ⌜p.2 ∈ it⌝.
  Proof.
    iIntros "Hl". destruct β.
    - iDestruct (ty_deref _ (IntOp _ ) MCNone with "Hl") as (?) "[_ (%&%&%&%&?)]"; [done|].
      iPureIntro. by eapply val_to_Z_in_range.
    - iDestruct "Hl" as (?????) "_".
      iPureIntro. by eapply val_to_Z_in_range.
  Qed.

  (* TODO: make a simple type as in lambda rust such that we do not
  have to reprove this everytime? *)
  Global Program Instance intptr_copyable p it : Copyable (p @ intptr it).
  Next Obligation.
    iIntros (??????->%is_int_ot_layout) "(%v&%aid&%Hv&%Hl&%&%&#?&Hl)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    iSplitR => //. iExists q, v. iFrame "∗#". iModIntro. eauto with iFrame.
  Qed.

  Global Instance intptr_timeless l p it:
    Timeless (l ◁ₗ p @ intptr it)%I.
  Proof. apply _. Qed.

End intptr.
Notation "intptr< it >" := (intptr it) (only printing, format "'intptr<' it '>'") : printing_sugar.

Section programs.
  Context `{!typeG Σ}.

  Lemma type_cast_ptr_intptr (p : loc) β it ty m `{!LearnAlignment β ty m} T:
    (p ◁ₗ{β} ty -∗
      ⌜if m is Some m' then p `aligned_to` m' else True⌝ -∗
      ∃ n, loc_in_bounds p n ∗
      (⌜min_alloc_start ≤ p.2 ∧ p.2 + n ≤ max_alloc_end⌝ -∗
       ⌜p.2 ∈ it⌝ ∗
         ((alloc_alive_loc p ∗ True) ∧ ∀ v, T v (p @ intptr it))))
    ⊢ typed_un_op p (p ◁ₗ{β} ty) (CastOp (IntOp it)) PtrOp T.
  Proof.
    iIntros "HT Hp" (Φ) "HΦ".
    iDestruct (learnalign_learn with "Hp") as %?.
    iDestruct ("HT" with "Hp [//]") as (?) "[#Hlib HT]".
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %?.
    iDestruct (loc_in_bounds_has_alloc_id with "Hlib") as %[aid ?].
    iDestruct ("HT" with "[//]") as ([? ?]%(val_of_Z_is_Some (Some aid))) "HT".
    iApply wp_cast_ptr_int; [by apply val_to_of_loc|done|done|].
    iSplit; [by iDestruct "HT" as "[[$ _] _]" | iDestruct "HT" as "[_ HT]"].
    iApply ("HΦ" with "[] HT").
    iExists _. repeat iSplit; try iPureIntro.
    - done.
    - by apply: val_to_of_Z.
    - by apply: val_of_Z_to_prov.
    - iApply loc_in_bounds_shorten; [|done]. lia.
  Qed.
  Definition type_cast_ptr_intptr_inst := [instance type_cast_ptr_intptr].
  Global Existing Instance type_cast_ptr_intptr_inst.

  Lemma type_cast_ptr_intptr_val (v : val) (p : loc) it (n : nat) T:
    (⌜min_alloc_start ≤ p.2 ∧ p.2 + n ≤ max_alloc_end⌝ -∗
      v ◁ᵥ p @ ptr n -∗
      ⌜p.2 ∈ it⌝ ∗
       (alloc_alive_loc p ∗ True) ∧ ∀ v, T v (p @ intptr it))
    ⊢ typed_un_op v (v ◁ᵥ p @ ptr n) (CastOp (IntOp it)) PtrOp T.
  Proof.
    unfold ptr; simpl_type.
    iIntros "HT [-> #Hlib]" (Φ) "HΦ".
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %?.
    iDestruct (loc_in_bounds_has_alloc_id with "Hlib") as %[aid ?].
    iDestruct ("HT" with "[//] []") as ([? ?]%(val_of_Z_is_Some (Some aid))) "HT". { by iFrame "Hlib". }
    iApply wp_cast_ptr_int; [by apply val_to_of_loc|done|done|].
    iSplit; [by iDestruct "HT" as "[[$ _] _]" | iDestruct "HT" as "[_ HT]"].
    iApply ("HΦ" with "[] HT").
    iExists _. repeat iSplit; try iPureIntro.
    - done.
    - by apply: val_to_of_Z.
    - by apply: val_of_Z_to_prov.
    - iApply loc_in_bounds_shorten; [|done]. lia.
  Qed.
  Definition type_cast_ptr_intptr_val_inst := [instance type_cast_ptr_intptr_val].
  Global Existing Instance type_cast_ptr_intptr_val_inst.

  Lemma type_cast_intptr_ptr p v it T:
    ((alloc_alive_loc p ∗ True) ∧ T (val_of_loc p) (p @ frac_ptr Own (place p)))
    ⊢ typed_un_op v (v ◁ᵥ p @ intptr it) (CastOp PtrOp) (IntOp it) T.
  Proof.
    iIntros "HT (%aid&%&%&%&#Hlib)" (Φ) "HΦ".
    destruct p; simplify_eq /=.
    iApply wp_cast_int_ptr_alive => //.
    iSplit; [by iDestruct "HT" as "[[$ _] _]"| iDestruct "HT" as "[_ HT]"].
    iApply ("HΦ" with "[]"); last iApply "HT". unfold frac_ptr, place; simpl_type. done.
  Qed.
  Definition type_cast_intptr_ptr_inst := [instance type_cast_intptr_ptr].
  Global Existing Instance type_cast_intptr_ptr_inst.

  Lemma intptr_wand_int v p it:
    v ◁ᵥ p @ intptr it -∗ v ◁ᵥ p.2 @ int it.
  Proof. iIntros "(%aid&%&%&%&#Hlib)". unfold int; simpl_type. by iPureIntro. Qed.

  Lemma subsume_intptr_int_val A M v it (n : A → Z) (p : loc) T:
    (∃ x, ⌜n x = p.2⌝ ∗ T x)
    ⊢ subsume (v ◁ᵥ p @ intptr it) M (λ x, v ◁ᵥ (n x) @ int it) T.
  Proof.
    iIntros "[% [%Heq ?]] ? !>". iExists _. iFrame. rewrite Heq. by iApply intptr_wand_int.
  Qed.
  Definition subsume_intptr_int_val_inst := [instance subsume_intptr_int_val].
  Global Existing Instance subsume_intptr_int_val_inst.

  Lemma subsume_intptr_int_place A M l β it n p T:
    (∃ x, ⌜n x = p.2⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} p @ intptr it) M (λ x : A, l ◁ₗ{β} (n x) @ int it) T.
  Proof.
    iIntros "[% [%Heq ?]]". rewrite /ty_own /=. iIntros "(%v&%aid&%&%&%&%&?&?) !>".
    iFrame. by rewrite Heq.
  Qed.
  Definition subsume_intptr_int_place_inst := [instance subsume_intptr_int_place].
  Global Existing Instance subsume_intptr_int_place_inst.

  Lemma typed_un_op_intptr it v l op T:
      typed_un_op v (v ◁ᵥ l.2 @ int    it) op (IntOp it) T
    ⊢ typed_un_op v (v ◁ᵥ l   @ intptr it) op (IntOp it) T.
  Proof.
    iIntros "HT". iApply (typed_un_op_wand with "HT"). iApply intptr_wand_int.
  Qed.
  Definition typed_un_op_intptr_inst := [instance typed_un_op_intptr].
  Global Existing Instance typed_un_op_intptr_inst | 50.

  Lemma typed_bin_op_intptr_l it v1 l v2 ty op ot T:
      typed_bin_op v1 (v1 ◁ᵥ l.2 @ int    it) v2 (v2 ◁ᵥ ty) op (IntOp it) ot T
    ⊢ typed_bin_op v1 (v1 ◁ᵥ l   @ intptr it) v2 (v2 ◁ᵥ ty) op (IntOp it) ot T.
  Proof.
    iIntros "HT". iApply (typed_bin_op_wand with "HT"); last by iIntros "$".
    iApply intptr_wand_int.
  Qed.
  Definition typed_bin_op_intptr_l_inst := [instance typed_bin_op_intptr_l].
  Global Existing Instance typed_bin_op_intptr_l_inst | 50.

  Lemma typed_bin_op_intptr_r it v1 ty v2 l op ot T:
      typed_bin_op v1 (v1 ◁ᵥ ty) v2 (v2 ◁ᵥ l.2 @ int    it) op ot (IntOp it) T
    ⊢ typed_bin_op v1 (v1 ◁ᵥ ty) v2 (v2 ◁ᵥ l   @ intptr it) op ot (IntOp it) T.
  Proof.
    iIntros "HT". iApply (typed_bin_op_wand with "HT"); first by iIntros "$".
    iApply intptr_wand_int.
  Qed.
  Definition typed_bin_op_intptr_r_inst := [instance typed_bin_op_intptr_r].
  Global Existing Instance typed_bin_op_intptr_r_inst | 50.

End programs.
Global Typeclasses Opaque intptr_type intptr.
