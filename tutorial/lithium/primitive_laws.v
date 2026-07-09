From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export gen_heap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import ectx_lifting.
From lithium.tutorial Require Export lang notation.
From lithium.tutorial Require Import tactics.

Class tutorialGS (Σ : gFunctors) := TutorialGS {
    tutorial_invGS : invGS Σ;
    tutorial_gen_heapGS :: gen_heapGS loc val Σ;
}.

Global Instance tutorial_irisG `{!tutorialGS Σ} : irisGS tutorial_lang Σ := {
  iris_invGS := tutorial_invGS;
  state_interp σ κs _ _ := gen_heap_interp σ.(heap);
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.

Definition val_pointsto `{!tutorialGS Σ} (v1 : val) (dq : dfrac) (v2 : val) : iProp Σ :=
  ∃ l : loc, ⌜v1 = #l⌝ ∗ pointsto l dq v2.

Notation "v1 ↦ dq v2" := (val_pointsto v1 dq v2)
  (at level 20, dq custom dfrac at level 1, format "v1  ↦ dq  v2") : bi_scope.


Section lifting.
  Context `{!tutorialGS Σ}.

  (** Heap *)
  Lemma wp_alloc s E Φ :
    (∀ v, v ↦ #0 -∗ Φ v) -∗ WP Alloc @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ1 κ κs n nt) "Hσ !>"; iSplit; first by auto with base_step.
    iIntros "!>" (v2 σ2 efs Hstep) "_Hcred"; inv_base_step.
    iMod (gen_heap_alloc with "Hσ") as "[Hσ [Hl _]]"; first done.
    iModIntro; iSplit=> //. iFrame. iApply "HΦ". iExists _. by iFrame.
  Qed.

  Lemma wp_load s E Φ v1 v2 :
    v1 ↦ v2 -∗ (v1 ↦ v2 -∗ Φ v2) -∗ WP Load v1 @ s; E {{ Φ }}.
  Proof.
    iIntros "[%l [-> Hl]] HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ1 κ κs n nt) "Hσ !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto with base_step.
    iIntros "!>" (? σ2 efs Hstep) "_Hcred"; inv_base_step.
    iModIntro; iSplit=> //. iFrame. iApply "HΦ". iExists _. by iFrame.
  Qed.

  Lemma wp_store s E Φ v1 v (w : val) :
    v1 ↦ v -∗ (v1 ↦ w -∗ Φ w) -∗ WP Store v1 w @ s; E {{ Φ }}.
  Proof.
    iIntros "[%l [-> Hl]] HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
    iIntros (σ1 κ κs n nt) "Hσ !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto with base_step.
    iIntros "!>" (v2 σ2 efs Hstep) "_Hcred"; inv_base_step.
    iMod (gen_heap_update with "Hσ Hl") as "[Hσ Hl]".
    iModIntro; iSplit=> //. iFrame. iApply "HΦ". iExists _. by iFrame.
  Qed.
End lifting.

Global Typeclasses Opaque val_pointsto.
