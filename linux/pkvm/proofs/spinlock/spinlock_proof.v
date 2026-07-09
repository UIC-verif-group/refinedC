From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.spinlock Require Import generated_code.
From refinedc.linux.pkvm.spinlock Require Import generated_spec.
From refinedc.linux.pkvm.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

Section proofs.
  Context `{!typeG Σ} `{!globalG Σ} `{!lockG Σ} `{!spinlockG Σ}.

  (* TODO: refactor proof and remove (some of) these transparent commands *)
  Local Typeclasses Transparent ty_own ty_own_val with_refinement.
  Local Typeclasses Transparent hyp_spinlock_t spinlock_token.
  Local Typeclasses Transparent frac_ptr_type frac_ptr place.

  (* Typing proof for [hyp_spin_lock_init]. *)
  Lemma type_hyp_spin_lock_init :
    ⊢ typed_function impl_hyp_spin_lock_init type_of_hyp_spin_lock_init.
  Proof.
    start_function "hyp_spin_lock_init" (p) => lock.
    split_blocks (∅ : gmap label (iProp Σ)) (@nil Prop).
    (* Allocate the resources for the lock. *)
    iMod (alloc_lock_token_and_tickets) as (id) "(?&?&?)".
    (* Run the automation. *)
    repeat liRStep; liShow.
    liInst (λ x, x.1ₗ = id).
    unfold hyp_spinlock_t_invariant.
    repeat liRStep; liShow.
    (* Establish the invariant *)
    liFromSyntax. rewrite right_id. iModIntro. iFrame.
    (* TODO: add simplify_goal rule for this *)
    by iApply ticket_range_empty.
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
  Qed.

  (* Typing proof for [hyp_spin_lock]. *)
  Lemma type_hyp_spin_lock :
    ⊢ typed_function impl_hyp_spin_lock type_of_hyp_spin_lock.
  Proof.
    start_function "hyp_spin_lock" ([[p id] s]) => var_lock local_got_it local_ticket local_next.
    split_blocks
      ((<[ "#1" :=
             (* First loop: checking that we got the ticket, we do if [got_it] is [true]. *)
             ∃ b : bool, ∃ i : Z,
             var_lock ◁ₗ p @ &frac{s} (hyp_spinlock_t id) ∗
             local_got_it ◁ₗ b @ builtin_boolean ∗
             local_ticket ◁ₗ i @ int u16 ∗
             local_next ◁ₗ uninit u16 ∗
             (if b then ticket id i else True) ]> $
        <[ "#7" :=
             (* Nested loop: we read a potential ticket number.
                We will know that it is not NO_TICKET when we exit the loop. *)
             ∃ i : Z,
             var_lock ◁ₗ p @ &frac{s} (hyp_spinlock_t id) ∗
             local_got_it ◁ₗ uninit bool_layout ∗
             local_ticket ◁ₗ i @ int u16 ∗
             local_next ◁ₗ uninit u16 ]> $
        <[ "#4" :=
             (* Last loop: we have the ticket, waiting for our turn. *)
             ∃ i : Z,
             var_lock ◁ₗ p @ &frac{s} (hyp_spinlock_t id) ∗
             local_got_it ◁ₗ uninit bool_layout ∗
             local_ticket ◁ₗ i @ int u16 ∗
             local_next ◁ₗ uninit u16 ∗
             ticket id i ]> ∅)%I : gmap label (iProp Σ))
      (@nil Prop).
    - (* #0 Initial block, running the nested loop for the first time. *)
      destruct s.
      + repeat liRStep; liShow.
        iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "(?&?&[%%]&?&?&?&?)".
        repeat liRStep; liShow.
        rewrite /hyp_spinlock_t_invariant.
        repeat liRStep; liShow.
      + repeat liRStep; liShow.
        iModIntro. iExists (Shr, tytrue). iSplitR; first by simpl.
        iDestruct select (inv _ _) as "#Hinv".
        iInv "Hinv" as ">Inv".
        iDestruct "Inv" as (owner next) "(Howner&Hnext&%&Hrest)".
        iApply typed_read_end_mono_strong; [done|]. iIntros "_ !>".
        iExists _, _, True%I. iFrame. iSplit; [done|].
        unshelve iApply type_read_copy. { apply _. } simpl.
        iSplit; [done|]. iSplit; [iPureIntro; solve_ndisj|]. iIntros (v) "_ Hl Hv !>".
        iExists tytrue, (next @ int u16)%I. iSplit; [done|]. iSplit; [done|]. iModIntro.
        iSplitL "Howner Hrest Hl Hv". {
          iNext. rewrite /hyp_spinlock_t_invariant. by iFrame.
        }
        iIntros "_". repeat liRStep; liShow.
    - (* #1 First loop (after the initial run), checking if we got the ticket. *)
      destruct s.
      + repeat liRStep; liShow. iIntros "!> Hb".
        repeat liRStep; liShow.
        iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "(?&?&[%%]&?&?&?&?)".
        repeat liRStep; liShow.
        rewrite /hyp_spinlock_t_invariant.
        repeat liRStep; liShow.
      + repeat liRStep; liShow. iIntros "!> Hb".
        repeat liRStep; liShow.
        iModIntro. iExists (Shr, tytrue); iSplitR; first by simpl.
        iDestruct select (inv _ _) as "#Hinv".
        iInv "Hinv" as ">Inv".
        iDestruct "Inv" as (owner next) "(Howner&Hnext&%&Hrest)".
        iApply typed_read_end_mono_strong; [done|]. iIntros "_ !>".
        iExists _, _, True%I. iFrame.
        unshelve iApply type_read_copy. { apply _. } simpl.
        iSplit; [done|]. iSplit; [iPureIntro; solve_ndisj|]. iIntros (v') "_ Hl Hv !>".
        iExists tytrue, (next @ int u16)%I. iSplit; [done|]. iSplit; [done|]. iModIntro.
        iSplitL "Howner Hrest Hl Hv". {
          iNext. rewrite /hyp_spinlock_t_invariant. by iFrame.
        }
        iIntros "_". repeat liRStep; liShow.
    - (* #7 Code that eventually goes to the CAS and takes care of the loop. *)
      destruct s.
      + liRStepUntil @typed_if. do 4 liRStep; liShow.
        * repeat liRStep; liShow.
          iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "(?&?&[%%]&?&?&?&?)".
          repeat liRStep; liShow.
          rewrite /hyp_spinlock_t_invariant.
          repeat liRStep; liShow.
        * liRStepUntil typed_cas.
          iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "(?&?&[%%]&?&?&?&?)".
          iIntros "!> ???" (Φ) "HΦ".
          destruct (decide (next = i)) as [<-|] .
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (next + 1) @ int u16)%I into "Hnext+1".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_suc_int with "Hnext Hticket [$]"). { cbv. lia. } 1: done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (true @ builtin_boolean)%I) => //.
             { iExists _. done. }
             repeat liRStep; liShow.
             rewrite /hyp_spinlock_t_invariant.
             repeat liRStep; liShow.
             iRename select (ticket_range _ _ _) into "Htks".
             iDestruct (split_first_ticket with "Htks") as "[Hnext $]".
             { split; last by lia. by transitivity (min_int u16) => //. }
             iRename select (_ ∨ _)%I into "Hcases".
             iModIntro. iSplitL "Hcases".
             { iDestruct "Hcases" as "[[H %]|H]"; [iLeft | iRight] => //. iSplitL => //. iPureIntro. lia. }
             repeat liRStep; liShow.
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (i + 1) @ int u16)%I into "Hi+1".
             iDestruct select (_ ◁ᵥ (i + 1) @ int u16)%I as "Hv".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_fail_int with "Hnext Hticket [$]"). { cbv. lia. } 1: done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (false @ builtin_boolean)%I) => //.
             { by iExists _. }
             repeat liRStep; liShow.
             rewrite /hyp_spinlock_t_invariant.
             repeat liRStep; liShow.
      + liRStepUntil @typed_if. do 4 liRStep; liShow.
        * repeat liRStep; liShow.
          iModIntro. iExists (Shr, tytrue); iSplitR; first by simpl.
          iDestruct select (inv _ _) as "#Hinv".
          iInv "Hinv" as ">Inv".
          iDestruct "Inv" as (owner next) "(Howner&Hnext&%&Hrest)".
          iApply typed_read_end_mono_strong; [done|]. iIntros "_ !>".
          iExists _, _, True%I. iFrame. iSplit; [done|].
          unshelve iApply type_read_copy. { apply _. } simpl.
          iSplit; [done|]. iSplit; [iPureIntro; solve_ndisj|]. iIntros (v') "_ Hl Hv !>".
          iExists tytrue, (next @ int u16)%I. iSplit; [done|]. iSplit; [done|]. iModIntro.
          iSplitL "Howner Hrest Hl Hv". {
            iNext. rewrite /hyp_spinlock_t_invariant. by iFrame.
          }
          iIntros "_". repeat liRStep; liShow.
        * liRStepUntil typed_cas.
          iIntros "!> ???" (Φ) "HΦ".
          iDestruct select (inv _ _) as "#Hinv".
          iInv "Hinv" as ">Inv" "Hclose_inv".
          iDestruct "Inv" as (owner next) "(Howner&Hnext&[%%]&Hrest)".
          destruct (decide (next = i)) as [<-|] .
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (next + 1) @ int u16)%I into "Hnext+1".
             iDestruct select (_ ◁ᵥ (next + 1) @ int u16)%I as "Hv".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_suc_int with "Hnext Hticket [$]"). { cbv. lia. } 1: done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (true @ builtin_boolean)%I) => //.
             { by iExists _. }
             iRename select (p at{struct_hyp_spinlock}ₗ "next" ◁ₗ _)%I into "Hnext".
             iDestruct "Hrest" as "(Hfrag&Hr1&Hr2&Hcases)".
             iDestruct (split_first_ticket with "Hr2") as "[Hticket Hr2]".
             { split; last by lia. by transitivity (min_int u16). }
             iMod ("Hclose_inv" with "[Howner Hnext Hfrag Hr1 Hr2 Hcases]") as "_".
             { iNext. iExists owner, (next + 1). iFrame.
               iSplit. { iPureIntro. lia. }
               iDestruct "Hcases" as "[[H %]|H]"; [iLeft | iRight] => //.
               iSplitL => //. iPureIntro. lia. }
             iModIntro.
             repeat liRStep; liShow.
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (i + 1) @ int u16)%I into "Hi+1".
             iDestruct select (_ ◁ᵥ (i + 1) @ int u16)%I as "Hv".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_fail_int with "Hnext Hticket [$]"). { cbv. lia. } 1: done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (false @ builtin_boolean)%I) => //.
             { by iExists _. }
             iRename select (p at{struct_hyp_spinlock}ₗ _ ◁ₗ _)%I into "Hnext".
             iMod ("Hclose_inv" with "[Howner Hnext Hrest]") as "_".
             { iNext. iExists owner, next. iFrame "Howner". iFrame "Hnext". iFrame "Hrest". done. }
             iModIntro.
             repeat liRStep; liShow.
    - (* #4 Final loop: checking if we are the owner. *)
      destruct s.
      + repeat liRStep; liShow.
        iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "(?&?&[%%]&?&?&?&?)".
        liRStepUntil @typed_if. do 4 liRStep; liShow.
        * repeat liRStep; liShow. rewrite /hyp_spinlock_t_invariant. repeat liRStep; liShow.
        * repeat liRStep; liShow. rewrite /hyp_spinlock_t_invariant.
          liRStepUntil (_ ∗ _)%I.
          iDestruct select (_ ∨ _)%I as "[[Ht _]|Htok]".
          { iExFalso. iRevert "Ht". iRename select (ticket _ _) into "Ht"; iRevert "Ht".
            iIntros "Ht1 Ht2". by iApply (ticket_non_duplicable with "Ht1 Ht2"). }
          iAssert (⌜i ≠ next⌝)%I as "%".
          { iIntros (<-). iRename select (ticket _ _) into "Hticket".
            iRename select (ticket_range _ i _) into "Hrange".
            iApply (ticket_already_in_range with "[] Hrange Hticket").
            iPureIntro. apply elem_of_seqZ. lia. }
          repeat liRStep; liShow.
          iModIntro. iSplitR "Htok"; last by iFrame. iLeft. iSplit => //. iPureIntro. lia.
      + repeat liRStep; liShow.
        iModIntro. iExists (Shr, tytrue); iSplitR; first by simpl.
        iDestruct select (inv _ _) as "#Hinv".
        iInv "Hinv" as ">Inv".
        iDestruct "Inv" as (owner next) "(Howner&Hnext&%&Hrest)".
        iApply typed_read_end_mono_strong; [done|]. iIntros "_ !>".
        iExists _, _, True%I. iFrame. iSplit; [done|].
        unshelve iApply type_read_copy. { apply _. } simpl.
        iSplit; [done|]. iSplit; [iPureIntro; solve_ndisj|]. iIntros (v') "_ Hl Hv !>".
        iExists tytrue, (owner @ int u16)%I. iSplit; [done|]. iSplit; [done|]. iModIntro.
        destruct (decide (i ≠ owner)).
        * iSplitL "Hnext Hrest Hl Hv". {
            iNext. rewrite /hyp_spinlock_t_invariant. by iFrame.
          }
          iIntros "_". repeat liRStep; liShow.
        * assert (i = owner) as -> by lia.
          iRename select (ticket _ _) into "Hticket".
          iDestruct "Hrest" as "(Hfrag&Hr1&Hr2&Hcases)".
          iDestruct "Hcases" as "[[Hticket' %] | Htok]".
          { iExFalso. by iApply (ticket_non_duplicable with "Hticket Hticket'"). }
          iAssert (⌜owner ∈ u16⌝)%I as %[??].
          { rewrite /ty_own_val /=. by iDestruct "Hv" as %Hv%val_to_Z_in_range. }
          iAssert (⌜owner < next⌝)%I as %?.
          { destruct (decide (owner < next)); first done. iExFalso.
            iDestruct (ty_size_eq _ (IntOp _) MCNone with "Hv") as %?; [done|].
            iApply (ticket_already_in_range with "[] Hr2 Hticket").
            iPureIntro. clear Q. apply elem_of_seqZ. lia. }
          iSplitL "Hnext Hl Hv Hfrag Hr1 Hr2 Hticket". {
            iNext. rewrite /hyp_spinlock_t_invariant. iExists owner, next.
            iFrame. iSplit; first done. iLeft. by iSplit.
          }
          iIntros "_". repeat liRStep; liShow.
    (* Solving side-conditions. *)
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
  Qed.

  (* Typing proof for [hyp_spin_unlock]. *)
  Lemma type_hyp_spin_unlock :
    ⊢ typed_function impl_hyp_spin_unlock type_of_hyp_spin_unlock.
  Proof.
    start_function "hyp_spin_unlock" ([[p id] s]) => lock ticket.
    split_blocks (∅ : gmap label (iProp Σ)) (@nil Prop).
    (* Extract the real token and our ticket number (owner) with a witness. *)
    iDestruct select (spinlock_token _ _) as (owner) "[Htok H●]".
    (* Run the automation, until we must look into the invariant. *)
    repeat liRStep; liShow. iIntros "!> Hinv". repeat liRStep; liShow.
    (* We do a different proof depending on the ownership state. *)
    destruct s.
    - (* [Own] case: we have full ownership. *)
      iDestruct select (hyp_spinlock_t_invariant _ _ _) as
          (owner' next) "(Howner&?&[%%]&H◯&Hr1&?&Hcases)".
      (* We have the token: we are the owner and our ticket is in [Hcases]. *)
      iDestruct (owner_auth_agree with "H● H◯") as %<-.
      iDestruct "Hcases" as "[[Hticket %] | Htok']"; last first.
      { iExFalso. iDestruct "Htok'" as (?) "[Htok' _]".
        iApply (lock_token_exclusive with "Htok Htok'"). }
      (* We put our ticket at the end of the first ticket range. *)
      iDestruct (ty_own_int_in_range with "Howner") as %[Hmin ?].
      rewrite /min_int /= in Hmin.
      iDestruct (ticket_range_insert_r with "Hr1 Hticket") as "Hr1"; first by lia.
      (* Run the automation up to the [if] statement. *)
      liRStepUntil @typed_if. do 4 liRStep; liShow.
      + (* We have the last ticket. The next owner will be 0, we update. *)
        iModIntro.
        iMod (owner_auth_update _ _ _ _ 0%nat with "H● H◯") as "[??]".
        (* Run the automation to the end of the function. *)
        repeat liRStep; liShow.
        (* Establish the invariant again, placing the token back inside. *)
        rewrite /hyp_spinlock_t_invariant.
        repeat liRStep; liShow.
        liFromSyntax. iModIntro.
        iSplitR; first by iApply ticket_range_empty. iSplit; [|done].
        iFrame. iRight. iFrame.
      + (* We do not have the last ticket, we do not reset the queue. *)
        iModIntro.
        iMod (owner_auth_update _ _ _ _ (owner + 1) with "H● H◯") as "[??]".
        (* Run the automation to the end of the function. *)
        repeat liRStep; liShow.
        (* Establish the invariant again, placing the token back inside. *)
        rewrite /hyp_spinlock_t_invariant.
        repeat liRStep; liShow.
        liFromSyntax. iModIntro. iSplit; [|done]. iRight. iFrame.
    - (* [Shr] case: we have shared ownership, we first run the automation. *)
      repeat liRStep; liShow.
      (* We must open the invariant to read. *)
      iModIntro. iExists (Shr, tytrue); iSplitR; first by simpl.
      iDestruct select (inv _ _) as "#Hinv".
      iInv "Hinv" as ">Inv".
      iDestruct "Inv" as (owner' next) "(Howner&Hnext&%&H◯&Hrest)".
      iDestruct (owner_auth_agree with "H● H◯") as %<-.
      iApply typed_read_end_mono_strong; [done|]. iIntros "_ !>".
      iExists _, _, True%I. iFrame. iSplit; [done|].
      unshelve iApply type_read_copy. { apply _. } simpl.
      iSplit; [done|]. iSplit; [iPureIntro; solve_ndisj|]. iIntros (v') "_ Hl Hv !>".
      iExists tytrue, (owner @ int u16)%I. iSplit; [done|]. iSplit; [done|]. iModIntro.
      iSplitL "Hnext Hrest Hl Hv H◯". {
          iNext. rewrite /hyp_spinlock_t_invariant. by iFrame.
      }
      iIntros "_".
      (* Run the automation to the write to [owner] of each branch. *)
      repeat liRStep; liShow.
      + (* We have the last ticket. The next owner will be 0, we update. *)
        (* We must open the invariant again. *)
        iModIntro. iExists (Shr, tytrue); iSplitR; first by simpl.
        iInv "Hinv" as ">Inv".
        iDestruct "Inv" as (owner' next') "(Howner&Hnext&[%%]&H◯&Htk1&Htk2&Hcases)".
        (* We have the token: we are the owner and our ticket is in [Hcases]. *)
        iDestruct (owner_auth_agree with "H● H◯") as %<-.
        iDestruct "Hcases" as "[[Hticket %] | Htok']"; last first.
        { iExFalso. iDestruct "Htok'" as (?) "[Htok' _]".
          iApply (lock_token_exclusive with "Htok Htok'"). }
        (* The owner will be 0, update the witness. *)
        iMod (owner_auth_update _ _ _ _ 0%nat with "H● H◯") as "[H● H◯]".
        (* Learn that [next'] actually is [max_int u16]. *)
        iAssert ⌜next' = max_int u16⌝%I as %->.
        { iDestruct (ty_deref _ (IntOp _) MCNone with "Hnext") as (w) "[_ H]"; [done|].
          unfold int; simpl_type. iDestruct "H" as %Hnext.
          iPureIntro. apply val_to_Z_in_range in Hnext as [??]. lia. }
        (* We perform the write and close the invariant. *)
        iApply typed_write_end_mono_strong; [done|].
        iIntros "Hv2 _ !>". iExists _, _, _, True%I. iFrame. iSplit; [done|].
        iApply type_write_own_copy. iSplit; [done|].
        iIntros "Hv _ Hl !>". iExists tytrue. iSplit; [done|]. iModIntro.
        iSplitL "Htok H● H◯ Hnext Hl Hv". {
          iNext. iExists 0, (LAST_TICKET + 1). iFrame.
          iSplit. { iPureIntro. split => //. }
          do 2 (iSplitR; first by iApply ticket_range_empty).
          iRight. iFrame "Htok". by iExists _.
        }
        iIntros "_".
        (* We have all the tickets, let's combine them. *)
        iAssert (ticket_range id 0 (LAST_TICKET + 1)) with "[Htk1 Htk2 Hticket]" as "Htk".
        { iDestruct (ticket_range_insert_r with "Htk1 Hticket") as "Hr" => //. }
        (* Run the automation up to the write to the [next] field, open invariant. *)
        repeat liRStep; liShow.
        iModIntro. iExists (Shr, tytrue); iSplitR; first by simpl.
        iInv "Hinv" as ">Inv".
        iDestruct "Inv" as (owner' next'') "(Howner&Hnext&[%%]&H◯&Htr1&Htr2&Hcases)".
        (* We can get [owner' = 0] since we have all the tickets. *)
        iAssert ⌜owner' = 0⌝%I as %->.
        { destruct (decide (owner' = 0)) => //. iExFalso.
          iDestruct (ty_deref _ (IntOp _) MCNone with "Howner") as (?) "[? Hv]"; [done|].
          unfold int; simpl_type.
          iDestruct "Hv" as %Howner%val_to_Z_in_range.
          destruct Howner as [Howner ?].
          iDestruct (overlaping_ticket_ranges with "[] Htk Htr1") as "$".
          iPureIntro. exists 0. split; apply elem_of_seqZ; try done.
          split => //. rewrite /min_int /= in Howner. lia. }
        (* Our ticket cannot be in [Hcases], we have it already. *)
        iDestruct "Hcases" as "[[?_] | Htok]".
        { iExFalso. iRename select (spinlock_def.ticket _ _) into "Hticket".
          iDestruct (ticket_already_in_range with "[] Htk Hticket") as "$".
          iPureIntro. apply elem_of_seqZ => //. }
        (* Learn that [next''] is [max_int u16]. *)
        iAssert ⌜next'' = max_int u16⌝%I as %->.
        { destruct (decide (next'' = max_int u16)); first done. iExFalso .
          destruct H as [??]. iDestruct (ty_own_int_in_range with "Hnext") as %[??].
          iDestruct (overlaping_ticket_ranges with "[] Htk Htr2") as "$".
          iExists next''. iPureIntro. split; apply elem_of_seqZ; lia. }
        (* We perform the write and close the invariant. *)
        iApply typed_write_end_mono_strong; [done|].
        iIntros "Hv2 _ !>". iExists _, _, _, True%I. iFrame. iSplit; [done|].
        iApply type_write_own_copy. iSplit; [done|].
        iIntros "Hv _ Hl !>". iExists tytrue. iSplit; [done|]. iModIntro.
        iRename select (ticket ◁ₗ _)%I into "Hticket_var".
        iSplitR "Hticket_var". { iNext. iExists 0, 0. by iFrame. }
        iIntros "_".
        (* Run the automation to finish the branch. *)
        repeat liRStep; liShow.
      + (* We do not have the last ticket, we do not reset the queue. *)
        (* We must open the invariant again. *)
        iModIntro. iExists (Shr, tytrue); iSplitR; first by simpl.
        iInv "Hinv" as ">Inv".
        iDestruct "Inv" as (owner' next') "(Howner&Hnext&[% %]&H◯&Htk1&Htk2&Hcases)".
        (* We have the token: we are the owner and our ticket is in [Hcases]. *)
        iDestruct (owner_auth_agree with "H● H◯") as %<-.
        iDestruct "Hcases" as "[[Hticket %] | Htok']"; last first.
        { iExFalso. iDestruct "Htok'" as (?) "[Htok' _]".
          iApply (lock_token_exclusive with "Htok Htok'"). }
        (* The owner will be [owner + 1], update the witness. *)
        iMod (owner_auth_update _ _ _ _ (owner + 1) with "H● H◯") as "[H● H◯]".
        iApply typed_write_end_mono_strong; [done|].
        iIntros "Hv2 _ !>". iExists _, _, _, True%I. iFrame. iSplit; [done|].
        iApply type_write_own_copy. iSplit; [done|].
        iIntros "Hv _ Hl !>". iExists tytrue. iSplit; [done|]. iModIntro.
        iSplitL "Htok H● H◯ Hticket Hnext Hl Htk1 Htk2". {
          iNext. iExists (owner + 1), next'. iFrame.
          iDestruct (ticket_range_insert_r with "Htk1 Hticket") as "$".
          { split; first done. by transitivity (min_int u16). }
          iSplit. { iPureIntro. by lia. }
          iRight. iFrame "Htok". by iExists _.
        }
        iIntros "_".
        (* Run the automation to finish the branch. *)
        repeat liRStep; liShow.
    (* Solving side-conditions. *)
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
  Qed.
End proofs.
