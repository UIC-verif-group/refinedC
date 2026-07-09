From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset gmap frac agree excl_auth.
From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.spinlock Require Import generated_code.
Set Default Proof Using "Type".

Notation range k n := (seqZ k (n - k)) (only parsing).

Notation LAST_TICKET := (max_int u16 - 1) (only parsing).
Notation NO_TICKET   := (max_int u16) (only parsing).

Definition lockN : namespace := nroot.@"lockN".

Record lock_id := mk_lock_id {
  γ_lock    : gname;
  γ_tickets : gname;
  γ_owner   : gname;
}.

(** Registering the necessary ghost state. *)
Class spinlockG Σ := SpinLockG {
   lock_tickets_inG :: inG Σ (gmapR Z (exclR unitO));
   lock_owner_inG :: inG Σ (excl_authR ZO);
}.
Definition spinlockΣ : gFunctors :=
  #[GFunctor (constRF (gmapR Z (exclR unitO)));
    GFunctor (constRF (excl_authR ZO))].
Global Instance subG_spinlockG {Σ} : subG spinlockΣ Σ → spinlockG Σ.
Proof. solve_inG. Qed.

Section type.
  Context `{!typeG Σ} `{!lockG Σ} `{!spinlockG Σ}.

  Definition owner_auth (γ : gname) (i : Z) : iProp Σ :=
    own γ (●E i).

  Definition owner_frag (γ : gname) (i : Z) : iProp Σ :=
    own γ (◯E i).

  Definition spinlock_token (id : lock_id) (l : list string) : iProp Σ :=
    ∃ i, lock_token id.(γ_lock) l ∗ owner_auth id.(γ_owner) i.

  Definition ticket_aux (γ : gname) (i : Z) : iProp Σ :=
    own γ {[i := Excl ()]} ∗ ⌜i ≠ NO_TICKET⌝.

  Definition ticket (id : lock_id) (i : Z) : iProp Σ :=
    ticket_aux id.(γ_tickets) i.

  Definition ticket_range_def (id : lock_id) (k n : Z) : iProp Σ :=
    [∗ list] i ∈ range k n, ticket id i.

  Definition ticket_range_aux : seal (@ticket_range_def). by eexists. Qed.
  Definition ticket_range := unseal ticket_range_aux.
  Definition ticket_range_eq : @ticket_range = @ticket_range_def :=
    seal_eq ticket_range_aux.

  Global Instance ticket_range_timeless id k n: Timeless (ticket_range id k n).
  Proof. rewrite ticket_range_eq. apply _. Qed.

  Theorem ticket_range_empty (id : lock_id) (n : Z) :
    ⊢ True ∗-∗ ticket_range id n n.
  Proof.
    rewrite ticket_range_eq /ticket_range_def Z.sub_diag /=.
    by iSplit.
  Qed.

  Theorem ticket_range_insert_r (id : lock_id) (k n : Z) :
    0 ≤ k ≤ n →
    ticket_range id k n -∗ ticket id n -∗ ticket_range id k (n + 1).
  Proof.
    iIntros ([??]) "H1 H2". rewrite ticket_range_eq /ticket_range_def.
    assert (n + 1 - k = n - k + 1) as -> by lia.
    rewrite seqZ_app /=; [.. | by lia | by lia].
    assert (k + (n - k) = n) as -> by lia. by iFrame.
  Qed.

  Theorem split_first_ticket (id : lock_id) (k n : Z) :
    0 ≤ k < n →
    ticket_range id k n -∗ ticket id k ∗ ticket_range id (k + 1) n.
  Proof.
    iIntros ([??]) "H". rewrite ticket_range_eq /ticket_range_def.
    assert (n - (k + 1) = n - k - 1) as -> by lia.
    assert (n - k > 0) as Hnk by lia. revert Hnk. generalize (n-k).
    clear. move => n Hn.
    assert (∃ m, n = 1 + m ∧ 0 ≤ m) as [m [-> ?]].
    { exists (n - 1). split; lia. }
    rewrite seqZ_app /=; try by lia. assert (1 + m - 1 = m) as -> by lia.
    by iFrame.
  Qed.

  Theorem ticket_non_duplicable (id : lock_id) (i1 i2 : Z) :
    i1 = i2 →
    ticket id i1 -∗ ticket id i2 -∗ False.
  Proof.
    iIntros (->) "[H1 _] [H2 _]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %H. iPureIntro.
    apply singleton_valid in H. by eapply exclusive_r.
  Qed.

  Theorem ticket_not_NO_TICKET (id : lock_id) (i : Z) :
    ticket id i -∗ ⌜i ≠ NO_TICKET⌝.
  Proof.
    iIntros "[_ $]".
  Qed.

  Theorem ticket_already_in_range (id : lock_id) (k n i : Z) :
    ⌜i ∈ range k n⌝ -∗ ticket_range id k n -∗ ticket id i -∗ False.
  Proof.
    iIntros (Hi) "Hr Ht". rewrite ticket_range_eq /ticket_range_def.
    iDestruct (big_sepL_elem_of with "Hr") as "Ht'" => //.
    by iApply (ticket_non_duplicable with "Ht Ht'").
  Qed.

  Theorem overlaping_ticket_ranges (id : lock_id) (k1 k2 n1 n2 : Z) :
    ⌜∃ i, i ∈ range k1 n1 ∧ i ∈ range k2 n2⌝ -∗ ticket_range id k1 n1 -∗ ticket_range id k2 n2 -∗ False.
  Proof.
    iIntros ([i [??]]) "Hr1 Hr2". rewrite ticket_range_eq.
    iDestruct (big_sepL_elem_of with "Hr1") as "Ht1" => //.
    iDestruct (big_sepL_elem_of with "Hr2") as "Ht2" => //.
    by iApply (ticket_non_duplicable with "Ht1 Ht2").
  Qed.

  Theorem alloc_tickets_aux_generic (ks : list Z) :
    Forall (λ i, i ≠ NO_TICKET) ks →
    NoDup ks →
    ⊢ |==> ∃ γ, [∗ list] i ∈ ks, ticket_aux γ i.
  Proof.
    move => Hks1 Hks2.
    iMod (own_alloc (list_to_map ((λ i, (i, Excl ())) <$> ks))) as (γ) "Hγ".
    { induction ks as [|k ks IH] => //=. apply insert_valid => //.
      apply Forall_cons in Hks1 as [Hk1 Hks1].
      apply NoDup_cons in Hks2 as [Hk2 Hks2].
      exact (IH Hks1 Hks2). }
    iModIntro. iExists γ. iInduction ks as [|k ks] "IH" => //=.
    apply Forall_cons in Hks1 as [Hk1 Hks1].
    apply NoDup_cons in Hks2 as [Hk2 Hks2].
    rewrite insert_singleton_op.
    - iDestruct "Hγ" as "[$ Hks]".
      iSplit; first done. by iApply "IH".
    - rewrite -/fmap /cmra_car /=. apply not_elem_of_list_to_map.
      by rewrite -list_fmap_compose list_elem_of_fmap_inj.
  Qed.

  Theorem alloc_tickets_aux :
    ⊢ |==> ∃ γ, [∗ list] i ∈ range 0 (LAST_TICKET + 1), ticket_aux γ i.
  Proof.
    iMod (alloc_tickets_aux_generic); last done.
    - apply Forall_seqZ. move => *. lia.
    - apply NoDup_seqZ.
  Qed.

  Theorem alloc_auth_owner (i : Z) :
    ⊢ |==> ∃ γ, owner_auth γ i ∗ owner_frag γ i.
  Proof.
    iMod (own_alloc (●E i ⋅ ◯E i)) as (γ) "H"; first by apply auth_both_valid.
    iExists γ. iModIntro. by iDestruct "H" as "[$ $]".
  Qed.

  Theorem owner_auth_update γ E (i j k : Z) :
    owner_auth γ i -∗ owner_frag γ j ={E}=∗ owner_auth γ k ∗ owner_frag γ k.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    rewrite /owner_auth /owner_frag -!own_op.
    iMod (own_update with "H"); last done. by apply excl_auth_update.
  Qed.

  Theorem owner_auth_agree γ (i j : Z) :
    owner_auth γ i -∗ owner_frag γ j -∗ ⌜i = j⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    by iDestruct (own_valid with "H") as %H%excl_auth_agree_L.
  Qed.

  Theorem alloc_lock_token_and_tickets :
    ⊢ |==> ∃ id, spinlock_token id [] ∗
                  ticket_range id 0 (LAST_TICKET + 1) ∗
                  owner_frag id.(γ_owner) 0.
  Proof.
    iMod (alloc_lock_token) as (γl) "Hγl".
    iMod (alloc_tickets_aux) as (γt) "Hγt".
    iMod (alloc_auth_owner 0) as (γo) "[H● H◯]".
    iModIntro. iExists {|γ_lock := γl; γ_tickets := γt; γ_owner := γo|}.
    rewrite ticket_range_eq. iFrame "Hγt". eauto with iFrame.
  Qed.

  Global Instance inv_own_constraint (N : namespace) (P : iProp Σ):
    OwnConstraint (λ β, match β return _ with Own => P | Shr => inv N P end).
  Proof.
    constructor; first apply _.
    iIntros (??) "H". by iMod (inv_alloc with "H").
  Qed.

  Definition with_invariant (ty : type) (N : namespace) (P : iProp Σ) : type :=
    own_constrained (λ β, match β return _ with Own => P | Shr => inv N P end) ty.

  Definition hyp_spinlock_t_invariant (id : lock_id) (p1 p2 : loc) : iProp Σ := (
    ∃ owner next : Z,
      p1 ◁ₗ owner @ int u16 ∗
      p2 ◁ₗ next  @ int u16 ∗
      ⌜owner ≤ next ∧ owner ≠ NO_TICKET⌝ ∗
      owner_frag id.(γ_owner) owner ∗
      ticket_range id 0 owner ∗
      ticket_range id next (LAST_TICKET + 1) ∗
      ((ticket id owner ∗ ⌜owner < next⌝) ∨ spinlock_token id [])
  )%I.

  Global Instance hyp_spinlock_t_timeless id o n: Timeless (hyp_spinlock_t_invariant id o n).
  Proof. rewrite /hyp_spinlock_t_invariant /ty_own /=. apply _. Qed.

  Definition hyp_spinlock_t (id : lock_id) : type :=
    tyexists (λ p1, tyexists (λ p2,
      with_invariant (
        struct struct_hyp_spinlock [ place p1 ; place p2 ]
      ) lockN (hyp_spinlock_t_invariant id p1 p2)
    )).

  Global Instance with_lock_id_hyp_spinlock_t id : WithLockId (hyp_spinlock_t id) (id.(γ_lock)) := I.
End type.

Global Typeclasses Opaque hyp_spinlock_t lock_token.
