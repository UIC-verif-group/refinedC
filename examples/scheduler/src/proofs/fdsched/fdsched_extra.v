From refinedc.examples.scheduler.src.fdsched Require Export message_extra.
From refinedc.examples.scheduler.src.fdsched Require Export priority_extra.
From refinedc.examples.scheduler.src.fdsched Require Export scheduler_extra.
From refinedc.examples.scheduler.src.fdsched Require Export misc_lemmas.
From refinedc.examples.scheduler.src.fdsched Require Export basic_definitions.

(** * upstream *)
(* TODO: upstream the following definitions *)
Global Instance simpl_plus_eq_l (x y z z' : nat):
  SimplBothRel (=) (x + y + z)%nat (x + z')%nat (y + z = z')%nat.
Proof. split; lia. Qed.

Global Instance simpl_sum_list_cons l l' x :
  SimplAndUnsafe (sum_list l + x = sum_list l')%nat (l' = l ++ [x]).
Proof. intros ->; induction l => //=; lia. Qed.

Global Instance simpl_add_0 m n :
  SimplAndRel (=) n (n + m)%nat (m = 0)%nat.
Proof. split; lia. Qed.

Global Instance simpl_sum_list_nil l :
  SimplAndRel (=) (sum_list l) 0%nat (∃ n, l = replicate n 0%nat).
Proof.
  split.
  - intros [n ->]. rewrite sum_list_replicate; lia.
  - induction l as [ | [ | ] l' IH] => /=; try lia.
    + intros _. by exists 0%nat.
    + intros.
      destruct (IH ltac:(lia)) as [n ->].
      exists (n + 1)%nat. by rewrite Nat.add_1_r.
Qed.

Global Instance simpl_list_trivial_match {A} (l : list A) :
  SimplAnd (if l is [] then True else False) (l = []).
Proof. split; solve_goal. Qed.

Section upstream.
  Context `{!typeG Σ}.

  Lemma subsume_array_insert_id A l ly ty elts elts' i β G :
    subsume (l ◁ₗ{β} array ly (<[ i := ty ]> elts)) (λ x : A, l ◁ₗ{β} array ly (elts' x)) G
     where `{!CanSolve (elts !! i = Some ty)} :-
      x ← (l ◁ₗ{β} array ly elts) :>> (λ x : A, l ◁ₗ{β} array ly (elts' x)); return G x.
  Proof. move => ?. by rewrite list_insert_id. Qed.
  Definition subsume_array_insert_id_inst := [instance subsume_array_insert_id].
  Global Existing Instance subsume_array_insert_id_inst | 0.
End upstream.

(** * main definitions *)
Record fd_sched := {
    input_channels : list FD;
    sched_state : npfp_sched;
  }.

(* TODO: upstream *)
Notation array_p ly elts n :=
  (array ly (elts ++ replicate (n - length elts) (uninit ly)))
  (only parsing).

Program Definition fds_set_callback_func (fds : fd_sched)  (type prio : nat) :=
  {|
    input_channels := input_channels fds;
    sched_state := {|
                    callbacks := <[type := prio]> (callbacks (sched_state fds));
                    msg_qs := msg_qs (sched_state fds);
                  |}
  |}.
Next Obligation.
  move => [? [? ? ? ?]] type prio.
  by rewrite length_insert.
Qed.
Next Obligation.
  by move => [? [? ? ? ?]] _ _ .
Qed.

Definition fds_add_channel_func (fd_state : fd_sched) (fd : FD) :=
  {|
    input_channels := fd_state.(input_channels) ++ [fd];
    sched_state := fd_state.(sched_state)
  |}.

Section RecieveOneMessageSpecification.

  Context `{!PacketArrivals}.

   (** Given a packet ID, generate the message corresponding to that packet ID *)
  Definition generate_msg_corresponding_to_packetID (id : packet_ID) : message_data :=
    {| m_type := inhabitant; m_length := length (get_packet_data id); m_id := id|}.

  (** if pending packets is empty then add nothing to the scheduler else add
      the right message to the scheduler. *)
  Definition add_pending_msg_to_scheduler (t :nat)  (fd : FD) (sched_state : npfp_sched) : npfp_sched :=
    let ID := {|fd := fd; read_index := t|} in
    if (bool_decide (is_Some (packet_arrivals fd t))) then
      let msg := generate_msg_corresponding_to_packetID ID in
      npfp_enqueue_func sched_state msg
    else sched_state.

  Definition receive_one_message_func (t :nat) (fd :FD) (fd_state : fd_sched) : fd_sched :=
    {|
      input_channels := fd_state.(input_channels);
      sched_state := add_pending_msg_to_scheduler t fd fd_state.(sched_state);
    |}.

End RecieveOneMessageSpecification.

Section RecieveOneMessageProof.
  Context `{!PacketArrivals} `{!typeG Σ}.

  Global Instance simpl_and_npfp_enqueue_func fd_state msg1 msg2:
    SimplAndUnsafe (npfp_enqueue_func (sched_state fd_state) msg1 =
                    npfp_enqueue_func (sched_state fd_state) msg2) (msg1 = msg2) .
  Proof. by move => ->. Qed.

  Lemma packet_data_len pckt:
    length (get_packet_data pckt) ≤ max_int i32.
  Proof.
    rewrite /get_packet_data length_take.
    unfold_opaque max_msg_len; solve_goal.
  Qed.

  Lemma receive_one_message_no_pending t fd fd_state :
    packet_arrivals fd t = None →
    receive_one_message_func t fd fd_state = fd_state.
  Proof.
    rewrite /receive_one_message_func /add_pending_msg_to_scheduler => ->.
    by destruct fd_state.
  Qed.

  Lemma get_packet_data_no_pending fd t :
    packet_arrivals fd t = None →
    get_packet_data {| fd := fd; read_index := t |} = [].
  Proof. rewrite /get_packet_data => /= ->; solve_goal. Qed.

End RecieveOneMessageProof.

Section ReceiveMessagesSpecs.

  Context `{!PacketArrivals}.

  Fixpoint receive_n_messages_func (t : nat) (fd : FD) (fd_state :fd_sched) (n : nat) : fd_sched :=
    match n with
    | 0%nat => fd_state
    | S n' => let new_fd_state := receive_n_messages_func t fd fd_state n' in
              receive_one_message_func (t + n') fd new_fd_state
    end.

  Definition fd_has_at_least_n_msgs (fd : FD) (m : nat) (init : nat) : Prop :=
      ∀ i, (0 ≤ i < m)%nat -> is_Some (packet_arrivals fd (init + i)%nat).

  Definition fd_has_n_msgs (fd : FD) (m : nat) (init : nat) : Prop :=
    fd_has_at_least_n_msgs fd m init ∧
      ¬ is_Some (packet_arrivals fd (init + m)).

End ReceiveMessagesSpecs.

#[export] Hint Unfold add_pending_msg_to_scheduler receive_one_message_func : core.

Section RecieveMessagesProof.

  Context `{!PacketArrivals}.

  Lemma simpl_fd_has_msgs_0 (fd : FD) (init : nat) :
    fd_has_at_least_n_msgs fd 0 init.
  Proof. rewrite /fd_has_at_least_n_msgs; lia. Qed.

  Lemma simpl_fd_has_msgs_S (fd : FD) (i init : nat) :
    (fd_has_at_least_n_msgs fd i init ∧ is_Some (packet_arrivals fd (init + i)%nat)) → (fd_has_at_least_n_msgs fd (S i) init).
  Proof.
    intros [H1 H2].
    unfold fd_has_at_least_n_msgs.
    intros j.
    intros [Hlb Hub].
    destruct (decide (j = i)) as [-> | Hneq] => //.
    + apply H1; lia.
  Qed.

End RecieveMessagesProof.

#[export] Hint Resolve simpl_fd_has_msgs_0 simpl_fd_has_msgs_S : core.

Section CheckChannelsSpec.

  Context `{!PacketArrivals}.

  Fixpoint check_n_channels_func' (t : nat)  (fd_state : fd_sched) (fds : list Z) (ns : list nat) : fd_sched :=
    match fds, ns with
    | [], [] => fd_state
    | fd :: fds', n :: ns' =>
        let fd_state' := receive_n_messages_func t fd fd_state n in
        check_n_channels_func' (t + n + 1)%nat fd_state' fds' ns'
    | _, _ => fd_state
    end.

  Definition check_n_channels_func (t : nat) (fd_state : fd_sched) (n : nat)  (ns : list nat) :=
    let fds := take n (input_channels fd_state) in
    check_n_channels_func' t fd_state fds ns.

  (** `ns` is the number of messages on each fd; `init` is the initial read index *)
  Fixpoint fds_have_n_msgs (fds : list FD) (ns : list nat) (init : nat) : Prop :=
    match fds, ns with
    | [], [] => True
    | fd :: fds, n :: ns =>
        (* Since the code will execute an additional empty read, the next read index
           needs to be incremented by the number of messages read + 1 (empty read) *)
        fd_has_n_msgs fd n init ∧ fds_have_n_msgs fds ns (init + n + 1)%nat
    | _, _ => False
    end.

  (** Computes the number of calls made to read given that ns is a list of
      of number of read messages for each fd. Since the code reads until it
      hits an empty read, we need to add 1 for each fd; hence the `length ns` *)
  Definition num_reads_for_ns (ns : list nat) := (length ns + sum_list ns)%nat.

End CheckChannelsSpec.

Section CheckChannelsProofs.

  Context `{!PacketArrivals} `{!typeG Σ}.

  Lemma fds_have_n_msgs_next_fd fds fd ns n init :
    fds_have_n_msgs fds ns init →
    fd_has_n_msgs fd n (init + num_reads_for_ns ns) →
    fds_have_n_msgs (fds ++ [fd]) (ns ++ [n]) init.
  Proof.
    induction fds as [ | fd' fds IH] in ns, init |- *.
    - destruct ns => //=. by rewrite Nat.add_0_r.
    - intros Hfds Hfd.
      destruct ns as [ | n' ns] => //. split; first naive_solver.
      apply IH; first naive_solver.
      eapply eq_ind_r => //.
      rewrite /num_reads_for_ns => /=; lia.
  Qed.

  Global Instance simpl_num_reads_for_ns_nil ns :
    SimplAndRel (=) (num_reads_for_ns ns) 0%nat (ns = []).
  Proof. split; by [subst | destruct ns]. Qed.

  Global Instance simpl_num_reads_for_ns_cons ns ns' n :
    SimplAndUnsafe (num_reads_for_ns ns + (S n) = num_reads_for_ns ns')%nat
      (ns' = ns ++ [n]).
  Proof.
    move => ->. rewrite /num_reads_for_ns => //=.
    rewrite sum_list_with_app length_app => /=. lia.
  Qed.


  Lemma receive_n_messages_input_channels init fd fd_state n :
    input_channels (receive_n_messages_func init fd fd_state n) =
      input_channels fd_state.
  Proof. induction n in fd_state, init |- * => //=. Qed.

  Lemma check_channels_input_channels' init fd_state fds ns :
    input_channels (check_n_channels_func' init fd_state fds ns) =
      input_channels fd_state.
  Proof.
    induction fds in init, fd_state, ns |- *.
    - simpl. by destruct ns.
    - simpl. destruct ns => //.
      rewrite IHfds.
      by rewrite receive_n_messages_input_channels.
  Qed.

  Lemma check_channels_input_channels init fd_state n ns :
    input_channels (check_n_channels_func init fd_state n ns) =
      input_channels fd_state.
  Proof.
    rewrite /check_n_channels_func.
    by rewrite check_channels_input_channels'.
  Qed.

  Lemma fd_has_n_msgs_implies_no_pending fd n init :
    fd_has_n_msgs fd n init →
    packet_arrivals fd (init + n)%nat = None.
  Proof.
    move  => [_ Hnone].
    by apply eq_None_not_Some.
  Qed.

  Lemma check_n_channels_S' init fd_state n fds fd ns :
    length ns = length fds →
    check_n_channels_func' init fd_state (fds ++ [fd]) (ns ++ [n]) =
      receive_n_messages_func (init + num_reads_for_ns ns) fd (check_n_channels_func' init fd_state fds ns) n.
  Proof.
    induction fds in n, fd, init, fd_state, ns |- *.
    - destruct ns => //= _.
      rewrite (proj1 (simpl_num_reads_for_ns_nil [])); f_equal; lia.
    - destruct ns as [ | n' ns'] => //= Hlen.
      rewrite IHfds; last lia.
      f_equal.
      unfold_opaque num_reads_for_ns => /=; lia.
  Qed.

  Lemma fds_have_n_msgs_same_len fds ns init :
    fds_have_n_msgs fds ns init →
    length ns = length fds.
  Proof.
    induction fds in ns, init |- *.
    - by destruct ns.
    - destruct ns => //=.
      by intros [_ ->%IHfds].
  Qed.

  Lemma check_n_channels_S i init fd_state n fd ns :
    fds_have_n_msgs (take i (input_channels fd_state)) ns init →
    input_channels fd_state !! i = Some fd →
    check_n_channels_func init fd_state (i + 1)%nat (ns ++ [n]) =
      receive_n_messages_func (init + num_reads_for_ns ns) fd (check_n_channels_func init fd_state i ns) n.
  Proof.
    intros ?%fds_have_n_msgs_same_len ?.
    rewrite /check_n_channels_func .
    rewrite Nat.add_1_r.
    erewrite take_S_r => //.
    rewrite check_n_channels_S' => //.
  Qed.

  Lemma Exists_last_false {A} P l (x : A) :
    ¬ (P x) →
    Exists P l ↔ Exists P (l ++ [x]).
  Proof.
    intros HPx. split => HP.
    - apply Exists_app; by left.
    - apply Exists_app in HP as [ | [ | ?%Exists_nil]%Exists_inv] => //.
  Qed.

End CheckChannelsProofs.

Global Opaque num_reads_for_ns.

Section CheckUntilEmptySpecs.

  Context `{!PacketArrivals}.

  Fixpoint check_channels_until_empty_func (t : nat) (fd_state : fd_sched) (ns_list : list (list nat)) : fd_sched :=
    match ns_list with
    | [] => fd_state
    | ns :: ns_list' =>
        let fd_state' := check_n_channels_func t fd_state (length (input_channels fd_state)) ns in
        check_channels_until_empty_func (t + num_reads_for_ns ns) fd_state' ns_list'
    end.

  Definition num_reads_for_ns_list (ns : list (list nat)) : nat :=
    (sum_list (map num_reads_for_ns ns))%nat.

  (* ns_list has the number of read messages on each descriptor (ns) for every call to check_channels *)
  (* this predicate assumes that all the calls to check_channels didn't fail - i.e. there was one successful read on some descriptor. check the definition below for the failed case *)
  Fixpoint fds_have_ns_list_msgs (fds : list FD) (ns_list : list (list nat)) (init : nat) : Prop :=
    match ns_list with
    | [] => True
    | ns :: ns_list' => Exists (λ n, (n <> 0)%nat) ns ∧ (* this holds because of the assumption that check_channels hasn't failed yet *)
                        fds_have_n_msgs fds ns init ∧
                        fds_have_ns_list_msgs fds ns_list' (init + num_reads_for_ns ns)
    end.

  (* there will be as many "ns" as the # of calls to `check_channels` *)
  (* this predicate assumes that the last call to `check_channels` failed to find any msgs *)
  (* assuming that `check_channes` was called at least once *)
  Definition fds_have_ns_list_msgs_done (fds : list FD) (ns_list : list (list nat)) (init : nat) : Prop :=
    let ns_list' := (take (length ns_list - 1)%nat ns_list) in
    fds_have_ns_list_msgs fds ns_list' init ∧
    match last ns_list with
    | None => False (* it should never be None *)
    | Some ns => fds_have_n_msgs fds ns (init + num_reads_for_ns_list ns_list')%nat ∧ Forall (λ n, (n = 0)%nat) ns
    end.

End CheckUntilEmptySpecs.

Section CheckUntilEmptyProofs.

  Context `{!PacketArrivals}.

  Lemma num_reads_for_ns_list_nil :
    num_reads_for_ns_list [] = 0%nat.
  Proof. done. Qed.

  Lemma num_reads_for_ns_list_cons ns ns_list :
    num_reads_for_ns_list (ns :: ns_list) = (num_reads_for_ns ns + num_reads_for_ns_list ns_list)%nat.
  Proof. done. Qed.

  (* Hint Rewrite @num_reads_for_ns_list_nil @num_reads_for_ns_list_cons. *)

  Global Instance simpl_and_rel_num_reads_init (t : nat) (ns : list nat) (ns_list : list (list nat)) :
    SimplAndUnsafe (t + num_reads_for_ns ns = t + num_reads_for_ns_list ns_list)%nat (ns_list = [ns]).
  Proof. intros ->. auto. Qed.

  Global Instance simpl_and_rel_num_reads_cons (ns : list nat) (ns_list ns_list' : list (list nat)) :
    SimplAndUnsafe (num_reads_for_ns_list ns_list + num_reads_for_ns ns = num_reads_for_ns_list ns_list')%nat (ns_list' = ns_list ++ [ns]).
  Proof.
    intros ->. rewrite /num_reads_for_ns_list => /=.
    rewrite map_app; simpl; rewrite sum_list_with_app => /=; lia.
  Qed.

  Lemma check_channels_until_empty_input_channels init fd_state ns_list :
    input_channels (check_channels_until_empty_func init fd_state ns_list) =
      input_channels fd_state.
  Proof.
    induction ns_list as [ | ???IH] in init, fd_state |- * => //=.
    rewrite IH.
    by rewrite check_channels_input_channels.
  Qed.

  Lemma fds_have_ns_list_msgs_next_loop fds ns_list ns init :
    fds_have_ns_list_msgs fds ns_list init →
    fds_have_n_msgs fds ns (init + num_reads_for_ns_list ns_list) →
    Exists (λ n : nat, n ≠ 0%nat) ns →
    fds_have_ns_list_msgs fds (ns_list ++ [ns]) init.
  Proof.
    induction ns_list as [ | ns' ns_list' IHns ] in init |- *.
    - simpl. rewrite /num_reads_for_ns_list Nat.add_0_r => /= _?? //.
    - simpl. intros [Hnon_empty_ns' [Hns' Hns_list']].
      rewrite /num_reads_for_ns_list => /=.
      intros Hns Hnon_empty_ns.
      split => //.
      split => //.
      apply IHns => //.
      rewrite /num_reads_for_ns_list. by rewrite -Nat.add_assoc.
  Qed.

  Lemma check_channels_until_empty_next init fd_state ns ns_list :
    fds_have_ns_list_msgs (input_channels fd_state) ns_list init →
    fds_have_n_msgs (input_channels fd_state) ns (init + num_reads_for_ns_list ns_list) →
    check_channels_until_empty_func init fd_state (ns_list ++ [ns]) =
      check_n_channels_func (init + num_reads_for_ns_list ns_list) (check_channels_until_empty_func init fd_state ns_list) (length (input_channels fd_state)) ns.
  Proof.
    induction ns_list as [ | ns' ns_list' IHns ] in init,fd_state |- *.
    - rewrite /num_reads_for_ns_list => /= ??; f_equal; lia.
    - intros Hns_list Hns.
      rewrite -app_comm_cons.
      cbn [check_channels_until_empty_func].
      rewrite IHns.
      all: rewrite ?check_channels_input_channels ?check_channels_until_empty_input_channels.
      + f_equal; first by rewrite -Nat.add_assoc.
      + naive_solver.
      + rewrite /num_reads_for_ns_list in Hns. simpl in Hns.
        by rewrite -Nat.add_assoc.
  Qed.

  Lemma fds_have_ns_list_msgs_done_base_run (ns : list nat) fd_state init:
    ¬ Exists (λ n : nat, n ≠ 0%nat) ns →
    fds_have_n_msgs (input_channels fd_state) ns init →
    fds_have_ns_list_msgs_done (input_channels fd_state) [ns] init.
  Proof.
    intros ??. split => //. rewrite last_singleton => /=.
    split.
    - by rewrite num_reads_for_ns_list_nil Nat.add_0_r.
    - apply not_Exists_Forall in H0; last solve_decision.
      eapply Forall_impl => // x /=; lia.
  Qed.

  Lemma fds_have_ns_list_msgs_done_next_run (ns : list nat) ns_list fd_state init:
    ¬ Exists (λ n : nat, n ≠ 0%nat) ns →
    fds_have_ns_list_msgs (input_channels fd_state) ns_list init →
    fds_have_n_msgs (input_channels fd_state) ns (init + num_reads_for_ns_list ns_list) →
    fds_have_ns_list_msgs_done (input_channels fd_state) (ns_list ++ [ns]) init.
  Proof.
    intros ???. split => //.
    { rewrite take_app_length' => //. rewrite length_app => /=; lia. }
    rewrite last_snoc. split.
    - rewrite take_app_length' => //. rewrite length_app => /=; lia.
    - apply not_Exists_Forall in H0; last solve_decision.
      eapply Forall_impl => // x /=; lia.
  Qed.

End CheckUntilEmptyProofs.

Ltac simplify_channels :=
  repeat
    match goal with
    | Hchannels : context G [input_channels (check_n_channels_func _ _ _ _)] |- _ =>
        rewrite check_channels_input_channels in Hchannels
    | Hchannels : context G [input_channels (check_channels_until_empty_func _ _ _)] |- _ => rewrite check_channels_until_empty_input_channels in Hchannels end;
  rewrite ?check_channels_input_channels ?check_channels_until_empty_input_channels.

Ltac clear_cases :=
  repeat match goal with
         | H : ?T |- _ =>
           (* Keep current location and case distinction info. *)
           lazymatch T with
           | CURRENT_LOCATION _ _ => idtac
           | CASE_DISTINCTION_INFO _ _ => idtac
           | _ => fail
           end;
           clear H
         end.

Section error_num.

  Context `{!typeG Σ}.

  Definition FindErrNo :=
    {| fic_A := Z; fic_Prop n := @is_errno Σ n; |}.
  Lemma find_in_context_err_no `{!typeG Σ} T:
    (∃ n, is_errno n ∗ T n) ⊢ find_in_context (FindErrNo) T.
  Proof. iIntros "(% & H)". iExists n. by iFrame. Qed.
  Definition find_in_context_err_no_inst :=
    [instance find_in_context_err_no with FICSyntactic].
  Global Existing Instance find_in_context_err_no_inst | 1.
  Global Instance related_to_err_no A n' : RelatedTo (λ x : A, is_errno (n' x)) := {| rt_fic := FindErrNo |}.

  Lemma subsume_is_errno A n n' G :
    subsume (@is_errno Σ n) (λ x : A, is_errno (n' x)) G :-
      ∃ x, exhale ⌜ n = n' x⌝; return (G x).
  Proof. iIntros "(%x & -> & ?) ?". iExists x. iFrame. Qed.
  Definition subsume_is_errno_inst := [instance subsume_is_errno].
  Global Existing Instance subsume_is_errno_inst.

End error_num.
