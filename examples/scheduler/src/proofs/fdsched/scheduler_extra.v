From caesium Require Import builtins_specs.
From refinedc.examples.scheduler.src.fdsched Require Import message_extra.
From refinedc.examples.scheduler.src.fdsched Require Import priority_extra.
From refinedc.typing Require Import typing.

Definition create_bitmap (qs : list (list (message_data))) : list bool :=
  (λ data, bool_decide (data ≠ [])) <$> qs.
Global Typeclasses Opaque create_bitmap.

#[projections(primitive)]
Record npfp_sched := {
  callbacks : list nat;
  msg_qs : list (list message_data);
  callbacks_bounded : length callbacks = Z.to_nat num_msg_types;
  msg_qs_bounded : length msg_qs = Z.to_nat num_priorities;
  }.

Program Definition initialize_scheduler  :=
  {|
    callbacks := replicate (Z.to_nat num_msg_types) 0%nat;
    msg_qs := replicate(Z.to_nat num_priorities) [];
  |}.
Next Obligation.
  solve_goal.
Qed.
Next Obligation.
  solve_goal.
Qed.

Lemma create_bitmap_length sched_state :
  length (create_bitmap (msg_qs sched_state)) = Z.to_nat num_priorities.
Proof. by rewrite -(msg_qs_bounded sched_state) /create_bitmap; apply length_fmap. Qed.

#[export] Hint Rewrite msg_qs_bounded : lithium_rewrite.
#[export] Hint Rewrite callbacks_bounded : lithium_rewrite.
#[export] Hint Rewrite create_bitmap_length : lithium_rewrite.

(** Add message to the queue corresponding to the right priority level *)
Definition add_msg_to_q (qs :list (list message_data)) (prio : nat)
  (msg : message_data) : list (list message_data) :=
  let q := default [] (qs !! prio) in
  let newq := q ++ [msg] in
  <[prio := newq]> qs.

(** Update the state of the scheduler by adding the message to the right queue. *)
Program Definition add_msg_to_scheduler (sched_state : npfp_sched) (msg : message_data) (prio : nat):= {|
  callbacks := callbacks sched_state;
  msg_qs := (add_msg_to_q (msg_qs sched_state) prio msg);
  callbacks_bounded := callbacks_bounded sched_state;
|}.
Next Obligation.
  move => sched_state ??. rewrite -(msg_qs_bounded sched_state). apply length_insert.
Qed.

(** Function to look up the priority for a given message type *)
(* Returns a very low priority if the message type does not have a priority assigned to it. *)
Definition get_priority (sched_state : npfp_sched) (msg : message_data) : nat :=
  let msg_type := (m_type msg) in
  default (Z.to_nat num_priorities - 1)%nat ((callbacks sched_state) !! msg_type).

(** Gallina equivalent of the [npfp_enqueue] function *)
Definition npfp_enqueue_func (sched_state : npfp_sched) (msg : message_data) : npfp_sched :=
  let new_msg := update_msg_type msg in
  let prio := get_priority sched_state new_msg in
  add_msg_to_scheduler sched_state new_msg prio.

(** DEQUEUE-------------------------------------------------------------------------------*)

(** Functions for dequeueing from the scheduler *)
(* TODO: change find_highest_prio to return an option *)
Definition get_highest_prio_level (sched_state : npfp_sched) : option nat :=
  let prio := find_highest_prio (create_bitmap (msg_qs sched_state)) in
  if bool_decide (0 ≤ prio) then Some (Z.to_nat prio) else None.

(** if this returns None then all queues are empty *)
Definition get_highest_prio_queue (sched_state : npfp_sched) : list message_data :=
  let prio := get_highest_prio_level sched_state in
  match prio with
  | None => []
  | Some l => msg_qs sched_state !!! l
  end.

Definition get_highest_prio_msg (sched_state : npfp_sched) : option message_data :=
  head (get_highest_prio_queue sched_state).

Definition dequeue_from_given_level_queue (sched_state : npfp_sched) (level : nat)
  : list (list message_data) :=
  let q := msg_qs sched_state !!! level in
  let newq := tail q in
  <[level:=newq]> (msg_qs sched_state).

Program Definition dequeue_from_given_level_sched (sched_state : npfp_sched) (level : nat) :=
  let newqs := dequeue_from_given_level_queue sched_state level in
  {|
    callbacks := callbacks sched_state;
    msg_qs := newqs;
    callbacks_bounded := callbacks_bounded sched_state;
  |}.
Next Obligation. solve_goal. Qed.

Definition npfp_dequeue_func (sched_state : npfp_sched) : npfp_sched :=
  let check := bool_decide ((find_highest_prio (create_bitmap (msg_qs sched_state)) < 0)) in
  if check then sched_state else
    let level := get_highest_prio_level sched_state in
    match level with
    | None => sched_state
    | Some k => dequeue_from_given_level_sched sched_state k
    end.

(** Some helpful lemmas *)

Lemma npfp_enqueue_add_msg_to_q1 qs a msg b:
  b = a →
  list_subequiv [b] qs (add_msg_to_q qs a msg).
Proof.
  move => ->.
  rewrite /add_msg_to_q -list_subequiv_insert_in_l; last by rewrite elem_of_list_singleton //=.
  naive_solver.
Qed.

Lemma npfp_enqueue_create_bitmap_addmsg prio qs msg i:
  prio = i →
  list_subequiv [i] (create_bitmap qs)
    (create_bitmap (add_msg_to_q qs prio msg)).
Proof.
  move => ->.
  apply list_subequiv_fmap.
  by apply npfp_enqueue_add_msg_to_q1.
Qed.

Lemma npfp_enqueue_create_bitmap_addmsg2 qs prio msg i :
  i = prio →
  (prio < length qs)%nat →
  create_bitmap (add_msg_to_q qs prio msg) !! i = Some true.
Proof.
  move => -> ?. rewrite /create_bitmap/add_msg_to_q.
  apply list_lookup_fmap_Some. rewrite list_lookup_insert //. eexists _. split; [done|].
  by rewrite bool_decide_true// => /app_eq_nil [??].
Qed.

Lemma find_highest_prio_length q :
  find_highest_prio q < length q.
Proof.
  rewrite /find_highest_prio.
  case_match eqn: Heq; last by solve_goal.
  move: Heq => /list_find_Some' [/(@lookup_lt_Some _ _ _ _ ) A B].
  lia.
Qed.

Lemma npfp_dequeue_nonempty sched_state y :
  ¬ find_highest_prio (create_bitmap (msg_qs sched_state)) < 0 →
  msg_qs sched_state !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some y →
  y ≠ [].
Proof.
  move => Hnle0 Hselect.
  rewrite /find_highest_prio in Hnle0.
  case_match eqn: Heq; last by naive_solver.
  rewrite /find_highest_prio Heq in Hselect.
  move : Heq => /list_find_Some' [EQ1 [EQ2 _]].
  rewrite list_lookup_fmap in EQ1.
  rewrite Nat2Z.id in Hselect.
  rewrite Hselect EQ2 in EQ1.
  naive_solver.
Qed.

Lemma find_highest_prio_bounded sched_state:
  find_highest_prio (create_bitmap (msg_qs sched_state)) ≤ max_int u8.
Proof.
  apply Zlt_succ_le.
  apply Z.lt_le_trans with (length (create_bitmap (msg_qs sched_state)));
    first by apply (find_highest_prio_length _).
  rewrite create_bitmap_length.
  naive_solver.
Qed.

Lemma get_highest_prio_msg_is_head sched_state y :
  ¬ find_highest_prio (create_bitmap (msg_qs sched_state)) < 0 →
  msg_qs sched_state !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some y →
  head y = get_highest_prio_msg sched_state.
Proof.
  move => Hle0 Hlookup.
  rewrite /get_highest_prio_msg /get_highest_prio_queue /get_highest_prio_level.
  case (find_highest_prio (create_bitmap (msg_qs sched_state))) eqn: EQ; try solve_goal;
   rewrite /= list_lookup_total_alt Hlookup; try done.
Qed.

Lemma npfp_dequeue_no_highest_priority sched_state y :
  msg_qs sched_state !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some y →
  ¬ find_highest_prio (create_bitmap (msg_qs sched_state)) < 0 →
  list_subequiv [Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state)))]
    (msg_qs sched_state)
    (msg_qs (npfp_dequeue_func sched_state)).
Proof.
  move => Hsome Hle0.
  rewrite /npfp_dequeue_func.
  rewrite -bool_decide_eq_false in Hle0.
  rewrite Hle0 /get_highest_prio_level.
  case (find_highest_prio (create_bitmap (msg_qs sched_state))) eqn: EQ; last by naive_solver.
  all : rewrite /dequeue_from_given_level_sched; simpl; rewrite /dequeue_from_given_level_queue; apply list_subequiv_insert_in_r; try done; solve_goal.
Qed.

Lemma npfp_dequeue_has_highest_pending_prio sched_state y y0 :
  ¬ find_highest_prio (create_bitmap (msg_qs sched_state)) < 0 →
  msg_qs sched_state !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some y →
  msg_qs (npfp_dequeue_func sched_state) !!
    Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some y0 →
  tail y = y0.
Proof.
  move => Hnle0 Hbefore Hafter.
  rewrite /npfp_dequeue_func in Hafter.
  rewrite -bool_decide_eq_false in Hnle0.
  rewrite Hnle0 in Hafter.
  rewrite /get_highest_prio_level in Hafter.
  case (find_highest_prio (create_bitmap (msg_qs sched_state))) eqn: EQ; try solve_goal;
    rewrite /dequeue_from_given_level_queue /dequeue_from_given_level_sched in Hafter; simpl in Hafter; rewrite /dequeue_from_given_level_queue list_lookup_total_alt Hbefore in Hafter;
    apply list_lookup_insert_Some in Hafter.
  - by move : Hafter => [[A [C D]] | B]; last by solve_goal.
  - by move : Hafter => [[A [C D]] | B]; last by solve_goal.
Qed.

Lemma npfp_dequeue_qs_equiv sched_state :
  list_subequiv [Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state)))]
    (msg_qs sched_state)
    (msg_qs (npfp_dequeue_func sched_state)).
Proof.
  rewrite /npfp_dequeue_func.
  case (find_highest_prio (create_bitmap (msg_qs sched_state))) eqn: EQ; try solve_goal;
    rewrite /get_highest_prio_level EQ /dequeue_from_given_level_sched /dequeue_from_given_level_queue;apply list_subequiv_insert_in_r; solve_goal.
Qed.

Lemma npfp_dequeue_create_bitmap_equiv sched_state :
  list_subequiv [Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state)))]
    (create_bitmap (msg_qs sched_state))
    (create_bitmap (msg_qs (npfp_dequeue_func sched_state))).
Proof. rewrite /create_bitmap. apply list_subequiv_fmap. apply npfp_dequeue_qs_equiv. Qed.

Lemma npfp_dequeue_create_bitmap_equiv1 sched_state y :
  ¬ find_highest_prio (create_bitmap (msg_qs sched_state)) < 0 →
  msg_qs sched_state !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some y →
  tail y ≠ [] →
  create_bitmap (msg_qs sched_state) = create_bitmap (msg_qs (npfp_dequeue_func sched_state)).
Proof.
  move => Hnle0 Hsome Hneq.
  rewrite /create_bitmap /npfp_dequeue_func.
  rewrite -bool_decide_eq_false in Hnle0.
  rewrite Hnle0.
  rewrite /get_highest_prio_level.
  case (find_highest_prio (create_bitmap (msg_qs sched_state))) eqn: EQ; try solve_goal;
    rewrite /get_highest_prio_level /dequeue_from_given_level_sched; simpl; rewrite
                                                                              /dequeue_from_given_level_queue list_lookup_total_alt Hsome list_fmap_insert.
  * destruct (decide (tail y ≠ [])); last by solve_goal.
    symmetry.
    apply list_insert_id' => Hle.
    rewrite list_lookup_fmap Hsome.
    solve_goal.
  * destruct (decide (tail y ≠ [])); last by solve_goal.
    symmetry.
    apply list_insert_id' => Hle.
    rewrite list_lookup_fmap Hsome.
    solve_goal.
Qed.

Lemma npfp_dequeue_create_bitmap_false sched_state y :
  ¬ find_highest_prio (create_bitmap (msg_qs sched_state)) < 0 →
  msg_qs sched_state !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some y →
  find_highest_prio (create_bitmap (msg_qs sched_state)) < num_priorities →
  tail y = [] →
  create_bitmap (msg_qs (npfp_dequeue_func sched_state))
  !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state))) = Some false.
Proof.
  move => ?? ? Htail. apply list_lookup_fmap_Some. eexists [].
  split; [|solve_goal]. rewrite -Htail.
  destruct (msg_qs (npfp_dequeue_func sched_state) !! Z.to_nat (find_highest_prio (create_bitmap (msg_qs sched_state)))) eqn: Heq.
  - f_equal. symmetry. by eapply npfp_dequeue_has_highest_pending_prio.
  - move: Heq => /lookup_ge_None. solve_goal.
Qed.
