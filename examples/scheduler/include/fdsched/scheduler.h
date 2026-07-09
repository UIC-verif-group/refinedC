#pragma once

#include "fdsched/message.h"
#include "fdsched/priority.h"

//@rc::import scheduler_extra from refinedc.examples.scheduler.src.fdsched

typedef int (*callback_fn_t)(struct message *);

struct [[rc::refined_by("priority : nat")]]
       [[rc::typedef("callback_t : ...")]]
       [[rc::constraints("{0 <= priority < 256}")]] callback {
  [[rc::field("priority @int<u8>")]]
  priority_t prio;
  [[rc::field("function_ptr<{"
  "fn(∀ (msg, q) : message_data * loc;"
  "(&own (msg @ (message (uninit (void*))))); True) →"
  "∃ () : (), (int (i32));"
  "True"
  "}>")]]
  callback_fn_t f;
};

/* state of the non-preemptive fixed-priority scheduler */
typedef struct [[rc::refined_by("npfp_scheduler : npfp_sched")]]
               [[rc::typedef("npfp_t : ...")]]
npfp_scheduler {
  /* the registered callbacks */
  [[rc::field("array<struct_callback, {callbacks npfp_scheduler `at_type` callback_t}>")]]
  struct callback callbacks[NUM_MESSAGE_TYPES];

  /* pending callback activations */
  [[rc::field("array<struct_message_queue, {msg_qs npfp_scheduler `at_type`  message_queue}>")]]
  struct message_queue pending[NUM_PRIORITIES];

  /* which priority levels are non-empty? */
  [[rc::field("{create_bitmap (msg_qs npfp_scheduler)} @ prio_bitmap_t")]]
  prio_bitmap_t prio_levels;
} npfp;



[[rc::parameters("m_len : Z", "l1 : loc", "l2 : loc", "sched_state : npfp_sched", "id : packet_ID")]]
[[rc::args("l1 @ &own<sched_state @ npfp_t>", "l2 @ &own<malloced<{ly_size struct_message}, struct<struct_message,"
	   "uninit<u8>,"
	   "m_len @ int<u64>,"
	   "uninit<void*>,"
	   "array_p<u8,{get_packet_data id `at_type` (int u8)},"
	      "{Z.to_nat max_msg_len}>>>>")]]
[[rc::ensures("own l1 : {let msg := {|m_type := (message_identify_type_coq id);"
	      "m_length := m_len;"
	      "m_id := id|} in"
	      " npfp_enqueue_func sched_state msg} @ npfp_t")]]
[[rc::tactics("by apply msg_type_bounded.")]]
[[rc::tactics("apply npfp_enqueue_add_msg_to_q1. by rewrite /get_priority/update_msg_type/set_msg_type /=; simplify_option_eq.")]]
[[rc::tactics("rewrite /update_msg_type /set_msg_type /get_priority/add_msg_to_q/=. simplify_option_eq. symmetry. eapply list_lookup_total_insert_eq; solve_goal.")]]
[[rc::tactics("eapply npfp_enqueue_create_bitmap_addmsg. by rewrite /get_priority/update_msg_type/set_msg_type/=; simplify_option_eq.")]]
[[rc::tactics("apply npfp_enqueue_create_bitmap_addmsg2; unfold get_priority in *; simplify_option_eq; solve_goal.")]]
static inline
void npfp_enqueue(struct npfp_scheduler *sched, struct message* msg) {
  /* identify the type of message we're looking at */
  msg->type = message_identify_type(msg);
  /* look up the fixed priority of such messages */
  priority_t msg_prio = sched->callbacks[msg->type].prio;
  /* add it to the appropriate queue */
  message_queue_add(&sched->pending[msg_prio], msg);
  /* note that the queue isn't empty anymore */
  priority_level_set(&sched->prio_levels, msg_prio);
}

[[rc::parameters("l1 : loc", "sched_state : npfp_sched")]]
[[rc::args("l1 @ &own<sched_state @ npfp_t>")]]
[[rc::ensures("own l1 : {npfp_dequeue_func sched_state} @ npfp_t")]]
[[rc::returns("{get_highest_prio_msg sched_state} @ optionalO<λ msg. &own<malloced<{ly_size struct_message}, msg @ message<uninit<void*>>>>>")]]
[[rc::tactics("all : try (rewrite /npfp_dequeue_func; solve_goal).")]]
[[rc::tactics("rewrite /get_highest_prio_msg /get_highest_prio_queue /get_highest_prio_level; solve_goal.")]]
[[rc::tactics("rewrite -(Z2Nat.id num_priorities); try solve_goal."
	            " by rewrite -(create_bitmap_length sched_state); apply find_highest_prio_length.")]]
[[rc::tactics("by eapply npfp_dequeue_nonempty.")]]
[[rc::tactics("by apply get_highest_prio_msg_is_head.")]]
[[rc::tactics("by eapply npfp_dequeue_no_highest_priority.")]]
[[rc::tactics("eapply npfp_dequeue_has_highest_pending_prio; [done..|solve_goal].")]]
[[rc::tactics("by eapply npfp_dequeue_create_bitmap_equiv.")]]
[[rc::tactics("eapply npfp_dequeue_create_bitmap_false; solve_goal.")]]
[[rc::tactics("by apply get_highest_prio_msg_is_head.")]]
[[rc::tactics("by apply npfp_dequeue_qs_equiv.")]]
[[rc::tactics("eapply npfp_dequeue_has_highest_pending_prio; [done..|solve_goal].")]]
[[rc::tactics("by eapply npfp_dequeue_create_bitmap_equiv1.")]]
static inline
struct message* npfp_dequeue(struct npfp_scheduler *sched) {
  /* figure out top pending priority level */
  int top_prio = highest_pending_priority(&sched->prio_levels);
  if (priority_search_none_found(top_prio))
    return NULL;
  else {
    /* dequeue the highest-priority message */
    struct message *msg = message_queue_remove(&sched->pending[top_prio]);

    /* check if we have to clear the priority bit */
    if (message_queue_empty(&sched->pending[top_prio])) {
      /* note that the queue is now empty */
      priority_level_clear(&sched->prio_levels, top_prio);
    }

    return msg;
  }
}

static inline
int npfp_dispatch(struct npfp_scheduler *sched, struct message *msg) {
  return sched->callbacks[msg->type].f(msg);
}
