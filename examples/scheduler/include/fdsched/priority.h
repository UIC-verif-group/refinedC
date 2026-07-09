#pragma once

#include <assert.h>
#include <stdint.h>
#include <stddef.h>

#if defined (__refinedc__)
#include "refinedc_builtins_specs.h"
#endif

/* let's support 256 priorities, with 0 being the highest priority */
typedef uint8_t priority_t;
#define NUM_PRIORITIES (UINT8_MAX + 1)

//@rc::import priority_extra from refinedc.examples.scheduler.src.fdsched

typedef struct
[[rc::refined_by("bitmap : {list bool}")]]
[[rc::typedef("prio_bitmap_t : ...")]]
[[rc::constraints("{length bitmap = Z.to_nat num_priorities}")]]
prio_bitmap
/* a bitmap of "non-empty queue" indicators */
{
  [[rc::field("array<u64, {encode_prio_bitmap bitmap `at_type` int u64}>")]]
  uint64_t bits[4];
} prio_bitmap_t;

typedef int priority_search_t;

/* initialize the bitmap to all empty */
[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<struct_prio_bitmap>>")]]
[[rc::ensures("own p : {replicate (Z.to_nat num_priorities) false} @ prio_bitmap_t")]]
[[rc::tactics("by apply list_subequiv_split; solve_goal.")]]
[[rc::tactics("by have -> : i = 4%nat by [lia].")]]
static inline
void prio_level_init(prio_bitmap_t *bm) {
  [[rc::exists("i : nat")]]
  [[rc::inv_vars("lvl : i @ int<i32>")]]
  [[rc::inv_vars("bm : p @ &own<struct<struct_prio_bitmap,"
		 "array_p<u64, {replicate i 0 `at_type` int u64}, {4%nat}>>>")]]
  [[rc::constraints("{0 <= i <= 4}")]]
  for(int lvl = 0; lvl < 4; lvl += 1) {
    bm->bits[lvl] = 0;
  }
}

/* find the maximum priority level with pending work, or return -1 */
[[rc::parameters("p : loc", "bm : {list bool}")]]
[[rc::args("p @ &own<bm @ prio_bitmap_t>")]]
[[rc::requires("{length bm = Z.to_nat num_priorities}")]]
[[rc::returns("{find_highest_prio bm} @ int<i32>")]]
[[rc::ensures("own p : bm @ prio_bitmap_t")]]
[[rc::tactics("have := Z_least_significant_one_lower_bound y. solve_goal.")]]
[[rc::tactics("have := encode_prio_bitmap_least_significant_one_bound bm lvl y. solve_goal.")]]
[[rc::tactics("rewrite (highest_pending_priority_found _ y lvl); solve_goal.")]]
[[rc::tactics("apply (highest_pending_priority_not_in_element _ lvl y); solve_goal.")]]
[[rc::tactics("symmetry; apply (highest_pending_priority_not_found _ lvl); solve_goal.")]]
static inline
priority_search_t highest_pending_priority(prio_bitmap_t *bm) {
  int offset = -1;
  [[rc::exists("lvl : Z")]]
  [[rc::inv_vars("i : lvl @ int<i32>")]]
  [[rc::constraints("{0 <= lvl <= 4}")]]
  [[rc::inv_vars("offset : {lvl * 64 - 1} @ int<i32>")]]
  [[rc::constraints("{forall (j : Z), 0 <= j < lvl * 64 -> bm !! (Z.to_nat j) = Some false}")]]
  //bits up to offset are always false
  for (int i = 0; i < 4; i++) {
    int first_bit = __builtin_ffsll(bm->bits[i]);
    if (first_bit) {
      return first_bit + offset;
    } else {
      offset += 64;
    }
  }
  return -1;
}

/* predicate: did we find a non-empty priority level? */
[[rc::parameters("res : Z")]]
[[rc::args("res @ int<i32>")]]
[[rc::returns("{bool_decide (res < 0)} @ boolean<i32>")]]
static inline
int priority_search_none_found(priority_search_t result) {
  return result < 0;
}

/* set the bit corresponding to the given priority */
[[rc::parameters("p : loc", "priority : Z", "bm : {list bool}")]]
[[rc::args("p @ &own<bm @ prio_bitmap_t>", "priority @ int<u8>")]]
[[rc::ensures("own p : {<[Z.to_nat priority := true]> bm} @ prio_bitmap_t")]]
[[rc::requires("{priority < num_priorities}", "{0 <= priority}")]]
[[rc::tactics("by apply Z_shiftl_1_range; solve_goal.")]]
[[rc::tactics("to_div_mod. by apply priority_level_set_clear_rest.")]]
[[rc::tactics("to_div_mod. by eapply priority_level_set_changed.")]]
static inline
void priority_level_set(prio_bitmap_t *bm, priority_t prio) {
  uint8_t word = prio / 64;
  uint8_t bit  = prio % 64;
  bm->bits[word] |= (((uint64_t) 1) << bit);
}

/* clear the bit corresponding to the given priority */
[[rc::parameters("p : loc","priority : Z","bm : {list bool}")]]
[[rc::args("p @ &own<bm  @ prio_bitmap_t>","priority @ int<u8>")]]
[[rc::ensures("own p : {<[Z.to_nat priority := false]> bm} @ prio_bitmap_t")]]
[[rc::requires("{priority < num_priorities}", "{0 <= priority}")]]
[[rc::tactics("by apply Z_shiftl_1_range; solve_goal.")]]
[[rc::tactics("to_div_mod. by apply priority_level_set_clear_rest.")]]
[[rc::tactics("to_div_mod. by eapply priority_level_clear_changed.")]]
static inline
void priority_level_clear(prio_bitmap_t *bm, priority_t prio) {
  uint8_t word = prio / 64;
  uint8_t bit  = prio % 64;
  bm->bits[word] &= ~(((uint64_t) 1) << bit);
}
