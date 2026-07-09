#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

//@rc::import binary_search_defs from refinedc.tutorial.t00_intro

/**
   Welcome to the tutorial of RefinedC!

   In this tutorial you will learn to use the RefinedC framework for
   verifying C programs.

   The tutorial starts in [t1_basic.c].

   Below is an example how a binary search function can be verified in
   RefinedC. The [rc::...] attributes (using modern C syntax) are
   annotations for RefinedC. You don't need to understand all
   annotations immediately. At a high level, the annotations say that
   if [binary_search] is called with a sorted list (see the
   precondition in [rc::requires]), it returns the index of the
   element if it appears it in the list and otherwise -1.

   The annotations on the function itself except [rc::lemmas] give the
   specification, while the annotations inside the body of the
   function give the loop invariant. Given the invariant, RefinedC
   reduces verification of the function to sideconditions about the
   [must_be_in_range] predicate that are proved using the lemmas
   listed in [rc::lemmas] (see [binary_search_defs.v]).
*/

[[rc::parameters("ls : {list Z}", "x : Z", "p : loc")]]
[[rc::args("p @ &own<array<i32, {ls `at_type` int i32}>>", "{length ls} @ int<i32>", "x @ int<i32>")]]
[[rc::requires("{StronglySorted (≤) ls}")]]
[[rc::returns("{x ∈ ls} @ optional<∃ i : nat. i @ int<i32> & {ls !! i = Some x}, {-1} @ int<i32>>")]]
[[rc::ensures("own p : array<i32, {ls `at_type` int i32}>")]]
 [[rc::lemmas("list_elem_of_lookup_2", "must_be_in_range_full", "must_be_in_range_not_in",
             "must_be_in_range_sorted_r", "must_be_in_range_sorted_l")]]
int binary_search(int *xs, int n, int x) {
  int l = 0, r = n;
  [[rc::exists("vl : nat", "vr : nat")]]
  [[rc::inv_vars("l : vl @ int<i32>", "r : vr @ int<i32>")]]
  [[rc::constraints("{vl <= vr}", "{vr <= length ls}", "{must_be_in_range ls vl vr x}")]]
  while(l < r) {
    int k = l + (r - l) / 2;
    if (xs[k] == x) {
      return k;
    } else if (xs[k] < x) {
      l = k + 1;
      } else {
      r = k;
    }
  }
  return -1;
}

/**

   Programs verified using RefinedC can be split into three categories:


   |   | program uses                                 | User needs to know      | Examples of programs                               |
   |---+----------------------------------------------+-------------------------+----------------------------------------------------|
   | 1 | large subset of C                            | Typesystem              | integers and controlflow (t1_basic)                |
   |   | concurrency via abstractions (e.g. spinlock) |                         | lists (t3_list, reverse)                           |
   |   | reasoning with builtin support               |                         | allocators (t4_alloc, mpool, malloc1, mpool_simpl) |
   |   | (currently integers, lists)                  |                         | arrays (t7_arrays)                                 |
   |   | ownership reasoning                          |                         | structs (t6_structs)                               |
   |   |                                              |                         | initialization (t5_main)                           |
   |---+----------------------------------------------+-------------------------+----------------------------------------------------|
   | 2 | harder functional correctness reasoning      | Typesystem + Coq        | binary search (t0_intro)                           |
   |   | custom functional model                      |                         | hashmap with linear probing (mutable_map)          |
   |   | custom automation for sideconditions         |                         | binary search trees (t8_tree)                      |
   |---+----------------------------------------------+-------------------------+----------------------------------------------------|
   | 3 | novel / custom abstractions                  | Typesystem + Coq + Iris | spinlock (spinlock)                                |
   |   | fine grained concurrency                     |                         |                                                    |


*/
