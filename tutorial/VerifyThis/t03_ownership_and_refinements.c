#include <stddef.h>
#include <refinedc.h>
#include "../talloc.h"

typedef struct [[rc::refined_by("xs : {list Z}")]]
[[rc::typedef("list_t : {xs <> []} @ optional<&own<...>, null>")]]
[[rc::exists("y : Z", "ys : {list Z}")]]
[[rc::constraints("{xs = y :: ys}")]]
list_node {
  [[rc::field("y @ int<i32>")]]
  int val;
  [[rc::field("ys @ list_t")]]
  struct list_node *next;
} *list_t;

/*

xs @ list_t :=
{xs <> []} @ optional<&own<
  ∃ y ys, struct<struct_list_node, y @ int<i32>, ys @ list_t> & {xs = y :: ys}>
  , null>

*/


[[rc::parameters("p : loc", "xs : {list Z}", "ys : {list Z}")]]
[[rc::args("p @ &own<xs @ list_t>", "ys @ list_t")]]
[[rc::ensures("own p : {xs ++ ys} @ list_t")]]
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

[[rc::requires("[talloc_initialized]")]]
void test() {
  struct list_node * node1 = talloc(sizeof(struct list_node));
  node1->val = 1; node1->next = NULL;
  struct list_node * node2 = talloc(sizeof(struct list_node));
  node2->val = 2; node2->next = NULL;
  append(&node1, node2);
  if(node1 != NULL) {
    assert(node1->val == 1);
  }
}
