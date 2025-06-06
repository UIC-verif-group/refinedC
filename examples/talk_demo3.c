#include <stddef.h>
#include <refinedc.h>
#include <refinedc_malloc.h>

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


[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<list_t>", "list_t")]]
[[rc::ensures("own p : list_t")]]
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

/* [[rc::requires("True")]] */
void test() {
  struct list_node * node1 = xmalloc(sizeof(struct list_node));
  node1->val = 1; node1->next = NULL;
  struct list_node * node2 = xmalloc(sizeof(struct list_node));
  node2->val = 2; node2->next = NULL;
  append(&node1, node2);
  if(node1 != NULL) {
    assert(node1->val == 1);
  }
}
