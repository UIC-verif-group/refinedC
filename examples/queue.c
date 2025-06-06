#include <stdbool.h>
#include <refinedc.h>
#include <refinedc_malloc.h>

typedef struct [[rc::parameters("cont : type")]]
               [[rc::refined_by("ty: type")]]
               [[rc::typedef("queue_elem : &own<malloced<{ly_size struct_queue_elem}, ...>>")]]
queue_elem {
  [[rc::field("&own<ty>")]]
  void *elem;
  [[rc::field("cont")]]
  struct queue_elem *next;
} *queue_elem_t;

typedef struct [[rc::refined_by("tys: {list type}")]]
               [[rc::typedef("queue : ∃ p. own_constrained<tyown_constraint<p, null>, &own<...>>")]]
queue {
  [[rc::field("tyfold<{(λ ty x, ty @ queue_elem x) <$> tys}, place<p>>")]]
  queue_elem_t head;
  [[rc::field("&own<place<p>>")]]
  queue_elem_t *tail;
} *queue_t;

[[rc::returns("{[]} @ queue")]]
queue_t init_queue() {
  queue_t queue = xmalloc(sizeof(struct queue));
  queue->head = NULL;
  queue->tail = &queue->head;
  return queue;
}

[[rc::parameters("p : loc", "tys : {list type}")]]
[[rc::args("p @ &own<{tys} @ queue>")]]
[[rc::returns("{bool_decide (tys ≠ [])} @ builtin_boolean")]]
[[rc::ensures("own p : {tys} @ queue")]]
bool is_empty(queue_t *q) {
  return (*q)->head != NULL;
}

[[rc::parameters("p : loc", "tys : {list type}", "ty : type")]]
[[rc::args("p @ &own<{tys} @ queue>", "&own<ty>")]]
[[rc::ensures("own p : {tys ++ [ty]} @ queue")]]
void enqueue(queue_t *q, void *v) {
  queue_elem_t elem = xmalloc(sizeof(struct queue_elem));
  elem->elem = v;
  elem->next = NULL;
  *(*q)->tail = elem;
  (*q)->tail = &elem->next;
}

[[rc::parameters("p : loc", "tys : {list type}")]]
[[rc::args("p @ &own<{tys} @ queue>")]]
[[rc::returns("{maybe2 cons tys} @ optionalO<λ (ty, _). &own<ty>>")]]
[[rc::ensures("own p : {tail tys} @ queue")]]
void *dequeue(queue_t *q) {
  if ((*q)->head == NULL) {
    return NULL;
  }
  queue_elem_t elem = (*q)->head;
  void *ret = elem->elem;
  if(elem->next == NULL) {
    (*q)->head = NULL;
    (*q)->tail = &(*q)->head;
  } else {
    (*q)->head = elem->next;
  }
  free(elem);
  return ret;
}
