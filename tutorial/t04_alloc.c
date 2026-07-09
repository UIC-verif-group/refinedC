#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>
#include <spinlock.h>
#include "talloc_internal.h"

 [[rc::global("alloc_state")]]
static struct alloc_state allocator_state;

 [[rc::tactics("all: try by apply: has_layout_loc_trans' => //; normalize_and_simpl_goal => //; apply: keep_factor2_leq; [solve_goal|]; apply Nat.divide_sub_r; apply Nat2Z.divide; rewrite /ly_align/ly_align_log/=; solve_goal.")]]
void *talloc(size_t size) {

  [[rc::constraints("[initialized \"allocator_state\" ()]")]]
  while(1) {
    sl_lock(&allocator_state.lock);
    rc_unlock(allocator_state.data);


    alloc_entry_t *prev = &allocator_state.data;
    [[rc::block]]
    [[rc::exists("pc : loc")]]
    [[rc::inv_vars("prev : pc @ &own<alloc_entry_t>")]]
    [[rc::constraints("[global_allocator_state at{struct_alloc_state}ₗ \"data\" ◁ₗ wand (pc ◁ₗ alloc_entry_t) alloc_entry_t]")]]
    while(*prev != NULL) {
      alloc_entry_t cur = *prev;

      if(cur->size == size) {
        *prev = cur->next;
        sl_unlock(&allocator_state.lock);
        return cur;
      }
      if(cur->size >= size + sizeof(struct alloc_entry)) {
        cur->size -= size;
        void *ret = ((unsigned char*)cur + cur->size);
        sl_unlock(&allocator_state.lock);
        return ret;
      }

      prev = &cur->next;
    }

    sl_unlock(&allocator_state.lock);
  }

}

 [[rc::tactics("all: try by rewrite ?Nat2Z.inj_mul ?Z2Nat.id //; apply Z.divide_factor_r.")]]
void tfree(size_t size, void *ptr) {
  if (size < sizeof(struct alloc_entry)) {
    // Too small to add to the list
    return;
  }

  struct alloc_entry *entry = ptr;
  entry->size = size;

  sl_lock(&allocator_state.lock);
  rc_unlock(allocator_state.data);

  entry->next = allocator_state.data;
  allocator_state.data = entry;

  sl_unlock(&allocator_state.lock);
}

void init_talloc() {
  sl_init(&allocator_state.lock);
  allocator_state.data = NULL;

  // The following used to be necessary but is not necessary anymore
  /* [[rc::constraints("own global_allocator_state : alloc_state")]] */
  /* rc_assert; */

  /* rc_share(allocator_state); */
}

 [[rc::tactics("all: try by rewrite /layout_wf -Z.mod_divide // /ly_size/ly_align/=; nia.")]]
void *talloc_array(size_t size, size_t n) {
  return talloc(n * size);
}

 [[rc::tactics("all: try by rewrite /layout_wf -Z.mod_divide // /ly_size/ly_align/=; nia.")]]
void tfree_array(size_t size, size_t n, void *ptr) {
  tfree(n * size, ptr);
}
