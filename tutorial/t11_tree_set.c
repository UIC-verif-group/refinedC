#include <stdbool.h>
#include <refinedc.h>
#include "talloc.h"

// In part inspired from the following example from Verifast:
// https://github.com/verifast/verifast/blob/master/examples/sorted_bintree.c

typedef struct [[rc::refined_by("s : {gset Z}")]]
               [[rc::typedef("tree_t : {s ≠ ∅} @ optional<&own<...>>")]]
               [[rc::exists("sl : {gset Z}", "sr : {gset Z}", "k : Z")]]
               [[rc::constraints("{s = sl ∪ {[k]} ∪ sr}", "{set_Forall (λ i, i < k) sl}",
                                 "{set_Forall (λ i, k < i) sr}")]]
tree {
  [[rc::field("sl @ tree_t")]]
  struct tree* left;

  [[rc::field("sr @ tree_t")]]
  struct tree* right;

  [[rc::field("k @ int<size_t>")]]
  size_t key;
} *tree_t;

[[rc::returns("{∅} @ tree_t")]]
tree_t empty(){
  return NULL;
}

[[rc::parameters("k : Z")]]
[[rc::args("k @ int<size_t>")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::returns("{{[k]}} @ tree_t")]]
 [[rc::tactics("all: try by set_solver.")]]
tree_t init(size_t key){
  struct tree *node = talloc(sizeof(struct tree));
  node->left  = NULL;
  node->key   = key;
  node->right = NULL;
  return node;
}

[[rc::parameters("sl : {gset Z}", "k : Z", "sr : {gset Z}")]]
[[rc::args("sl @ tree_t", "k @ int<size_t>", "sr @ tree_t")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::requires("{set_Forall (λ i, i < k) sl}", "{set_Forall (λ i, k < i) sr}")]]
[[rc::returns("{sl ∪ {[k]} ∪ sr} @ tree_t")]]
 [[rc::tactics("all: try by set_solver.")]]
tree_t node(tree_t left, size_t key, tree_t right){
  struct tree *node = talloc(sizeof(struct tree));
  node->left  = left;
  node->key   = key;
  node->right = right;
  return node;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<tree_t>")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::ensures("own p : uninit<void*>")]]
void free_tree(tree_t* t){
  if(*t != NULL){
    free_tree(&((*t)->left));
    free_tree(&((*t)->right));
    tfree(sizeof(struct tree), *t);
  }
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::returns("{bool_decide (k ∈ s)} @ builtin_boolean")]]
[[rc::ensures("own p : s @ tree_t")]]
 [[rc::tactics("all: try by set_unfold; naive_solver lia.")]]
bool member_rec(tree_t* t, size_t k){
  if(*t == NULL) return false;
  if((*t)->key == k) return true;
  if(k < (*t)->key) return member_rec(&((*t)->left), k);
  return member_rec(&((*t)->right), k);
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::returns("{bool_decide (k ∈ s)} @ builtin_boolean")]]
[[rc::ensures("own p : s @ tree_t")]]
 [[rc::tactics("all: try by set_unfold; naive_solver lia.")]]
bool member(tree_t* t, size_t k){
  tree_t* cur = &*t;

  [[rc::exists("cur_p : loc", "cur_s : {gset Z}")]]
  [[rc::inv_vars("cur : cur_p @ &own<cur_s @ tree_t>")]]
  [[rc::inv_vars("t : p @ &own<wand<{cur_p ◁ₗ cur_s @ tree_t}, s @ tree_t>>")]]
  [[rc::constraints("{k ∈ s ↔ k ∈ cur_s}")]]
  while(*cur != NULL){
    if((*cur)->key == k) return true;
    if(k < (*cur)->key){
      cur = &((*cur)->left);
    } else {
      cur = &((*cur)->right);
    }
  }
  return false;
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::ensures("own p : {{[k]} ∪ s} @ tree_t")]]
 [[rc::tactics("all: try by set_unfold; (solve_goal || naive_solver lia).")]]
void insert_rec(tree_t* t, size_t k) {
  if(*t == NULL) {
    *t = node(NULL, k, NULL);
  } else {
    if((*t)->key == k) {
      return;
    } else if(k < (*t)->key) {
      insert_rec(&((*t)->left), k);
    } else {
      insert_rec(&((*t)->right), k);
    }
  }
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::ensures("own p : {{[k]} ∪ s} @ tree_t")]]
 [[rc::tactics("all: try by set_unfold; (solve_goal || naive_solver lia).")]]
void insert(tree_t* t, size_t k){
  tree_t* cur = &*t;

  [[rc::exists("cur_p : loc", "cur_s : {gset Z}")]]
  [[rc::inv_vars("cur : cur_p @ &own<cur_s @ tree_t>")]]
  [[rc::inv_vars("t : p @ &own<wand<{cur_p ◁ₗ ({[k]} ∪ cur_s) @ tree_t}, {{[k]} ∪ s} @ tree_t>>")]]
  while(*cur != NULL){
    if((*cur)->key == k) return;
    if(k < (*cur)->key){
      cur = &((*cur)->left);
    } else {
      cur = &((*cur)->right);
    }
  }

  *cur = node(NULL, k, NULL);
}

[[rc::parameters("p : loc", "s : {gset Z}")]]
[[rc::args("p @ &own<s @ tree_t>")]]
[[rc::requires("{s ≠ ∅}")]]
[[rc::exists("m : Z")]]
[[rc::returns("m @ int<size_t>")]]
[[rc::ensures("{m ∈ s}", "{set_Forall (λ i, i ≤ m) s}")]]
[[rc::ensures("own p : s @ tree_t")]]
 [[rc::tactics("all: by set_unfold_trigger; refined_solver (trigger_foralls; lia).")]]
size_t tree_max(tree_t* t){
  if((*t)->right == NULL) {
    return (*t)->key;
  }
  return tree_max(&((*t)->right));
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::ensures("own p : {s ∖ {[k]}} @ tree_t")]]
 [[rc::tactics("all: try apply Z.le_neq.")]]
 [[rc::tactics("all: try (rewrite difference_union_L !difference_union_distr_l_L !difference_diag_L !difference_disjoint_L; move: (H0 x2) (H1 x2); clear -H9).")]]
 [[rc::tactics("all: try by set_unfold_trigger; naive_solver (trigger_foralls; lia).")]]
void remove(tree_t* t, size_t k){
  tree_t tmp;
  size_t m;
  if(*t == NULL) {
    return;
  }

  if(k == (*t)->key) {
    if((*t)->left != NULL){
      m = tree_max(&(*t)->left);
      remove(&(*t)->left, m);
      (*t)->key = m;
    } else {
      tmp = (*t)->right;
      tfree(sizeof(struct tree), *t);
      *t = tmp;
    }
  } else if(k < (*t)->key){
    remove(&(*t)->left, k);
  } else {
    remove(&(*t)->right, k);
  }
}

[[rc::requires("[talloc_initialized]")]]
[[rc::returns("{0} @ int<i32>")]]
int main(){
  tree_t t = empty();
  t = init(3);

  //assert(!member(&t, 2)); // FIXME cast missing?

  insert(&t, 2);

  assert(member(&t, 2));
  assert(member(&t, 3));

  remove(&t, 3);
  //assert(!member(t, 3); // FIXME cast missing?

  insert(&t, 3);
  assert(member(&t, 2));

  remove(&t, 3);
  //assert(!member(t, 3); // FIXME cast missing?

  free_tree(&t);

  return 0;
}
