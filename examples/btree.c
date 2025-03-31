#include <refinedc.h>
#include <refinedc_malloc.h>
#include "btree.h"

//@rc::import btree_learn from refinedc.examples.btree (for proofs only)

btree_t* new_btree(){
  btree_t* t = xmalloc(sizeof(btree_t));
  *t = NULL;
  return t;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<btree_t>")]]
[[rc::ensures("own p : null")]]
[[rc::trust_me]] // FIXME
void free_btree_nodes(btree_t* t){
  if(*t == NULL) return;

  for(int i = 0; i <= (*t)->nb_keys; i++){
    free_btree_nodes(&(*t)->children[i]);
  }

  free(*t);
  *t = NULL;
}

void free_btree(btree_t* t){
  free_btree_nodes(t);
  free(t);
}

// Finds the index at which the key [k] should be inserted in the sorted array
// of integers [ar] of size [n].
[[rc::parameters("p : loc", "l : {list Z}", "n : nat", "k : Z", "sz : nat")]]
[[rc::args("p @ &own<array<{it_layout i32}, {(l `at_type` int i32) ++ "
                     "replicate (sz - n)%nat (uninit i32 : type)}>>")]]
[[rc::args("n @ int<i32>", "k @ int<i32>")]]
[[rc::requires("{n = length l}", "{StronglySorted (<) l}")]]
[[rc::exists("s : nat")]]
[[rc::returns("s @ int<i32>")]]
[[rc::ensures("{s ≤ n}")]]
[[rc::ensures("{k ∈ l → l !! s = Some k}")]]
[[rc::ensures("{¬ k ∈ l → StronglySorted (<) (take s l ++ k :: drop s l)}")]]
[[rc::ensures("own p : array<{it_layout i32}, {(l `at_type` int i32) ++ "
                        "replicate (sz - n)%nat (uninit i32 : type)}>")]]
[[rc::tactics("destruct (decide (i = s)); by naive_solver lia.")]]
[[rc::tactics(// FIXME
  "move: (elem_of_list_lookup_1 _ _ H14) => [i Hi]. "
  "destruct (decide (y = k)); [ done | exfalso ]. "
  "assert (k < y) as Hky by lia. "
  "assert (i < s)%nat as Hle by by eapply (StronglySorted_lookup_index_lt (R:=(<))). "
  "assert (i < s) as His  by lia. assert (k < k) by by eapply H0. by lia.")]]
[[rc::tactics(// FIXME
  "apply StronglySorted_insert_drop_take; last done. "
  "* move => z Hz. destruct (l !! z) eqn:?; naive_solver lia. "
  "* move: (elem_of_list_lookup_2 l s y H7) => Hy. rewrite H7 /=. "
  "  assert (k ≠ y); [ by set_solver | by lia ].")]]
[[rc::tactics(// FIXME
  "assert (s = length l) as -> by lia. assert (k < k); last by lia. "
  "move: (elem_of_list_lookup_1 _ _ H7) => [i Hi]. "
  "move: (lookup_lt_Some _ _ _ Hi) => Hlt. naive_solver lia.")]]
[[rc::tactics(// FIXME
  "assert (s = length l) as -> by lia. rewrite drop_all. "
  "apply StronglySorted_app; [ .. | done | by do 2 constructor ]. "
  "move => x y Hx Hy. assert (y = k) as -> by set_solver. "
  "move: (elem_of_list_lookup_1 _ _ Hx) => [i Hi]. "
  "move: (lookup_lt_Some _ _ _ Hi) => Hlt. naive_solver lia.")]]
int key_index(int* ar, int n, int k){
  int slot = 0;

  [[rc::exists("s : nat")]]
  [[rc::inv_vars("slot : s @ int<i32>")]]
  [[rc::constraints("{∀ i : nat, ∀ v : Z, l !! i = Some v → i < s → v < k}")]]
  [[rc::constraints("{s ≤ length l}")]]
  while(slot < n && ar[slot] < k){
    slot++;
  }

  return slot;
}

[[rc::tactics("unfold btree_invariant in *; by solve_goal.")]]
[[rc::tactics("rewrite H1; by apply: (btree_invariant_in_keys_not_None H2).")]]
[[rc::tactics("by rewrite list_insert_id.")]]
[[rc::tactics("eapply (btree_invariant_in_range_child H2); naive_solver lia.")]]
[[rc::tactics("eapply (btree_invariant_in_range_child H2); naive_solver lia.")]]
[[rc::tactics("rewrite H1; apply: (btree_invariant_lookup_child H2); by naive_solver.")]]
[[rc::tactics("do 2 rewrite list_insert_id //; by destruct y0.")]]
[[rc::tactics("assert (k ∉ x0) as Hx1. { move => /H7 Hk. apply lookup_lt_Some in Hk. lia. } "
              "eapply (btree_invariant_in_range_child H2); by naive_solver.")]]
[[rc::tactics("assert (k ∉ x0) as Hx1. { move => /H7 Hk. apply lookup_lt_Some in Hk. lia. } "
              "eapply (btree_invariant_in_range_child H2); by naive_solver.")]]
[[rc::tactics("assert (k ∉ x0) as Hx1. { move => /H7 Hk. apply lookup_lt_Some in Hk. lia. } "
              "rewrite H1. apply: (btree_invariant_lookup_child H2); by naive_solver.")]]
[[rc::tactics("rewrite list_insert_id //; by destruct y.")]]
[[rc::tactics("unfold btree_invariant in *; by solve_goal.")]]
bool btree_member(btree_t* t, int k){
  btree_t* cur = &*t;
  rc_unfold_int(k);

  [[rc::exists("cur_p : loc", "cur_m : {gmap Z type}")]]
  [[rc::exists("b : bool", "cur_h : nat", "min_k : Z", "max_k : Z")]]
  [[rc::inv_vars("cur : cur_p @ &own<{BR b cur_h min_k max_k cur_m} @ btree_t>")]]
  [[rc::inv_vars("t : p @ &own<wand<{cur_p ◁ₗ !{{BR b cur_h min_k max_k cur_m} @ btree_t}}, "
                 " {BRroot h m} @ btree_t>>")]]
  [[rc::constraints("{min_k ≤ k ∧ k ≤ max_k}", "{m !! k = cur_m !! k}")]]
  while(*cur != NULL){
    int i = key_index((*cur)->keys, (*cur)->nb_keys, k);

    if(i < (*cur)->nb_keys && (*cur)->keys[i] == k) return true;

    cur = &((*cur)->children[i]);
  }

  return false;
}

[[rc::trust_me]] // FIXME
void** btree_find(btree_t* t, int k){
  btree_t* cur = &*t;

  while(*cur != NULL){
    int i = key_index((*cur)->keys, (*cur)->nb_keys, k);

    if(i < (*cur)->nb_keys && (*cur)->keys[i] == k) return &((*cur)->vals[i]);

    cur = &((*cur)->children[i]);
  }

  return NULL;
}

// Inserts the key [k] with value [v] into the given [node] in such a way that
// it has branch [b] as its right subtree. If splitting is required, the right
// branch produced is returned, in which case the median key / value pair that
// is to be inserted into the parent node is written in [med_k] and [med_v].
[[rc::skip]] // FIXME
btree_t insert_br(btree_t* node, int k, void* v, btree_t b,
    int* med_k, void** med_v){
  // Find the insertion index.
  int n = (*node)->nb_keys;
  int slot = key_index((*node)->keys, n, k);
  int i;

  // Directly insert if a slot is available.
  if((*node)->nb_keys < ORDER - 1){
    // Make space in the arrays.
    for(i = n; i > slot; i--){
      (*node)->keys[i] = (*node)->keys[i - 1];
      (*node)->vals[i] = (*node)->vals[i - 1];

      (*node)->children[i+1] = (*node)->children[i];
    }

    // Write in the new slot.
    (*node)->keys[slot] = k;
    (*node)->vals[slot] = v;
    (*node)->children[slot + 1] = b;

    // Increment the key counter and return (no spliting occured).
    (*node)->nb_keys++;
    return NULL;
  }

  // We need to split the node, so we allocate a new one.
  btree_t new_node = xmalloc(sizeof(struct btree));

  new_node->height = (*node)->height;

  // Slot of the median key.
  int med = ORDER / 2;

  // Case where insertion occurs in the original node.
  if(slot < med){
    // The median is actually in slot [med - 1].
    *med_k = (*node)->keys[med - 1];
    *med_v = (*node)->vals[med - 1];

    // The new key will be inserted on the left, first buld the new node.
    for(i = med; i < ORDER; i++){
      new_node->keys[i - med] = (*node)->keys[i];
      new_node->vals[i - med] = (*node)->vals[i];

      new_node->children[i - med + 1] = (*node)->children[i + 1];
    }

    new_node->children[0] = (*node)->children[med]; // Not done by the loop.

    // Make space for the inserted key and value in the original node.
    for(i = med - 1; i > slot; i--){
      (*node)->keys[i] = (*node)->keys[i - 1];
      (*node)->vals[i] = (*node)->vals[i - 1];

      (*node)->children[i+1] = (*node)->children[i];
    }

    // Write in the new slot.
    (*node)->keys[slot] = k;
    (*node)->vals[slot] = v;
    (*node)->children[slot + 1] = b;

    // Update the key counters and return the created node.
    new_node->nb_keys = ORDER - med - 1;
    (*node)->nb_keys = med;
    return new_node;
  }

  // Case where the inserted key is the median.
  if(slot == med){
    *med_k = k;
    *med_v = v;

    // First build the new node.
    for(i = med; i < ORDER - 1; i++){
      new_node->keys[i - med] = (*node)->keys[i];
      new_node->vals[i - med] = (*node)->vals[i];

      new_node->children[i - med + 1] = (*node)->children[i + 1];
    }

    new_node->children[0] = b; // Attach the branch from the above level.

    // Update the key counters and return the created node.
    new_node->nb_keys = ORDER - med - 1;
    (*node)->nb_keys = med;
    return new_node;
  }

  // Last case, the key is inserted in the created node after the split.
  *med_k = (*node)->keys[med];
  *med_v = (*node)->vals[med];

  // Insert in the new node up to the slot.
  for(i = med + 1; i < slot; i++){
    new_node->keys[i - (med + 1)] = (*node)->keys[i];
    new_node->vals[i - (med + 1)] = (*node)->vals[i];

    new_node->children[i - med] = (*node)->children[i + 1];
  }

  new_node->children[0] = (*node)->children[med + 1]; // Not done by the loop.

  // Insert the new node in its slot.
  new_node->keys[slot - (med + 1)] = k;
  new_node->vals[slot - (med + 1)] = v;
  new_node->children[slot - med] = b;

  // Insert the rest of the nodes after the slot.
  for(i = slot; i < ORDER - 1; i++){
    new_node->keys[i - med] = (*node)->keys[i];
    new_node->vals[i - med] = (*node)->vals[i];

    new_node->children[i - med + 1] = (*node)->children[i + 1];
  }

  // Update the key counters and return the created node.
  new_node->nb_keys = ORDER - med - 1;
  (*node)->nb_keys = med;
  return new_node;
}

[[rc::parameters("rl : btree_rfmt", "rr : btree_rfmt")]]
[[rc::parameters("k : Z", "v : loc", "ty : type")]]
[[rc::args("rl @ btree_t", "rr @ btree_t", "k @ int<i32>", "v @ &own<ty>")]]
[[rc::requires("{br_height rl + 1 ≤ max_int i32}")]]
[[rc::requires("{br_height rl = br_height rr}")]]
[[rc::requires("{br_max rl = (k - 1)%Z}", "{br_min rr = (k + 1)%Z}")]]
[[rc::requires("{br_min rl = min_int i32}", "{br_max rr = max_int i32}")]]
[[rc::returns("{BR true (br_height rl + 1)%nat (br_min rl) (br_max rr) "
              "({[k:=ty]} ∪ (br_map (non_root rl) ∪ br_map (non_root rr)))} "
              "@ btree_t")]]
[[rc::lemmas("insert_non_empty")]]
[[rc::trust_me]] // FIXME
static inline btree_t btree_make_root(btree_t l, btree_t r, int k, void* v){
  btree_t root = xmalloc(sizeof(struct btree));

  if(l == NULL){
    root->height = 1;
  } else {
    root->height = l->height + 1;
  }

  root->nb_keys = 1;
  root->keys[0] = k;
  root->vals[0] = v;

  root->children[0] = l;
  rc_learn(r);
  root->children[1] = r;

  rc_unfold_int(k);
  return root;
}

[[rc::trust_me]] // FIXME
void btree_insert(btree_t* t, int k, void* v){
  // We first handle the case where the B-tree is empty.
  if(*t == NULL){
    *t = btree_make_root(NULL, NULL, k, v);
    return;
  }

  // We remember the nodes and corresponding keys on the insertion path.
  btree_t** path_ptrs = xmalloc(((*t)->height + 1) * sizeof(btree_t*));
  int* path_keys = xmalloc((*t)->height * sizeof(int));

  path_ptrs[0] = &*t;
  int cur = 0;

  while(*(path_ptrs[cur]) != NULL){
    btree_t* cur_node = path_ptrs[cur];
    int i = key_index((*cur_node)->keys, (*cur_node)->nb_keys, k);

    if(i < (*cur_node)->nb_keys && (*cur_node)->keys[i] == k){
      (*cur_node)->vals[i] = v;
      goto done;
    }

    path_keys[cur] = i;
    cur++;
    path_ptrs[cur] = &((*cur_node)->children[i]);
  }

  // Currently inserted.
  int ins_k = k;
  void* ins_v = v;
  btree_t ins_b = NULL;

  int med_k;
  void* med_v;
  btree_t new;

  while(cur > 0){
    btree_t* node = path_ptrs[cur - 1];

    new = insert_br(node, ins_k, ins_v, ins_b, &med_k, &med_v);

    // Insertion done, no split.
    if(new == NULL) goto done;

    // A split occured.
    ins_k = med_k;
    ins_v = med_v;
    ins_b = new;

    cur--;
  }

  // Create and install the new root.
  *t = btree_make_root(*t, new, med_k, med_v);

  // Free the path data.
done:
  free(path_ptrs);
  free(path_keys);
}
