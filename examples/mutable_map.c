#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <refinedc.h>
#include <refinedc_malloc.h>

// see https://github.com/splatlab/veribetrfs/blob/master/lib/DataStructures/MutableMapImpl.i.dfy
// and https://github.com/splatlab/veribetrfs/blob/master/lib/DataStructures/MutableMapModel.i.dfy

//@rc::import mutable_map_extra from refinedc.examples.mutable_map

#define ITEM_EMPTY ((size_t)0)
#define ITEM_ENTRY ((size_t)1)
#define ITEM_TOMBSTONE ((size_t)2)

struct [[rc::tagged_union("item_ref")]]
item {
  size_t tag;

  union item_union {
    [[rc::union_tag("Empty")]]
    struct empty {
        [[rc::field("int<size_t>")]]
        size_t dummy; // TODO should empty struct be allowed / supported?
    } empty;

    [[rc::union_tag("Entry (key : Z) (ty : type)")]]
    struct entry {
        [[rc::field("key @ int<size_t>")]]
        size_t key;
        [[rc::field("&own<ty>")]]
        void* value;
    } entry;

    [[rc::union_tag("Tombstone (key : Z)")]]
    struct tombstone {
        [[rc::field("key @ int<size_t>")]]
        size_t key;
    } tombstone;
  } u;
};

struct [[rc::refined_by("mp : {gmap Z type}", "items : {list item_ref}", "count : nat")]]
       [[rc::constraints("{1 < length items}", "{count = length (filter (λ x, x = Empty) items)}",
                         "{0 < count}", "{fsm_invariant mp items}")]]
fixed_size_map {
  [[rc::field("&own<malloced<{ly_size struct_item * length items}, array<struct_item, {items `at_type` item}>>>")]]
  struct item (* items)[];

  [[rc::field("count @ int<size_t>")]]
  size_t count;

  [[rc::field("{length items} @ int<size_t>")]]
  size_t length;
};

[[rc::parameters("m : loc", "items : {list item_ref}", "count : nat", "mp : {gmap Z type}")]]
[[rc::args("m @ &own<{mp, items, count} @ fixed_size_map>")]]
[[rc::exists("items2 : {list item_ref}", "count2: nat")]]
[[rc::ensures("own m : {mp, items2, count2} @ fixed_size_map", "{count <= count2}", "{1 < count2}",
              "{length items <= length items2}")]]
void fsm_realloc_if_necessary(struct fixed_size_map *m);


[[rc::parameters("m : loc", "len : nat")]]
[[rc::args("m @ &own<uninit<struct_fixed_size_map>>")]]
[[rc::args("len @ int<size_t>")]]
[[rc::requires("{1 < len}", "{struct_item.(ly_size) * len + 16 ≤ max_int size_t}")]]
[[rc::ensures("own m : {∅, replicate len Empty, len} @ fixed_size_map")]]
 [[rc::lemmas("fsm_invariant_init")]]
 [[rc::tactics("all: try by apply/list_subequiv_split; solve_goal.")]]
 [[rc::tactics("all: try by rewrite length_filter_replicate_True; solve_goal.")]]
 [[rc::tactics("all: try by rewrite (replicate_O _ (len-i)); [solve_goal | lia].")]]
void fsm_init(struct fixed_size_map *m, size_t len) {
  size_t i;
  void *storage = xmalloc(sizeof(struct item) * len);
  m->length = len;
  m->items = storage;
  m->count = len;

  [[rc::exists("i : nat")]]
  [[rc::inv_vars("i : i @ int<size_t>")]]
  [[rc::inv_vars("m : m @ &own<struct<struct_fixed_size_map, &own<malloced<{ly_size struct_item * len}, array<struct_item," \
                "{replicate i Empty `at_type` item ++ replicate (len - i)%nat (uninit (struct_item))}>>>," \
                 "len @ int<size_t>, len @ int<size_t>>>")]]
  [[rc::constraints("{i <= len}")]]
  for(i = 0; i < len; i += 1) {
    (*m->items)[i].tag = ITEM_EMPTY;
    (*m->items)[i].u.empty.dummy = 0;
  }
}

[[rc::parameters("len : nat", "key : Z")]]
[[rc::args("len @ int<size_t>")]]
[[rc::args("key @ int<size_t>")]]
[[rc::requires("{(0 < len)%nat}")]]
[[rc::returns("{slot_for_key_ref key len} @ int<size_t>")]]
 [[rc::lemmas("slot_for_key_ref_unfold_rem")]]
size_t fsm_slot_for_key(size_t len, size_t key) {
    // TODO: hash
    return key % len;
}

[[rc::parameters("m : loc", "mp : {gmap Z type}", "items : {list item_ref}", "key : Z", "count : nat")]]
[[rc::args("m @ &own<{mp, items, count} @ fixed_size_map>", "key @ int<size_t>")]]
[[rc::exists("n : nat")]]
[[rc::returns("n @ int<size_t>")]]
[[rc::ensures("own m : {mp, items, count} @ fixed_size_map")]]
[[rc::ensures("{∃ x, items !! n = Some x ∧ probe_ref key items = Some (n, x)}")]]
 [[rc::lemmas("lookup_lt_is_Some_2")]]
 [[rc::tactics("all: try by eexists _; split => //; apply probe_ref_take_Some; naive_solver.")]]
 [[rc::tactics("all: try by apply: probe_ref_go_next_take => // ? /lookup_rotate_r_Some ?; try lia; simplify_eq; naive_solver.")]]
size_t fsm_probe(struct fixed_size_map *m, size_t key) {
    size_t slot_idx = fsm_slot_for_key(m->length, key);

    [[rc::exists("offset : nat")]]
    [[rc::inv_vars("slot_idx : {rotate_nat_add (slot_for_key_ref key (length items)) offset (length items)} @ int<size_t>")]]
    [[rc::constraints("{probe_ref_go key (take offset (rotate (slot_for_key_ref key (length items)) items)) = None}")]]
    [[rc::constraints("{∃ x, items !! rotate_nat_add (slot_for_key_ref key (length items)) offset (length items) = Some x}")]]
    while(true) {
        if((*m->items)[slot_idx].tag == ITEM_EMPTY || ((*m->items)[slot_idx].tag == ITEM_TOMBSTONE && (*m->items)[slot_idx].u.tombstone.key == key)) {
            return slot_idx;
        }
        if((*m->items)[slot_idx].tag == ITEM_ENTRY && (*m->items)[slot_idx].u.entry.key == key) {
            return slot_idx;
        }
        rc_unfold_int(m->length);
        slot_idx = (slot_idx + 1) % m->length;
    }
}

[[rc::parameters("m : loc", "mp : {gmap Z type}", "items : {list item_ref}", "count : nat", "key : Z", "ty : type")]]
[[rc::args("m @ &own<{mp, items, count} @ fixed_size_map>", "key @ int<size_t>", "&own<ty>")]]
[[rc::exists("items2 : {list item_ref}", "count2 : nat")]]
[[rc::returns("{mp !! key} @ optionalO<λ ty. &own<ty>>")]]
[[rc::ensures("own m : {<[key:=ty]>mp, items2, count2} @ fixed_size_map")]]
[[rc::ensures("{count - 1 <= count2}", "{length items <= length items2}")]]
 [[rc::lemmas("fsm_invariant_insert")]]
 [[rc::tactics("all: try by erewrite length_filter_insert => //; solve_goal.")]]
 [[rc::tactics("all: try by eexists _; solve_goal.")]]
void *fsm_insert(struct fixed_size_map *m, size_t key, void *value) {
    fsm_realloc_if_necessary(m);
    size_t slot_idx = fsm_probe(m, key);
    void *replaced = NULL;
    struct item *item = &(*m->items)[slot_idx];
    if (item->tag == ITEM_ENTRY) {
        replaced = item->u.entry.value;
    } else if(item->tag == ITEM_EMPTY) {
      m->count -= 1;
    }

    item->tag = ITEM_ENTRY;
    item->u.entry.key = key;
    item->u.entry.value = value;

    return replaced;
}

[[rc::parameters("m : loc", "mp : {gmap Z type}", "items : {list item_ref}", "count : nat", "key : Z")]]
[[rc::args("m @ &own<{mp, items, count} @ fixed_size_map>", "key @ int<size_t>")]]
[[rc::exists("p : loc", "items2 : {list item_ref}")]]
[[rc::returns("{mp !! key} @ optionalO<λ ty. p @ &own<ty>>")]]
[[rc::ensures("own m : {alter (λ _, place p) key mp, items2, count} @ fixed_size_map")]]
 [[rc::tactics("all: try by erewrite length_filter_insert => //; solve_goal.")]]
void *fsm_get(struct fixed_size_map *m, size_t key) {
    size_t slot_idx = fsm_probe(m, key);
    struct item *item = &(*m->items)[slot_idx];

    if (item->tag == ITEM_ENTRY) {
        return &*item->u.entry.value;
    } else {
        return NULL;
    }
}

[[rc::parameters("m : loc", "mp : {gmap Z type}", "items : {list item_ref}", "count : nat", "key : Z")]]
[[rc::args("m @ &own<{mp, items, count} @ fixed_size_map>", "key @ int<size_t>")]]
[[rc::exists("items2 : {list item_ref}")]]
[[rc::returns("{mp !! key} @ optionalO<λ ty. &own<ty>>")]]
[[rc::ensures("own m : {delete key mp, items2, count} @ fixed_size_map")]]
 [[rc::lemmas("fsm_invariant_delete")]]
 [[rc::tactics("all: try by erewrite length_filter_insert => //; solve_goal.")]]
 [[rc::tactics("all: try by eexists _; solve_goal.")]]
void *fsm_remove(struct fixed_size_map *m, size_t key) {
    void* removed;
    size_t slot_idx = fsm_probe(m, key);
    struct item *item = &(*m->items)[slot_idx];

    if (item->tag == ITEM_ENTRY) {
        removed = item->u.entry.value;
        item->tag = ITEM_TOMBSTONE;
        item->u.tombstone.key = key;
        return removed;
    } else {
        return NULL;
    }
}

[[rc::parameters("n : Z")]]
[[rc::args("n @ int<size_t>")]]
[[rc::requires("{1 < n}")]]
[[rc::exists("m : Z")]]
[[rc::returns("m @ int<size_t>")]]
[[rc::ensures("{1 < m <= n}")]]
size_t compute_min_count(size_t len) {
  return 2;
}


 [[rc::tactics("all: try by eexists (length items); split_and?; rewrite ?drop_ge; solve_goal.")]]
 [[rc::tactics("all: try match goal with | H : fsm_invariant ?mp2 ?items2 |- fsm_invariant ?mp1 ?items1 => have ->: mp1 = mp2; [|done] end.")]]
 [[rc::tactics("all: try by apply: fsm_copy_entries_not_add; solve_goal.")]]
 [[rc::tactics("all: try by apply: fsm_copy_entries_add; solve_goal.")]]
 [[rc::tactics("all: try by apply: fsm_copy_entries_id; solve_goal.")]]
 [[rc::tactics("all: try by apply list_subequiv_split; [solve_goal|]; normalize_and_simpl_goal; try solve_goal; f_equal; solve_goal.")]]
void fsm_realloc_if_necessary(struct fixed_size_map *m) {
  if(compute_min_count(m->length) <= m->count) {
    return;
  }

  if(m->length < SIZE_MAX / 2 / sizeof(struct item) - 16) {} else { while(1); }

  struct fixed_size_map m2;
  size_t new_len = m->length * 2;

  fsm_init(&m2, new_len);
  [[rc::exists("i : nat", "items2 : {list item_ref}", "count2 : nat")]]
  [[rc::inv_vars("i : i @ int<size_t>")]]
  [[rc::inv_vars("m : m @ &own<struct<struct_fixed_size_map, &own<malloced<{ly_size struct_item * length items}, array<struct_item, {replicate i (uninit struct_item) ++ (drop i items `at_type` item)}>>>, int<size_t>, {length items} @ int<size_t>>>")]]
  [[rc::inv_vars("m2 : {fsm_copy_entries items i, items2, count2} @ fixed_size_map")]]
  [[rc::constraints("{count + length items - i < count2}", "{i <= length items}", "{0 < count}",
                    "{length items * 2 <= length items2}", "{fsm_invariant mp items}",
                    "{struct_item.(ly_size) * length items ≤ max_int size_t}")]]
  for(size_t i = 0; i < m->length; i += 1) {
    if((*m->items)[i].tag == ITEM_ENTRY) {
      fsm_insert(&m2, (*m->items)[i].u.entry.key, (*m->items)[i].u.entry.value);
    }
    rc_unfold(m2.length);
  }
  free(m->items);
  *m = m2;
}
