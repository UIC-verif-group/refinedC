#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>
#include <refinedc_malloc.h>

//@rc::import binary_search_extra from refinedc.examples.binary_search

typedef bool (*comp_fn)(void *, void *);

[[rc::parameters("R : {Z → Z → Prop}", "ls : {list (loc * Z)}", "x : Z", "p : loc", "ty : {Z → type}", "px : loc")]]
[[rc::args("function_ptr<{fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ builtin_boolean; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝}>",
      "p @ &own<array<void*, {(fun x => (x.1 @ &own (ty x.2)) : type) <$> ls}>>", "{length ls} @ int<size_t>", "px @ &own<{ty x}>")]]
[[rc::requires("{StronglySorted R ls.*2}", "{Transitive R}")]]
[[rc::exists("n : nat")]]
[[rc::returns("n @ int<size_t>")]]
[[rc::ensures("{∀ i y, (i < n)%nat → ls.*2 !! i = Some y → R y x}",
              "{∀ i y, (n ≤ i)%nat → ls.*2 !! i = Some y → ¬ R y x}")]]
[[rc::ensures("own p : array<void*, {(fun x => (x.1 @ &own (ty x.2)) : type) <$> ls}>")]]
[[rc::ensures("own px : ty<x>")]]
[[rc::tactics("all: try by [revert select (∀ i j, _ → _ → ¬ R _ _); apply; [|apply list_lookup_fmap_Some; eexists (_, _); naive_solver]; solve_goal].")]]
[[rc::tactics("all: try by apply: binary_search_cond_1; [solve_goal|..]; solve_goal.")]]
[[rc::tactics("all: try by apply: binary_search_cond_2; [solve_goal|..]; solve_goal.")]]
size_t binary_search(comp_fn comp, void **xs, size_t n, void *x) {
  size_t l = 0, r = n;
  [[rc::exists("vl : nat", "vr : nat")]]
  [[rc::inv_vars("l : vl @ int<size_t>", "r : vr @ int<size_t>")]]
  [[rc::constraints("{vl <= vr}", "{vr <= length ls}")]]
  [[rc::constraints("{∀ i y, (i < vl)%nat → ls.*2 !! i = Some y → R y x}",
                    "{∀ i y, (vr ≤ i)%nat → ls.*2 !! i = Some y → ¬ R y x}")]]
  while(l < r) {
    size_t k = l + (r - l) / 2;
    if (comp(xs[k], x)) {
      l = k + 1;
      } else {
      r = k;
    }
  }
  return l;
}

[[rc::parameters("x : Z", "y : Z", "px : loc", "py : loc")]]
[[rc::args("px @ &own<x @ int<size_t>>", "py @ &own<y @ int<size_t>>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own px : x @ int<size_t>", "own py : y @ int<size_t>", "{b ↔ Z.le x y}")]]
bool compare_int(void *x, void *y) {
  size_t *xi = x, *yi = y;
  return *xi <= *yi;
}

[[rc::requires("True")]]
[[rc::tactics("all: try by repeat constructor; lia.")]]
[[rc::tactics("all: try by apply _.")]]
[[rc::tactics("all: try by do 4 (destruct x'; [ naive_solver lia |]); exfalso; apply: (H0 3%nat) => //; lia.")]]
void test() {
  size_t *ptrs[5];
  ptrs[0] = xmalloc(sizeof(size_t));
  ptrs[1] = xmalloc(sizeof(size_t));
  ptrs[2] = xmalloc(sizeof(size_t));
  ptrs[3] = xmalloc(sizeof(size_t));
  ptrs[4] = xmalloc(sizeof(size_t));
  *ptrs[0] = 0;
  *ptrs[1] = 1;
  *ptrs[2] = 2;
  *ptrs[3] = 3;
  *ptrs[4] = 4;

  size_t needle = 2;
  int res = binary_search(compare_int, (void **)ptrs, 5, &needle);
  assert(res == 3);

  free(ptrs[0]);
  free(ptrs[1]);
  free(ptrs[2]);
  free(ptrs[3]);
  free(ptrs[4]);
}
