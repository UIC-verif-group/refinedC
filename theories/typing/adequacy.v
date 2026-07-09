From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap.
From iris.base_logic.lib Require Import ghost_map.
From caesium Require Import ghost_state.
From refinedc.typing Require Export type.
From refinedc.typing Require Import programs function bytes globals int fixpoint.
From iris.program_logic Require Export language. (* must be last to get the correct nsteps *)
Set Default Proof Using "Type".

Class typePreG Σ := PreTypeG {
  type_invG                      :: invGpreS Σ;
  type_heap_heap_inG             :: inG Σ (authR heapUR);
  type_heap_alloc_meta_map_inG  :: ghost_mapG Σ alloc_id (Z * nat * alloc_kind);
  type_heap_alloc_alive_map_inG  :: ghost_mapG Σ alloc_id bool;
  type_heap_fntbl_inG            :: ghost_mapG Σ addr function;
}.

Definition typeΣ : gFunctors :=
  #[invΣ;
   GFunctor (constRF (authR heapUR));
   ghost_mapΣ alloc_id (Z * nat * alloc_kind);
   ghost_mapΣ alloc_id bool;
   ghost_mapΣ addr function].
Global Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Definition initial_prog (main : loc) : runtime_expr :=
  coerce_rtexpr (Call main []).

Definition initial_heap_state :=
  {| hs_heap := ∅; hs_allocs := ∅; |}.

Definition initial_state (fns : gmap addr function) :=
  {| st_heap := initial_heap_state; st_fntbl := fns; |}.

Definition main_type `{!typeG Σ} (P : iProp Σ) :=
  fn(∀ () : (); P) → ∃ () : (), int i32; True.

(** * The main adequacy lemma *)
Lemma refinedc_adequacy Σ `{!typePreG Σ} (thread_mains : list loc) (fns : gmap addr function) (gls : list loc) (gvs : list val.val) n t2 σ2 κs hs σ:
  alloc_new_blocks initial_heap_state GlobalAlloc gls gvs hs →
  σ = {| st_heap := hs; st_fntbl := fns; |} →
  (∀ {HtypeG : typeG Σ}, ∃ gl gt,
  let Hglobals : globalG Σ := {| global_locs := gl; global_initialized_types := gt; |} in
    ([∗ list] l; v ∈ gls; gvs, l ↦ v) -∗
    ([∗ map] k↦qs∈fns, fntbl_entry (fn_loc k) qs) ={⊤}=∗
      [∗ list] main ∈ thread_mains, ∃ P, main ◁ᵥ main @ function_ptr (main_type P) ∗ P) →
  nsteps (Λ := c_lang) n (initial_prog <$> thread_mains, σ) κs (t2, σ2) →
  ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
Proof.
  move => Hnew -> Hwp. apply: wp_strong_adequacy. move => ?.
  set h := to_heapUR ∅.
  iMod (own_alloc (● h ⋅ ◯ h)) as (γh) "[Hh _]" => //.
  { apply auth_both_valid_discrete. split => //. }
  iMod (ghost_map_alloc fns) as (γf) "[Hf Hfm]".
  iMod (ghost_map_alloc_empty (V:=(Z * nat * alloc_kind))) as (γr) "Hr".
  iMod (ghost_map_alloc_empty (V:=bool)) as (γs) "Hs".
  set (HheapG := HeapG _ _ γh _ γr _ γs _ γf).
  set (HrefinedCG := RefinedCG _ _ HheapG).
  set (HtypeG := TypeG _ HrefinedCG).
  move: (Hwp HtypeG) => {Hwp} [gl [gt]].
  set (Hglobals := {| global_locs := gl; global_initialized_types := gt; |}).
  move => Hwp.
  iMod (heap_alloc_new_blocks_upd with "[Hh Hr Hs]") as "[Hctx Hmt]" => //. {
    rewrite /heap_state_ctx /alloc_meta_ctx /to_alloc_meta_map /alloc_alive_ctx /to_alloc_alive_map !fmap_empty.
    by iFrame.
  }
  rewrite big_sepL2_sep. iDestruct "Hmt" as "[Hmt Hfree]".
  iAssert (|==> [∗ map] k↦qs ∈ fns, fntbl_entry (fn_loc k) qs)%I with "[Hfm]" as ">Hfm". {
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Hfm").
    iIntros "!>" (???) "Hm". rewrite fntbl_entry_eq.
    iExists _. iSplitR; [done|]. by iApply ghost_map_elem_persist.
  }
  iMod (Hwp with "Hmt Hfm") as "Hmains".

  iModIntro. iExists _, (replicate (length thread_mains) (λ _, True%I)), _, _.
  iSplitL "Hctx Hf"; last first. 1: iSplitL "Hmains".
  - rewrite big_sepL2_fmap_l. iApply big_sepL2_replicate_r; [done|]. iApply (big_sepL_impl with "Hmains").
    iIntros "!#" (? main ?); iDestruct 1 as (P) "[Hmain HP]".
    iApply (type_call (typeG0:=HtypeG) with "[-]"). 2: { by iIntros (??) "??". }
    iApply type_val. iApply type_val_context.
    iExists (main @ function_ptr (main_type P))%I => /=. iFrame => /=.
    iApply type_call_fnptr. iIntros "_ !>". iExists () => /=. iFrame. by iIntros (v []) "Hv" => /=.
  - iFrame. iIntros (?? _ _ ?) "_ _ _". iApply fupd_mask_intro_discard => //. iPureIntro. by eauto.
  - by iFrame.
Qed.

(** * Helper functions for using the adequacy lemma *)
Definition fn_lists_to_fns (addrs : list addr) (fns : list function) : gmap addr function :=
  list_to_map (zip addrs fns).

Lemma fn_lists_to_fns_cons `{!refinedcG Σ} addr fn addrs fns :
  length addrs = length fns →
  addr ∉ addrs →
  ([∗ map] k↦qs ∈ fn_lists_to_fns (addr :: addrs) (fn :: fns), fntbl_entry (fn_loc k) qs) -∗
  fntbl_entry (ProvFnPtr, addr) fn ∗ ([∗ map] k↦qs ∈ fn_lists_to_fns addrs fns, fntbl_entry (fn_loc k) qs).
Proof.
  move => Hnotin ?.
  rewrite /fn_lists_to_fns /= big_sepM_insert. { by iIntros "?". }
  apply not_elem_of_list_to_map_1. rewrite fst_zip => //; lia.
Qed.

(** * Tactics for solving conditions in an adequacy proof *)

Ltac adequacy_intro_parameter :=
  repeat lazymatch goal with
         | |- ∀ _ : (), _ => case
         | |- ∀ _ : (_ * _), _ => case
         | |- ∀ _ : _, _ => move => ?
         end.

Ltac adequacy_unfold_equiv :=
  lazymatch goal with
  | |- type_fixpoint _ _ ≡ type_fixpoint _ _ => apply: type_fixpoint_proper; [|move => ??]
  | |- ty_own_val _ _ ≡ ty_own_val _ _ => unfold ty_own_val => /=
  | |-  _ =@{struct_layout} _ => apply: struct_layout_eq
  end.

Ltac adequacy_solve_equiv unfold_tac :=
  first [ eassumption | fast_reflexivity | unfold_type_equiv | adequacy_unfold_equiv | f_contractive | f_equiv' | reflexivity | progress unfold_tac ].

Ltac adequacy_solve_typed_function lemma unfold_tac :=
  iApply typed_function_equiv; [
    done |
    adequacy_intro_parameter => /=; repeat (constructor; [done|]); by constructor |
    | iApply lemma => //; iExists _; repeat iSplit => //];
    adequacy_intro_parameter => /=; eexists eq_refl => /=; split_and!; [..|adequacy_intro_parameter => /=; split_and!];  repeat adequacy_solve_equiv unfold_tac.
