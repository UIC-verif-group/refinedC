From refinedc.typing Require Export type.
From refinedc.typing Require Import programs singleton optional constrained exist.
From refinedc.typing Require Import type_options.

Section tyfold.
  Context `{!typeG Σ}.

  Program Definition tyfold_type (tys : list (type → type)) (base : type) (ls : list loc) : type := {|
    ty_own β l := ⌜length ls = length tys⌝ ∗
            ([∗ list] i ↦ ty ∈ tys, ∃ l1 l2, ⌜(l::ls) !! i = Some l1⌝ ∗ ⌜ls !! i = Some l2⌝ ∗
           l1 ◁ₗ{β} ty (place l2)) ∗ (default l (last ls)) ◁ₗ{β} base;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ := True;
  |}%I.
  Solve Obligations with try done.
  Next Obligation.
    iIntros (tys base ls l E ?). iDestruct 1 as (Hlen) "(Htys&Hb)".
    iMod (ty_share with "Hb") as "$" => //. iSplitR => //.
    iInduction (tys) as [|ty tys] "IH" forall (l ls Hlen) => //.
    destruct ls as [|l' ls] => //=. move: Hlen => /= [Hlen].
    iDestruct "Htys" as "[Hty Htys]". iDestruct "Hty" as (l1 l2 [=->] [=->]) "Hty".
    iMod (ty_share with "Hty") as "Hty" => //. iSplitL "Hty". 1: iExists _, _; by iFrame.
    by iApply "IH".
  Qed.

  Definition tyfold (tys : list (type → type)) (base : type) : rtype _ :=
    RType (tyfold_type tys base).

  Local Typeclasses Transparent own_constrained persistent_own_constraint.
  Lemma simplify_hyp_place_tyfold_optional l β ls tys b T:
    (l ◁ₗ{β} (maybe2 cons tys) @ optionalO (λ '(ty, tys), tyexists (λ l2, tyexists (λ ls2,
       constrained (
       own_constrained (tyown_constraint l2 (ls2 @ tyfold tys b)) (ty (place l2))) (⌜ls = l2::ls2⌝)))) b -∗ T)
    ⊢ simplify_hyp (l◁ₗ{β} ls @ tyfold tys b) T.
  Proof.
    iIntros "HT Hl". iApply "HT". iDestruct "Hl" as (Hlen) "[Htys Hb]".
    destruct tys as [|ty tys], ls as [ |l' ls] => //=.
    iDestruct "Htys" as "[H1 Hty2]". iDestruct "H1" as (l1 l2 ??) "H1". simplify_eq.
    iExists l2. rewrite tyexists_eq. iExists ls. rewrite tyexists_eq. iSplit => //.
    iSplitL "H1" => //=. rewrite /tyown_constraint. iSplit => //. iFrame.
    iStopProof. f_equiv. destruct ls =>//=. by apply default_last_cons.
  Qed.
  Definition simplify_hyp_place_tyfold_optional_inst :=
    [instance simplify_hyp_place_tyfold_optional with 50%N].
  Global Existing Instance simplify_hyp_place_tyfold_optional_inst.

  Lemma simplify_goal_place_tyfold_nil l β ls b T:
    ⌜ls = []⌝ ∗ l ◁ₗ{β} b ∗ T ⊢ simplify_goal (l◁ₗ{β} ls @ tyfold [] b) T.
  Proof. iIntros "[-> [Hl $]]". repeat iSplit => //. Qed.
  Definition simplify_goal_place_tyfold_nil_inst := [instance simplify_goal_place_tyfold_nil with 0%N].
  Global Existing Instance simplify_goal_place_tyfold_nil_inst.

  Lemma simplify_goal_place_tyfold_cons l β ls ty tys b T:
    (∃ l2 ls2, ⌜ls = l2::ls2⌝ ∗ l ◁ₗ{β} ty (place l2) ∗ l2 ◁ₗ{β} ls2 @ tyfold tys b ∗ T)
    ⊢ simplify_goal (l◁ₗ{β} ls @ tyfold (ty :: tys) b) T.
  Proof.
    iDestruct 1 as (l2 ls2 ->) "[Hl [[% [Htys Hb]] $]]".
    iSplit => /=. 1: by iPureIntro; f_equal. iFrame.
    iSplitR "Hb"; first by eauto with iFrame.
    iStopProof. f_equiv. destruct ls2 =>//=. by apply default_last_cons.
  Qed.
  Definition simplify_goal_place_tyfold_cons_inst := [instance simplify_goal_place_tyfold_cons with 0%N].
  Global Existing Instance simplify_goal_place_tyfold_cons_inst.

  Lemma subsume_tyfold_eq A l β ls1 ls2 tys b1 b2 T :
    (default l (last ls1) ◁ₗ{β} b1 -∗ ∃ x, ⌜ls1 = ls2 x⌝ ∗ (default l (last ls1) ◁ₗ{β} b2 x) ∗ T x)
    ⊢ subsume (l ◁ₗ{β} ls1 @ tyfold tys b1) (λ x : A, l ◁ₗ{β} (ls2 x) @ tyfold tys (b2 x)) T.
  Proof.
    iIntros "HT". iDestruct 1 as (?) "[? Hb]". iDestruct ("HT" with "Hb") as (? ->) "[? ?]".
    iExists _. by iFrame.
  Qed.
  Definition subsume_tyfold_eq_inst := [instance subsume_tyfold_eq].
  Global Existing Instance subsume_tyfold_eq_inst.

  Lemma subsume_tyfold_snoc A B l β f ls1 ls2 tys (ty : B → A) b1 b2 T :
    (default l (last ls1) ◁ₗ{β} b1 -∗ ∃ x l2, ⌜ls2 x = ls1 ++ [l2]⌝ ∗
         default l (last ls1) ◁ₗ{β} f (ty x) (place l2) ∗ l2 ◁ₗ{β} (b2 x) ∗ T x)
    ⊢ subsume (l ◁ₗ{β} ls1 @ tyfold (f <$> tys) b1)
        (λ x : B, l ◁ₗ{β} (ls2 x) @ tyfold (f <$> (tys ++ [ty x])) (b2 x)) T.
  Proof.
    iIntros "HT". iDestruct 1 as (Hlen) "(Htys&Hb)".
    iDestruct ("HT" with "Hb") as (?? Heq) "[?[??]]". iExists _. iFrame.
    rewrite fmap_app. rewrite Heq. iSplit.
    { iPureIntro. by rewrite !length_app Hlen length_fmap. }
    rewrite last_snoc /=. iFrame. iSplitL "Htys" => /=.
    - iApply (big_sepL_mono with "Htys") => k y /(lookup_lt_Some _ _ _). rewrite -Hlen => Hl /=.
      rewrite ?app_comm_cons !lookup_app_l//=. lia.
    - iSplit => //. rewrite Nat.add_0_r !lookup_app_r -?Hlen ?Nat.sub_diag /=; try lia.
      iSplit => //. iPureIntro. rewrite ?app_comm_cons lookup_app_l /=; try lia.
      by apply list_lookup_length_default_last.
  Qed.
  Definition subsume_tyfold_snoc_inst := [instance subsume_tyfold_snoc].
  Global Existing Instance subsume_tyfold_snoc_inst.
End tyfold.
Global Typeclasses Opaque tyfold_type tyfold.
