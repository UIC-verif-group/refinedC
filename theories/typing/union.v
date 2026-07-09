From refinedc.typing Require Export type.
From refinedc.typing Require Import programs bytes padded int struct.
From refinedc.typing Require Import type_options.

Section union.
  Context `{!typeG Σ}.

  (*** active_union *)
  Program Definition active_union (ul : union_layout) (f : var_name) (ty : type) : type := {|
    ty_own β l := (∃ ly, ⌜layout_of_union_member f ul = Some ly⌝ ∗ l ◁ₗ{β} (padded ty ly ul));
    ty_has_op_type _ _ := False%type;
    ty_own_val _ := True;
  |}%I.
  Solve Obligations with try done.
  Next Obligation.
    iIntros (ul f ty l E ?). iDestruct 1 as (ly ?) "Hp". iExists _. iSplitR => //. by iApply ty_share.
  Qed.

  Lemma type_place_uninit_union K β ul n l T:
    (∃ ly, ⌜layout_of_union_member n ul = Some ly⌝ ∗
    typed_place (GetMemberUnionPCtx ul n :: K) l β (active_union ul n (uninit ly)) T)
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l β (uninit ul) T.
  Proof.
    iDestruct 1 as (ly Hly) "HP".
    iIntros (Φ) "Hs HΦ" => /=.
    iApply ("HP" with "[Hs] HΦ").
    iExists _. iSplit => //.
    iApply (apply_subsume_place_true with "Hs"). iApply subsume_uninit_padded.
    iExists tt. iSplit => //. iPureIntro.
    split; apply max_list_elem_of_le; apply list_elem_of_fmap_2; by apply: layout_of_union_member_in_ul.
  Qed.
  Definition type_place_uninit_union_inst := [instance type_place_uninit_union].
  Global Existing Instance type_place_uninit_union_inst.

  Lemma type_place_active_union K β ul n l ty T:
    typed_place K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, active_union ul n (typ t)))
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l β (active_union ul n ty) T.
  Proof.
    iIntros "HP" (Φ) "Hs HΦ" => /=.
    iDestruct "Hs" as (ly ?) "Hpad".
    rewrite /padded. iDestruct "Hpad" as (??) "[Hb [Hty Hpad]]".
    iApply (wp_get_member_union with "[#//]"). 1: by apply val_to_of_loc.
    iExists _. iSplit => //.
    iApply ("HP" with "[Hty]"). 1: by rewrite /GetMemberUnionLoc.
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    iExists _. iSplitR => //. rewrite /padded/GetMemberUnionLoc. by iFrame.
  Qed.
  Definition type_place_active_union_inst := [instance type_place_active_union].
  Global Existing Instance type_place_active_union_inst.

End union.
  (*** tagged union *)
  (*** tunion_info *)
Record tunion_info `{!typeG Σ} {A : Type} := {
  ti_base_layout : struct_layout;
  ti_tag_field_name : string;
  ti_union_field_name : string;
  ti_union_layout : union_layout;
  ti_tag : A → nat;
  ti_type : A → type;

  ti_base_layout_members : ti_base_layout.(sl_members) = [(Some ti_tag_field_name, it_layout size_t); (Some ti_union_field_name, ul_layout ti_union_layout)];
  ti_tags_valid r : is_Some (ti_union_layout.(ul_members) !! ti_tag r);
}.
Arguments tunion_info {_ _} _.

Section union.
  Context `{!typeG Σ} {A : Type}.

  Definition ti_member (ti : tunion_info A) (r : A) :=
    (default ("", void_layout) (ti.(ti_union_layout).(ul_members) !! ti.(ti_tag) r)).

  Lemma index_of_ti_member ti (x : A):
    index_of_union (ti_member ti x).1 (ti_union_layout ti) = Some (ti.(ti_tag) x).
  Proof.
    rewrite /ti_member.
    destruct (ti_tags_valid ti x) as [[n ly] Heq]. rewrite Heq /=.
    by apply: index_of_union_lookup.
  Qed.

  Lemma layout_of_member_ti_member ti x ly:
    layout_of_union_member (ti_member ti x).1 (ti_union_layout ti) = Some ly →
    ly = (ti_member ti x).2.
  Proof.
    rewrite /layout_of_union_member index_of_ti_member/=/ti_member.
    by destruct (ul_members (ti_union_layout ti) !! ti_tag ti x) => //= [[]].
  Qed.

  (*** tag *)
  Program Definition tunion_tag (ti : tunion_info A) (x : A) : type := {|
    ty_has_op_type ot mt := is_int_ot ot size_t;
    ty_own β l := l ◁ₗ{β}ti.(ti_tag) x @ int size_t;
    ty_own_val v := v ◁ᵥ ti.(ti_tag) x @ int size_t;
  |}%I.
  Next Obligation. iIntros (?????). by iApply ty_share. Qed.
  Next Obligation. iIntros (?????->%is_int_ot_layout) "Hl". by iApply (ty_aligned _ (IntOp _) MCNone with "Hl").  Qed.
  Next Obligation. iIntros (?????->%is_int_ot_layout) "Hv". by iDestruct (ty_size_eq _ (IntOp _) MCNone with "Hv") as %?. Qed.
  Next Obligation. iIntros (??????) => /=. by apply: ty_deref. Qed.
  Next Obligation. iIntros (??????->%is_int_ot_layout?) "Hl Hv" => /=. by iApply (ty_ref _ (IntOp _) MCNone with "[] Hl Hv"). Qed.
  Next Obligation. iIntros (???????) "Hv" => /=. by iApply (ty_memcast_compat (_ @ int size_t) with "[Hv]"). Qed.

  Global Program Instance copyable_tunion_tag ti x : Copyable (tunion_tag ti x).
  Next Obligation. move => *. unfold tunion_tag; simpl_type. apply _. Qed.
  Next Obligation.
    rewrite /ty_own/ty_own_val/= => ??????/is_int_ot_layout->/=.
    iIntros "Hl". iMod (copy_shr_acc _ (IntOp _) with "Hl") as (???) "Hc" => //.
    iSplitR => //. iExists _, _. by iFrame.
  Qed.

  Lemma subsume_int_tunion_tag B M ti x (n : Z) l β T:
    (∃ y, ⌜ti.(ti_tag) (x y) =@{Z} n⌝ ∗ T y)
    ⊢ subsume (l ◁ₗ{β} n @ int size_t) M (λ y : B, l ◁ₗ{β} tunion_tag ti (x y)) T.
  Proof. iIntros "[% [<- ?]] ?". iModIntro. iFrame. Qed.
  Definition subsume_int_tunion_tag_inst := [instance subsume_int_tunion_tag].
  Global Existing Instance subsume_int_tunion_tag_inst.

  Lemma subsume_tunion_tag M B ti x1 x2 l β T:
    (∃ y, ⌜ti.(ti_tag) x1 = ti.(ti_tag) (x2 y)⌝ ∗ T y)
    ⊢ subsume (l ◁ₗ{β} tunion_tag ti x1) M (λ y : B, l ◁ₗ{β} tunion_tag ti (x2 y)) T.
  Proof. rewrite /ty_own/=. iIntros "[% [-> ?]] ? !>". iExists _. iFrame. Qed.
  Definition subsume_tunion_tag_inst := [instance subsume_tunion_tag].
  Global Existing Instance subsume_tunion_tag_inst.

  Inductive trace_union :=
  | TraceUnion (info : tunion_info A).

  Lemma type_binop_tunion_tag_int op it ti x v1 n v2 T:
    case_destruct x (λ x' _,
        li_trace (TraceUnion ti, x') (typed_bin_op v1 (v1 ◁ᵥ ti.(ti_tag) x' @ int size_t) v2 (v2 ◁ᵥ n @ int it) op (IntOp size_t) (IntOp it) T))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ tunion_tag ti x) v2 (v2 ◁ᵥ n @ int it) op (IntOp size_t) (IntOp it) T.
  Proof. iDestruct 1 as (?) "?". by rewrite /(ty_own_val (tunion_tag _ _))/=. Qed.
  Definition type_binop_tunion_tag_int_eq_inst := [instance type_binop_tunion_tag_int (EqOp i32)].
  Global Existing Instance type_binop_tunion_tag_int_eq_inst.
  Definition type_binop_tunion_tag_int_ne_inst := [instance type_binop_tunion_tag_int (NeOp i32)].
  Global Existing Instance type_binop_tunion_tag_int_ne_inst.
  Definition type_binop_tunion_tag_int_gt_inst := [instance type_binop_tunion_tag_int (GtOp i32)].
  Global Existing Instance type_binop_tunion_tag_int_gt_inst.
  Definition type_binop_tunion_tag_int_lt_inst := [instance type_binop_tunion_tag_int (LtOp i32)].
  Global Existing Instance type_binop_tunion_tag_int_lt_inst.
  Definition type_binop_tunion_tag_int_ge_inst := [instance type_binop_tunion_tag_int (GeOp i32)].
  Global Existing Instance type_binop_tunion_tag_int_ge_inst.
  Definition type_binop_tunion_tag_int_le_inst := [instance type_binop_tunion_tag_int (LeOp i32)].
  Global Existing Instance type_binop_tunion_tag_int_le_inst.


  (*** variant *)
  Program Definition variant (ti : tunion_info A) (x : A) (ty : type) : type := {|
    ty_has_op_type ot mt := ot = UntypedOp ti.(ti_union_layout) ∧ ty.(ty_has_op_type) (UntypedOp (ti_member ti x).2) MCNone;
     ty_own β l := (l ◁ₗ{β} (padded ty (ti_member ti x).2 (ul_layout ti.(ti_union_layout))))%I;
    ty_own_val v := (v ◁ᵥ (padded ty (ti_member ti x).2 (ul_layout ti.(ti_union_layout))))%I;
  |}.
  Next Obligation. iIntros (??????). by iApply ty_share. Qed.
  Next Obligation. iIntros (???????) "Hv". by iDestruct (ty_aligned _ _ _ with "Hv") as "$".  Qed.
  Next Obligation. iIntros (???????) "Hv". by iDestruct (ty_size_eq with "Hv") as %?. Qed.
  Next Obligation. iIntros (???????) => /=. by apply: ty_deref. Qed.
  Next Obligation. iIntros (?????????) "Hl Hv" => /=. by iApply (ty_ref with "[] Hl Hv"). Qed.
  Next Obligation. iIntros (????????) "Hv". by iApply (ty_memcast_compat with "Hv"). Qed.

  Lemma subsume_active_union_variant B M ti ul x l β ty1 ty2 n T:
    (l at_union{ul}ₗ n ◁ₗ{β} ty1 -∗
      ‖M‖ ∃ y, ⌜ti.(ti_union_layout) = ul⌝ ∗ ⌜(ti_member ti (x y)).1 = n⌝ ∗
            (l at_union{ul}ₗ n ◁ₗ{β} ty2 y) ∗ T y)
    ⊢ subsume (l ◁ₗ{β} active_union ul n ty1) M (λ y : B, l ◁ₗ{β} variant ti (x y) (ty2 y)) T.
  Proof.
    iIntros "HT". iDestruct 1 as (ly Hly) "Hu".
    iDestruct (padded_focus with "Hu") as "[Hl Hpad]".
    rewrite /GetMemberUnionLoc/=. iMod ("HT" with "[$]") as (? <- <-) "[??]".
    iDestruct ("Hpad" with "[$]") as "?". iModIntro. iFrame.
    move: Hly => /layout_of_member_ti_member ->. done.
  Qed.
  Definition subsume_active_union_variant_inst := [instance subsume_active_union_variant].
  Global Existing Instance subsume_active_union_variant_inst.

  Lemma subsume_variant_variant B M ti x1 x2 l β ty1 ty2 T:
    (l at_union{ti.(ti_union_layout)}ₗ (ti_member ti x1).1 ◁ₗ{β} ty1 -∗
      ‖M‖ ∃ y, ⌜ti.(ti_tag) x1 = ti.(ti_tag) (x2 y)⌝ ∗
      l at_union{ti.(ti_union_layout)}ₗ (ti_member ti x1).1 ◁ₗ{β} (ty2 y) ∗ T y)
    ⊢ subsume (l ◁ₗ{β} variant ti x1 ty1) M (λ y : B, l ◁ₗ{β} variant ti (x2 y) (ty2 y)) T.
  Proof.
    iIntros "HT". rewrite !/(ty_own (variant _ _ _))/=/ti_member.
    iIntros "Hpad". iDestruct (padded_focus with "Hpad") as "[Hl Hpad]".
    iMod ("HT" with "Hl") as (? Heq) "[??]". iModIntro. iFrame.
    rewrite Heq. by iApply "Hpad".
  Qed.
  Definition subsume_variant_variant_inst := [instance subsume_variant_variant].
  Global Existing Instance subsume_variant_variant_inst.

  Lemma type_place_variant K β ul n l ty ti x {Heq: TCEq (ti_member ti x).1 n} T :
    ⌜ul = ti.(ti_union_layout)⌝ ∗
     typed_place K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, variant ti x (typ t)))
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l β (variant ti x ty) T.
  Proof.
    move: Heq => /TCEq_eq <-.
    iIntros "[-> HP]" (Φ) "Hs HΦ" => /=.
    rewrite {2}/variant /padded/=. iDestruct "Hs" as (??) "[Hb [Hty Hpad]]".
    iApply (wp_get_member_union with "[#//]"). 1: by apply val_to_of_loc.
    iExists _. iSplit => //.
    iApply ("HP" with "[Hty]"). 1: by rewrite /GetMemberUnionLoc.
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    rewrite /variant/padded/GetMemberUnionLoc/=. iSplit => //. by iFrame.
  Qed.
  Definition type_place_variant_inst := [instance type_place_variant].
  Global Existing Instance type_place_variant_inst | 20.

  Lemma type_place_variant_neq K ul n l ty ti x T :
    (⌜ul = ti.(ti_union_layout)⌝ ∗ ⌜ty.(ty_has_op_type) (UntypedOp (ti_member ti x).2) MCNone⌝ ∗ ∀ v, v ◁ᵥ ty -∗ typed_place (GetMemberUnionPCtx ul n :: K) l Own (uninit ul) T)
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l Own (variant ti x ty) T.
  Proof.
    iIntros "[-> [% HP]]". iApply (typed_place_subsume _ _ _ (uninit (ti_union_layout ti))).
    iApply subsume_padded_uninit. iSplit; [done|]. iIntros (v) "Hv $". iExists tt.
    by iApply "HP".
  Qed.
  Definition type_place_variant_neq_inst := [instance type_place_variant_neq].
  Global Existing Instance type_place_variant_neq_inst | 50.
End union.

Section tunion.
  Context `{!typeG Σ} {A : Type}.
  (*** tunion *)
  (* TODO: extract the inner type to a separate definition and make it typeclasses opaque. *)
  Program Definition tunion (ti : tunion_info A) : rtype A := {|
    rty r := {|
      ty_has_op_type :=
        is_struct_ot ti.(ti_base_layout) [tunion_tag ti r; variant ti r (ti.(ti_type) r)];
      ty_own β l := l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti r;
         variant ti r (ti.(ti_type) r)
      ];
      ty_own_val v := ty_own_val (struct ti.(ti_base_layout) [
         tunion_tag ti r;
         variant ti r (ti.(ti_type) r)
   ]) v;
   |}%I |}.
  Next Obligation. iIntros (?????). by apply ty_share. Qed.
  Next Obligation. iIntros (??????) "Hl". by iApply (ty_aligned with "Hl"). Qed.
  Next Obligation. iIntros (??????) "Hv". by iApply (ty_size_eq with "Hv"). Qed.
  Next Obligation. iIntros (??????) "Hl". by iApply (ty_deref with "Hl"). Qed.
  Next Obligation. iIntros (????????) "Hl Hv". by iApply (ty_ref with "[] Hl Hv"). Qed.
  Next Obligation. move => ???????. by apply ty_memcast_compat. Qed.

  Lemma simplify_hyp_tunion ti x l β M T:
    (l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ] -∗ ‖M‖ T)
    ⊢ simplify_hyp (l◁ₗ{β} x @ tunion ti) M T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simplify_hyp_tunion_inst := [instance simplify_hyp_tunion with 0%N].
  Global Existing Instance simplify_hyp_tunion_inst.

  Lemma simplify_goal_tunion ti x l β M T:
    l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ] ∗ T
    ⊢ simplify_goal M (l◁ₗ{β} x @ tunion ti) T.
  Proof. by iIntros "[$ $] !>". Qed.
  Definition simplify_goal_tunion_inst := [instance simplify_goal_tunion with 0%N].
  Global Existing Instance simplify_goal_tunion_inst.

End tunion.

Global Typeclasses Opaque active_union variant tunion tunion_tag.
