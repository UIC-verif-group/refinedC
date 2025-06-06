From refinedc.typing Require Export type.
From refinedc.typing Require Import programs bytes.
From refinedc.typing Require Import type_options.

Definition introduce_typed_stmt {Σ} `{!typeG Σ} (fn : function) (ls : list loc) (R : val → type → iProp Σ) : iProp Σ :=
  let Q := (subst_stmt (zip (fn.(f_args).*1 ++ fn.(f_local_vars).*1)
                            (val_of_loc <$> ls))) <$> fn.(f_code) in
  typed_stmt (Goto fn.(f_init)) fn ls R Q.
Global Typeclasses Opaque introduce_typed_stmt.
Arguments introduce_typed_stmt : simpl never.

Section introduce_typed_stmt.
  Context `{!typeG Σ}.

  Lemma introduce_typed_stmt_wand R1 R2 fn locs :
    introduce_typed_stmt fn locs R1 -∗
    (∀ v ty, R1 v ty -∗ R2 v ty) -∗
    introduce_typed_stmt fn locs R2.
  Proof.
    rewrite /introduce_typed_stmt. iIntros "HR1 Hwand" (Hlen).
    iApply (wps_wand with "[HR1]"). { by iApply "HR1". }
    iIntros (v) "(%ty & Hty & Hargs & Hret)".
    iExists ty. iFrame. by iApply "Hwand".
  Qed.
End introduce_typed_stmt.

Section function.
  Context `{!typeG Σ} {A : Type}.
  Record fn_ret := FR {
    (* return type (rc::returns) *)
    fr_rty : type;
    (* postcondition (rc::ensures) *)
    fr_R : iProp Σ;
  }.
  Definition mk_FR (rty : type) (R : iProp Σ) := FR rty R.


  (* The specification of a function is given by [A → fn_params].
     The full specification roughly looks like the following:
     ∀ x : A, args ◁ᵥ fp_atys ∗ fp_Pa → ∃ y : fp_rtype, ret ◁ᵥ fr_rty ∗ fr_R
 *)
  Record fn_params := FP {
    (* types of arguments (rc::args) *)
    fp_atys : list type;
    (* precondition (rc::requires) *)
    fp_Pa : iProp Σ;
    (* type of the existential quantifier (rc::exists) *)
    fp_rtype : Type;
    (* return type and postcondition (rc::returns and rc::ensures) *)
    fp_fr: fp_rtype → fn_ret;
  }.

  Definition fn_ret_prop {B} (fr : B → fn_ret) : val → type → iProp Σ :=
    (λ v ty, v ◁ᵥ ty -∗ ∃ x, v ◁ᵥ (fr x).(fr_rty) ∗ (fr x).(fr_R) ∗ True)%I.

  Definition FP_wf {B} (atys : list type) (Pa : iProp Σ) (fr : B → fn_ret)  :=
    FP atys Pa B fr.

  Definition typed_function (fn : function) (fp : A → fn_params) : iProp Σ :=
    (∀ x, ⌜Forall2 (λ (ty : type) '(_, p), ty.(ty_has_op_type) (UntypedOp p) MCNone) (fp x).(fp_atys) (f_args fn)⌝ ∗
      □ ∀ (lsa : vec loc (length (fp x).(fp_atys))) (lsv : vec loc (length fn.(f_local_vars))),
          let Qinit := ([∗list] l;t∈lsa;(fp x).(fp_atys), l ◁ₗ t) ∗
                       ([∗list] l;p∈lsv;fn.(f_local_vars), l ◁ₗ uninit (p.2)) ∗ (fp x).(fp_Pa) in
          Qinit -∗ introduce_typed_stmt fn (lsa ++ lsv) (fn_ret_prop (fp x).(fp_fr))
    )%I.

  Global Instance typed_function_persistent fn fp : Persistent (typed_function fn fp) := _.

  Import EqNotations.
  Lemma typed_function_equiv fn1 fn2 (fp1 fp2 : A → _) :
    fn1 = fn2 →
    (∀ x, Forall2 (λ ty '(_, p), ty_has_op_type ty (UntypedOp p) MCNone) (fp_atys (fp2 x)) (f_args fn2)) →
    (* TODO: replace the following with an equivalenve relation for fn_params? *)
    (∀ x, ∃ Heq : (fp1 x).(fp_rtype) = (fp2 x).(fp_rtype),
          (fp1 x).(fp_atys) ≡ (fp2 x).(fp_atys) ∧
          (fp1 x).(fp_Pa) ≡ (fp2 x).(fp_Pa) ∧
          (∀ y, ((fp1 x).(fp_fr) y).(fr_rty) ≡ ((fp2 x).(fp_fr) (rew [λ x : Type, x] Heq in y)).(fr_rty) ∧
                ((fp1 x).(fp_fr) y).(fr_R) ≡ ((fp2 x).(fp_fr) (rew [λ x : Type, x] Heq in y)).(fr_R))) →
    typed_function fn1 fp1 ⊢ typed_function fn2 fp2.
  Proof.
    iIntros (-> Hly Hfn) "HT".
    rewrite /typed_function.
    iIntros (x). iDestruct ("HT" $! x) as ([Hlen Hall]%Forall2_same_length_lookup) "#HT".
    have [Heq [Hatys [HPa Hret]]] := Hfn x.
    iSplit; [done|].
    rewrite /introduce_typed_stmt.
    iIntros "!>" (lsa lsv) "[Hv Ha] %". rewrite -HPa.
    have [|lsa' Hlsa]:= vec_cast _ lsa (length (fp_atys (fp1 x))). { by rewrite Hatys. }
    iApply (wps_wand with "[Hv Ha]").
    - iSpecialize ("HT" $! lsa' lsv with "[Hv Ha]"); rewrite Hlsa. {
        iFrame. iApply (big_sepL2_impl' with "Hv") => //. 1: by rewrite Hatys.
        move: Hatys => /list_equiv_lookup Hatys.
        iIntros "!>" (k ????? Haty2 ? Haty1) "?".
        have := Hatys k. rewrite Haty1 Haty2=> /(Some_equiv_eq _ _)[?[? [Heql ?]]].
        rewrite -Heql. by simplify_eq.
      }
      iApply "HT". by rewrite -Hlsa.
    - rewrite /typed_stmt_post_cond. iIntros (v).
      iDestruct 1 as (?) "[?[? HR]]". rewrite Hlsa.
      iExists _. iFrame.
      iIntros "Hty". iDestruct ("HR" with "Hty") as (y) "[?[??]]".
      have [-> ->]:= Hret y.
      iExists (rew [λ x : Type, x] Heq in y). iFrame.
  Qed.

  Program Definition function_ptr_type (fp : A → fn_params) (f : loc) : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β l := (∃ fn, ⌜l `has_layout_loc` void*⌝ ∗ l ↦[β] val_of_loc f ∗ fntbl_entry f fn ∗ ▷ typed_function fn fp)%I;
    ty_own_val v := (∃ fn, ⌜v = val_of_loc f⌝  ∗ fntbl_entry f fn ∗ ▷ typed_function fn fp)%I;
  |}.
  Next Obligation. iDestruct 1 as (fn) "[? [H [? ?]]]". iExists _. iFrame. by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (fp f ot mt l ->%is_ptr_ot_layout). by iDestruct 1 as (??) "?". Qed.
  Next Obligation. iIntros (fp f ot mt v ->%is_ptr_ot_layout). by iDestruct 1 as (? ->) "?". Qed.
  Next Obligation. iIntros (fp f ot mt v ?). iDestruct 1 as (??) "(?&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (fp f ot mt v ? ->%is_ptr_ot_layout ?) "?". iDestruct 1 as (? ->) "?". by iFrame. Qed.
  Next Obligation.
    iIntros (fp f v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[%fn [-> ?]]". iPureIntro. naive_solver.
  Qed.

  Definition function_ptr (fp : A → fn_params) : rtype _ :=
    RType (function_ptr_type fp).

  Global Program Instance copyable_function_ptr p fp : Copyable (p @ function_ptr fp).
  Next Obligation.
    iIntros (p fp E ly l ? ->%is_ptr_ot_layout). iDestruct 1 as (fn Hl) "(Hl&?&?)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    iFrame. iModIntro. do 2 iSplit => //. by iIntros "_".
  Qed.

  Lemma type_call_fnptr l v vl tys fp T:
    (([∗ list] v;ty∈vl; tys, v ◁ᵥ ty) -∗ ∃ x,
      ([∗ list] v;ty∈vl; (fp x).(fp_atys), v ◁ᵥ ty) ∗
      (fp x).(fp_Pa) ∗ ∀ v x',
      ((fp x).(fp_fr) x').(fr_R) -∗
      T v ((fp x).(fp_fr) x').(fr_rty))
    ⊢ typed_call v (v ◁ᵥ l @ function_ptr fp) vl tys T.
  Proof.
    iIntros "HT (%fn&->&He&Hfn) Htys" (Φ) "HΦ".
    iDestruct ("HT" with "Htys") as "(%x&Hvl&HPa&Hr)".
    iDestruct ("Hfn" $! x) as "[>%Hl #Hfn]".
    iAssert ⌜Forall2 has_layout_val vl (f_args fn).*2⌝%I as %Hall. {
      iClear "Hfn HPa Hr".
      move: Hl. move: (fp_atys (fp x)) => atys Hl.
      iInduction (fn.(f_args)) as [|[??]] "IH" forall (vl atys Hl).
      { move: Hl => /Forall2_nil_inv_r ->. destruct vl => //=. }
      move: Hl. intros (?&?&Heq&?&->)%Forall2_cons_inv_r.
      destruct vl => //=. iDestruct "Hvl" as "[Hv Hvl]".
      iDestruct ("IH" with "[//] He HΦ Hvl") as %?.
      iDestruct (ty_size_eq with "Hv") as %?; [done|].
      iPureIntro. constructor => //.
    }
    iApply (wp_call with "He") => //. { by apply val_to_of_loc. }
    iIntros "!#" (lsa lsv Hly) "Ha Hv".
    iDestruct (big_sepL2_length with "Ha") as %Hlen1.
    iDestruct (big_sepL2_length with "Hv") as %Hlen2.
    iDestruct (big_sepL2_length with "Hvl") as %Hlen3.
    have [lsa' ?]: (∃ (ls : vec loc (length (fp_atys (fp x)))), lsa = ls) by rewrite -Hlen3 -Hlen1; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.
    have [lsv' ?]: (∃ (ls : vec loc (length (f_local_vars fn))), lsv = ls) by rewrite -Hlen2; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.

    iDestruct ("Hfn" $! lsa' lsv') as "#Hm". iClear "Hfn". unfold introduce_typed_stmt.
    iExists _. iSplitR "Hr HΦ" => /=.
    - iFrame. iApply ("Hm" with "[-]"). 2:{
        iPureIntro. rewrite !length_app. f_equal => //. rewrite Hlen1 Hlen3. by eapply Forall2_length.
      } iClear "Hm". iFrame.
      move: Hlen1 Hly. move: (lsa' : list _) => lsa'' Hlen1 Hly. clear lsa' Hall.
      move: Hlen3 Hl. move: (fp_atys (fp x)) => atys Hlen3 Hl.
      move: Hly Hl. move: (f_args fn) => alys Hly Hl.
      iInduction (vl) as [|v vl] "IH" forall (atys lsa'' alys Hlen1 Hly Hlen3 Hl).
      { destruct atys, lsa'' => //. iSplitR => //. iApply (big_sepL2_mono with "Hv").
        iIntros (?????) => /=. iDestruct 1 as (??) "[%?]".
        iExists _. iFrame. by rewrite Forall_forall. }
      destruct atys, lsa'' => //.
      move: Hl => /(Forall2_cons_inv_l _ _)[[??][?[?[??]]]]; simplify_eq. csimpl in *.
      move: Hly => /(Forall2_cons _ _ _ _)[??].
      iDestruct "Hvl" as "[Hvl ?]".
      iDestruct "Ha" as "[Ha ?]".
      iDestruct (ty_ref with "[] Ha Hvl") as "$"; [done..|].
      by iApply ("IH" with "[] [] [] [] [$] [$]").
    - iIntros (v). iDestruct 1 as (x') "[Hv [Hls HPr]]".
      iDestruct (big_sepL2_app_inv with "Hls") as "[$ $]".
      { rewrite Hlen1 Hlen3. left. by eapply Forall2_length. }
      iDestruct ("HPr" with "Hv") as (?) "[Hty [HR _]]".
      iApply ("HΦ" with "Hty").
      by iApply ("Hr" with "HR").
  Qed.
  Definition type_call_fnptr_inst := [instance type_call_fnptr].
  Global Existing Instance type_call_fnptr_inst.

  Lemma subsume_fnptr_val_ex B v l1 l2 (fnty1 : A → fn_params) fnty2 `{!∀ x, ContainsEx (fnty2 x)} T:
    (∃ x, ⌜l1 = l2 x⌝ ∗ ⌜fnty1 = fnty2 x⌝ ∗ T x)
    ⊢ subsume (v ◁ᵥ l1 @ function_ptr fnty1) (λ x : B, v ◁ᵥ (l2 x) @ function_ptr (fnty2 x)) T.
  Proof. iIntros "(%&->&->&?) ?". iExists _. iFrame. Qed.
  Definition subsume_fnptr_val_ex_inst := [instance subsume_fnptr_val_ex].
  Global Existing Instance subsume_fnptr_val_ex_inst | 5.

  (* TODO: split this in an ex and no_ex variant as for values *)
  Lemma subsume_fnptr_loc B l l1 l2  (fnty1 : A → fn_params) fnty2 T:
    (∃ x, ⌜l1 = l2 x⌝ ∗ ⌜fnty1 = fnty2 x⌝ ∗ T x)
      ⊢ subsume (l ◁ₗ l1 @ function_ptr fnty1) (λ x : B, l ◁ₗ (l2 x)  @ function_ptr (fnty2 x))  T .
  Proof. iIntros "(%&->&->&?) ?". iExists _. iFrame. Qed.
  Definition subsume_fnptr_loc_inst := [instance subsume_fnptr_loc].
  Global Existing Instance subsume_fnptr_loc_inst | 5.
End function.
Arguments fn_ret_prop _ _ _ /.

(* We need start a new section since the following rules use multiple different A. *)
Section function_extra.
  Context `{!typeG Σ}.

  Lemma subsume_fnptr_no_ex A A1 A2 v l1 l2 (fnty1 : A1 → fn_params) (fnty2 : A2 → fn_params)
    `{!Inhabited A1} T:
    subsume (v ◁ᵥ l1 @ function_ptr fnty1) (λ x : A, v ◁ᵥ (l2 x) @ function_ptr fnty2) T :-
      and:
      | drop_spatial;
        ∀ a2,
        (* We need to use an implication here since we don't have
        access to the layouts of the function otherwise. If this is a
        problem, we could also add the argument layouts as part of the
        function pointer type. *)
        exhale ⌜Forall2 (λ ty1 ty2,
                    ∀ p, ty1.(ty_has_op_type) (UntypedOp p) MCNone →
                         ty2.(ty_has_op_type) (UntypedOp p) MCNone)
                  (fnty1 (inhabitant)).(fp_atys) (fnty2 a2).(fp_atys)⌝;
        inhale (fp_Pa (fnty2 a2));
        ls ← iterate: fp_atys (fnty2 a2) with [] {{ ty T ls,
               ∀ l, inhale (l ◁ₗ ty); return T (ls ++ [l]) }};
        ∃ a1,
        exhale ⌜length (fp_atys (fnty1 a1)) = length (fp_atys (fnty2 a2))⌝%I;
        iterate: zip ls (fp_atys (fnty1 a1)) {{ e T, exhale (e.1 ◁ₗ e.2); return T }};
        exhale (fp_Pa (fnty1 a1));
        ∀ ret1 ret_val,
        inhale (ret_val ◁ᵥ fr_rty (fp_fr (fnty1 a1) ret1));
        inhale (fr_R (fp_fr (fnty1 a1) ret1));
        ∃ ret2,
        exhale (ret_val ◁ᵥ fr_rty (fp_fr (fnty2 a2) ret2));
        exhale (fr_R (fp_fr (fnty2 a2) ret2)); done
      | ∃ x, exhale ⌜l1 = l2 x⌝; return T x.
  Proof.
    iIntros "(#Hsub & (%x & -> & HT))".
    iIntros "(%fn & -> & #Hfn & #Htyp_f1)".
    iExists x; iFrame. unfold function_ptr; simpl_type.
    iExists fn; iSplit => //; iFrame "#"; iNext.
    rewrite /typed_function. iIntros (a2).
    iDestruct ("Htyp_f1" $! inhabitant) as "(%Hlayouts1 & _)".
    iDestruct ("Hsub" $! a2) as "{Hsub} (%Hlayouts2 & Hsub)".
    iSplit; [iPureIntro|iModIntro].
    { move: Hlayouts1 Hlayouts2 => /Forall2_same_length_lookup[Hlen1 Hlookup1] /Forall2_same_length_lookup[Hlen2 Hlookup2] .
      apply Forall2_same_length_lookup. split; [lia|].
      move => i ty [name ly] ? Hlookup.
      have Hlen := lookup_lt_Some _ _ _ Hlookup.
      move: Hlen; rewrite -Hlen1 => /(lookup_lt_is_Some_2 _ _)[ty' Hty'].
      apply: Hlookup2  => //.
      by apply (Hlookup1 i _ (name, ly)).
    }
    iIntros (lsa lsv) "(Hargs & Hlocals & HP)".
    iSpecialize ("Hsub" with "HP").
    pose (INV := (λ i ls', ⌜ls' = take i lsa⌝ ∗
      [∗ list] l;t ∈ drop i lsa;drop i (fp_atys (fnty2 a2)), l ◁ₗ t)%I).
    iDestruct (iterate_elim1 INV with "Hsub [Hargs] [#]") as (ls') "((-> & ?) & (%a1 & %Hlen & Hsub))"; unfold INV; clear INV.
    { rewrite take_0 !drop_0. by iFrame. }
    { iIntros "!>" (i x2 ? ls' ?). iIntros "[-> Hinv] HT".
      have [|??]:= lookup_lt_is_Some_2 lsa i. {
        rewrite length_vec_to_list. by apply: lookup_lt_Some. }
      erewrite drop_S; [|done]. erewrite (drop_S _ _ i); [|done] => /=.
      iDestruct "Hinv" as "[Hl $]". iDestruct ("HT" with "[$]") as "HT". iExists _. iFrame.
      by erewrite take_S_r.
    }
    pose (INV := (λ i,
      [∗ list] l;t ∈ take i lsa;take i (fp_atys (fnty1 a1)), l ◁ₗ t)%I).
    iDestruct (iterate_elim0 INV with "Hsub [] [#]") as "[Hinv [Hpre1 Hsub]]"; unfold INV; clear INV.
    { by rewrite !take_0. } {
      iIntros "!>" (i ? ? (?&?&?&Hvs&?)%lookup_zip_with_Some); simplify_eq/=.
      iIntros "Hinv [? $]". rewrite lookup_take in Hvs.
      2: { rewrite -Hlen. by apply: lookup_lt_Some. }
      erewrite take_S_r; [|done]. erewrite take_S_r; [|done].
      rewrite big_sepL2_snoc. iFrame.
    }
    rewrite -Hlen in lsa *.
    iDestruct ("Htyp_f1" $! a1) as "{Htyp_f1} (_ & #Htyp_f1)".
    iSpecialize ("Htyp_f1" $! lsa lsv).
    rewrite !length_zip_with !take_ge ?length_vec_to_list; [|lia..].
    iSpecialize ("Htyp_f1" with "[$]").
    iApply (introduce_typed_stmt_wand with "Htyp_f1").
    iIntros (v ty) "Hret1 Hty" => /=.
    iDestruct ("Hret1" with "Hty") as "(%ret1 & Hty1 & Hpost1 & _)".
    iDestruct ("Hsub" $! ret1 v with "Hty1 Hpost1") as "(%ret2 & Hty2 & Hpost2 & _)".
    iExists ret2; iFrame.
  Qed.
  Definition subsume_fnptr_no_ex_inst := [instance subsume_fnptr_no_ex].
  Global Existing Instance subsume_fnptr_no_ex_inst | 10.

End function_extra.

Notation "'fn(∀' x ':' A ';' T1 ',' .. ',' TN ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((fun x => FP_wf (B:=B) (@cons type T1%I .. (@cons type TN%I (@nil type)) ..) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  T1 ','  .. ','  TN ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.

Notation "'fn(∀' x ':' A ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((λ x, FP_wf (B:=B) (@nil type) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.


Global Typeclasses Opaque typed_function.
Global Typeclasses Opaque function_ptr_type function_ptr.

Section inline_function.
  Context `{!typeG Σ} {A : Type}.

  Program Definition inline_function_ptr_type (fn : function) (f : loc) : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β l := (⌜l `has_layout_loc` void*⌝ ∗ l ↦[β] val_of_loc f ∗ fntbl_entry f fn)%I;
    ty_own_val v := (⌜v = val_of_loc f⌝ ∗ fntbl_entry f fn)%I;
  |}.
  Next Obligation. iDestruct 1 as "[? [H ?]]". iFrame. by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (fn f ot mt l ->%is_ptr_ot_layout). by iDestruct 1 as (?) "?". Qed.
  Next Obligation. iIntros (fn f ot mt v ->%is_ptr_ot_layout). by iDestruct 1 as (->) "?". Qed.
  Next Obligation. iIntros (fn f ot mt v ?). iDestruct 1 as (?) "(?&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (fn f ot mt l v ->%is_ptr_ot_layout ?) "?". iDestruct 1 as (->) "?". by iFrame. Qed.
  Next Obligation.
    iIntros (fn f v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[-> ?]". iPureIntro. naive_solver.
  Qed.

  Definition inline_function_ptr (fn : function) : rtype _ :=
    RType (inline_function_ptr_type fn).

  Global Program Instance copyable_inline_function_ptr p fn : Copyable (p @ inline_function_ptr fn).
  Next Obligation.
    iIntros (p fn E l ly ? ->%is_ptr_ot_layout). iDestruct 1 as (Hl) "(Hl&?)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit; [done|].
    by iIntros "_".
  Qed.

  Lemma type_call_inline_fnptr l v vl tys fn T:
    (⌜Forall2 (λ ty '(_, p), ty.(ty_has_op_type) (UntypedOp p) MCNone) tys (f_args fn)⌝ ∗
      foldr (λ '(v, ty) T lsa, ∀ l, l ◁ₗ ty -∗ T (lsa ++ [l]))
      (λ lsa, foldr (λ ly T lsv, ∀ l, l ◁ₗ uninit ly -∗ T (lsv ++ [l]))
                    (λ lsv,
                     introduce_typed_stmt fn (lsa ++ lsv) T)
                    fn.(f_local_vars).*2 [])
      (zip vl tys)
      [])
    ⊢ typed_call v (v ◁ᵥ l @ inline_function_ptr fn) vl tys T.
  Proof.
    iIntros "[%Hl HT] (->&Hfn) Htys" (Φ) "HΦ".
    iAssert ⌜Forall2 has_layout_val vl (f_args fn).*2⌝%I as %Hall. {
      iClear "Hfn HT HΦ".
      iInduction (fn.(f_args)) as [|[??]] "IH" forall (vl tys Hl).
      { move: Hl => /Forall2_nil_inv_r ->. destruct vl => //=. }
      move: Hl. intros (?&?&Heq&?&->)%Forall2_cons_inv_r.
      destruct vl => //=. iDestruct "Htys" as "[Hv Hvl]".
      iDestruct ("IH" with "[//] Hvl") as %?.
      iDestruct (ty_size_eq with "Hv") as %?; [done|].
      iPureIntro. constructor => //.
    }
    iApply (wp_call with "Hfn") => //. { by apply val_to_of_loc. }
    iIntros "!#" (lsa lsv Hly) "Ha Hv".
    iAssert ⌜length lsa = length (f_args fn)⌝%I as %Hlen1. {
      iDestruct (big_sepL2_length with "Ha") as %->.
      iPureIntro. move: Hall => /Forall2_length ->. by rewrite length_fmap.
    }
    iDestruct (big_sepL2_length with "Hv") as %Hlen2.
    move: Hl Hall Hly. move: {1 2 3}(f_args fn) => alys Hl Hall Hly.
    have : lsa = [] ++ lsa by done.
    move: {1 5}([]) => lsr.
    move: {1 3 4}(lsa) Hly => lsa' Hly Hr.
    iInduction vl as [|v vl] "IH" forall (tys lsa' alys lsr Hr Hly Hl Hall) => /=. 2: {
       iDestruct (big_sepL2_cons_inv_r with "Ha") as (???) "[Hmt ?]".
       iDestruct (big_sepL2_cons_inv_l with "Htys") as (???) "[Hv' ?]". simplify_eq/=.
       move: Hl => /(Forall2_cons_inv_l _ _ _ _)[[??][?[?[??]]]]. simplify_eq/=.
       move: Hly => /(Forall2_cons _ _ _ _)[??].
       move: Hall => /(Forall2_cons _ _ _ _)[??].
       iDestruct (ty_ref with "[] Hmt Hv'") as "Hl"; [done..|].
       iSpecialize ("HT" with "Hl").
       iApply ("IH" with "[%] [//] [//] [//] HT [$] [$] [$] [$]").
       by rewrite -app_assoc/=.
    }
    iDestruct (big_sepL2_nil_inv_r with "Ha") as %?. subst.
    move: {1 2}(f_local_vars fn) => vlys.
    have : lsv = [] ++ lsv by done.
    move: {1 3}([]) => lvr.
    move: {2 3}(lsv) => lsv' Hr.
    iInduction lsv' as [|lv lsv'] "IH" forall (vlys lvr Hr) => /=. 2: {
       iDestruct (big_sepL2_cons_inv_l with "Hv") as (???) "[(%x&%&%&Hl) ?]". simplify_eq/=.
       iSpecialize ("HT" $! lv with "[Hl]"). { iExists _. iFrame. iPureIntro. split_and! => //. by apply: Forall_true. }
       iApply ("IH" with "[%] HT [$] [$] [$] [$]").
       by rewrite -app_assoc/=.
    }
    iDestruct (big_sepL2_nil_inv_l with "Hv") as %?. subst.
    simplify_eq/=.
    rewrite /introduce_typed_stmt !right_id_L.
    iExists _. iSplitR "HΦ" => /=.
    - iFrame. iApply ("HT" with "[-]"). iPureIntro. rewrite !length_app -Hlen1 -Hlen2 !length_app/=. lia.
    - iIntros (v). iDestruct 1 as (x') "[Hv [Hls HPr]]".
      iDestruct (big_sepL2_app_inv with "Hls") as "[$ $]".
      { left. by rewrite -Hlen1 right_id_L.  }
      by iApply ("HΦ" with "Hv HPr").
  Qed.
  Definition type_call_inline_fnptr_inst := [instance type_call_inline_fnptr].
  Global Existing Instance type_call_inline_fnptr_inst.
End inline_function.

Global Typeclasses Opaque inline_function_ptr_type inline_function_ptr.

(*** Tests *)
Section test.
  Context  `{!typeG Σ}.

  Local Definition test_fn := fn(∀ () : (); (uninit size_t); True) → ∃ () : (), void; True.
  Local Definition test_fn2 := fn(∀ () : (); True) → ∃ () : (), void; True.
  Local Definition test_fn3 := fn(∀ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z; uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t; True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True) → ∃ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z, uninit size_t; True%I.

  Goal ∀ (l : loc) fn, l ◁ᵥ l @ function_ptr test_fn2 -∗ typed_function fn test_fn.
  Abort.
End test.
