From stdpp Require Import fin_maps.
From caesium Require Export notation.
Set Default Proof Using "Type".

Module W.
(*** Expressions *)
Section expr.
Local Unset Elimination Schemes.
Inductive expr :=
| Var (x : var_name)
| Loc (l : loc)
| Val (v : val)
| UnOp (op : un_op) (ot : op_type) (e : expr)
| BinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| CopyAllocId (ot1 : op_type) (e1 e2 : expr)
| Deref (o : order) (ot : op_type) (memcast : bool) (e : expr)
| CAS (ot : op_type) (e1 e2 e3 : expr)
| Call (f : expr) (args : list expr)
| Concat (es : list expr)
| IfE (op : op_type) (e1 e2 e3 : expr)
| Alloc (ly : layout) (e : expr)
| SkipE (e : expr)
| StuckE
(* new constructors *)
| LogicalAnd (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr)
| LogicalOr (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr)
| Use (o : order) (ot : op_type) (memcast : bool) (e : expr)
| AddrOf (e : expr)
| LValue (e : expr)
| GetMember (e : expr) (s : struct_layout) (m : var_name)
| GetMemberUnion (e : expr) (ul : union_layout) (m : var_name)
| OffsetOf (s : struct_layout) (m : var_name)
| OffsetOfUnion (ul : union_layout) (m : var_name)
| AnnotExpr (n : nat) {A} (a : A) (e : expr)
| LocInfoE (a : location_info) (e : expr)
| StructInit (ly : struct_layout) (fs : list (string * expr))
| MacroE (m : list lang.expr → lang.expr) (es : list expr) (wf : MacroWfSubst m)
(* for opaque expressions*)
| Expr (e : lang.expr)
.
End expr.

Lemma expr_ind (P : expr → Prop) :
  (∀ (x : var_name), P (Var x)) →
  (∀ (l : loc), P (Loc l)) →
  (∀ (v : val), P (Val v)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (UnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (BinOp op ot1 ot2 e1 e2)) →
  (∀ (ot1 : op_type) (e1 e2 : expr), P e1 → P e2 → P (CopyAllocId ot1 e1 e2)) →
  (∀ (o : order) (ot : op_type) (memcast : bool) (e : expr), P e → P (Deref o ot memcast e)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (CAS ot e1 e2 e3)) →
  (∀ (f : expr) (args : list expr), P f → Forall P args → P (Call f args)) →
  (∀ (es : list expr), Forall P es → P (Concat es)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (IfE ot e1 e2 e3)) →
  (∀ (ly : layout) (e : expr), P e → P (Alloc ly e)) →
  (∀ (e : expr), P e → P (SkipE e)) →
  (P StuckE) →
  (∀ (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr), P e1 → P e2 → P (LogicalAnd ot1 ot2 rit e1 e2)) →
  (∀ (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr), P e1 → P e2 → P (LogicalOr ot1 ot2 rit e1 e2)) →
  (∀ (o : order) (ot : op_type) (memcast : bool) (e : expr), P e → P (Use o ot memcast e)) →
  (∀ (e : expr), P e → P (AddrOf e)) →
  (∀ (e : expr), P e → P (LValue e)) →
  (∀ (e : expr) (s : struct_layout) (m : var_name), P e → P (GetMember e s m)) →
  (∀ (e : expr) (ul : union_layout) (m : var_name), P e → P (GetMemberUnion e ul m)) →
  (∀ (s : struct_layout) (m : var_name), P (OffsetOf s m)) →
  (∀ (ul : union_layout) (m : var_name), P (OffsetOfUnion ul m)) →
  (∀ (n : nat) (A : Type) (a : A) (e : expr), P e → P (AnnotExpr n a e)) →
  (∀ (a : location_info) (e : expr), P e → P (LocInfoE a e)) →
  (∀ (ly : struct_layout) (fs : list (string * expr)), Forall P fs.*2 → P (StructInit ly fs)) →
  (∀ (m : list lang.expr → lang.expr) (es : list expr) (wf : MacroWfSubst m), Forall P es → P (MacroE m es wf)) →
  (∀ (e : lang.expr), P (Expr e)) → ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ???????? Hcall Hconcat ??????????????? Hstruct Hmacro ?.
  9: {
    apply Hcall; [ |apply Forall_true => ?]; by apply: FIX.
  }
  9: {
    apply Hconcat. apply Forall_true => ?. by apply: FIX.
  }
  24: {
    apply Hstruct. apply Forall_fmap. apply Forall_true => ?. by apply: FIX.
  }
  24: {
    apply Hmacro. apply Forall_true => ?. by apply: FIX.
  }
  all: auto.
Qed.

Fixpoint to_expr (e : expr) : lang.expr :=
  match e with
  | Val v => v
  | Loc l => val_of_loc l
  | Var x => lang.Var x
  | UnOp op ot e  => lang.UnOp op ot (to_expr e)
  | BinOp op ot1 ot2 e1 e2 => lang.BinOp op ot1 ot2 (to_expr e1) (to_expr e2)
  | CopyAllocId ot1 e1 e2 => lang.CopyAllocId ot1 (to_expr e1) (to_expr e2)
  | Deref o ot mc e => lang.Deref o ot mc (to_expr e)
  | CAS ot e1 e2 e3 => lang.CAS ot (to_expr e1) (to_expr e2) (to_expr e3)
  | Call f args => lang.Call (to_expr f) (to_expr <$> args)
  | Concat es => lang.Concat (to_expr <$> es)
  | IfE ot e1 e2 e3 => lang.IfE ot (to_expr e1) (to_expr e2) (to_expr e3)
  | Alloc ly e => lang.Alloc ly (to_expr e)
  | SkipE e => lang.SkipE (to_expr e)
  | StuckE => lang.StuckE
  | LogicalAnd ot1 ot2 rit e1 e2 => notation.LogicalAnd ot1 ot2 rit (to_expr e1) (to_expr e2)
  | LogicalOr ot1 ot2 rit e1 e2 => notation.LogicalOr ot1 ot2 rit (to_expr e1) (to_expr e2)
  | Use o ot mc e => notation.Use o ot mc (to_expr e)
  | AddrOf e => notation.AddrOf (to_expr e)
  | LValue e => notation.LValue (to_expr e)
  | AnnotExpr n a e => notation.AnnotExpr n a (to_expr e)
  | LocInfoE a e => notation.LocInfo a (to_expr e)
  | StructInit ly fs => notation.StructInit ly (prod_map id to_expr <$> fs)
  | GetMember e s m => notation.GetMember (to_expr e) s m
  | GetMemberUnion e ul m => notation.GetMemberUnion (to_expr e) ul m
  | OffsetOf s m => notation.OffsetOf s m
  | OffsetOfUnion ul m => notation.OffsetOfUnion ul m
  | MacroE m es _ => notation.MacroE m (to_expr <$> es)
  | Expr e => e
  end.

Ltac of_expr e :=
  lazymatch e with
  | [] => constr:(@nil expr)
  | ?e :: ?es =>
    let e := of_expr e in
    let es := of_expr es in
    constr:(e :: es)

  | lang.Val (val.val_of_loc ?l) => constr:(Loc l)
  | notation.AddrOf ?e =>
    let e := of_expr e in constr:(AddrOf e)
  | notation.LValue ?e =>
    let e := of_expr e in constr:(LValue e)
  | notation.AnnotExpr ?n ?a ?e =>
    let e := of_expr e in constr:(AnnotExpr n a e)
  | notation.MacroE ?m ?es =>
    let es := of_expr es in constr:(MacroE m es _)
  | notation.LocInfo ?a ?e =>
    let e := of_expr e in constr:(LocInfoE a e)
  | notation.StructInit ?ly ?fs =>
    let fs := of_field_expr fs in constr:(StructInit ly fs)
  | notation.GetMember ?e ?s ?m =>
    let e := of_expr e in constr:(GetMember e s m)
  | notation.GetMemberUnion ?e ?ul ?m =>
    let e := of_expr e in constr:(GetMemberUnion e ul m)
  | notation.OffsetOf ?s ?m => constr:(OffsetOf s m)
  | notation.OffsetOfUnion ?ul ?m => constr:(OffsetOfUnion ul m)
  | notation.LogicalAnd ?ot1 ?ot2 ?rit ?e1 ?e2 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(LogicalAnd ot1 ot2 rit e1 e2)
  | notation.LogicalOr ?ot1 ?ot2 ?rit ?e1 ?e2 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(LogicalOr ot1 ot2 rit e1 e2)
  | notation.Use ?o ?ot ?mc ?e =>
    let e := of_expr e in constr:(Use o ot mc e)
  | lang.Val ?x => constr:(Val x)
  | lang.Var ?x => constr:(Var x)
  | lang.UnOp ?op ?ot ?e =>
    let e := of_expr e in constr:(UnOp op ot e)
  | lang.BinOp ?op ?ot1 ?ot2 ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op ot1 ot2 e1 e2)
  | lang.CopyAllocId ?ot1 ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(CopyAllocId ot1 e1 e2)
  | lang.Deref ?o ?ot ?mc ?e =>
    let e := of_expr e in constr:(Deref o ot mc e)
  | lang.CAS ?ot ?e1 ?e2 ?e3 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in let e3 := of_expr e3 in constr:(CAS ot e1 e2 e3)
  | lang.Call ?f ?args =>
    let f := of_expr f in
    let args := of_expr args in constr:(Call f args)
  | lang.Concat ?es =>
    let es := of_expr es in constr:(Concat es)
  | lang.IfE ?ot ?e1 ?e2 ?e3 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    let e3 := of_expr e3 in
    constr:(IfE ot e1 e2 e3)
  | lang.Alloc ?ly ?e =>
    let e := of_expr e in constr:(Alloc ly e)
  | lang.SkipE ?e =>
    let e := of_expr e in constr:(SkipE e)
  | lang.StuckE => constr:(StuckE e)
  | _ => constr:(Expr e)
  end
with of_field_expr fs :=
  lazymatch fs with
  | [] => constr:(@nil (string * expr))
  | (?id, ?e) :: ?fs =>
    let e := of_expr e in
    let fs := of_field_expr fs in
    constr:((id, e) :: fs)
  end.

Inductive ectx_item :=
| UnOpCtx (op : un_op) (ot : op_type)
| BinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : expr)
| BinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| CopyAllocIdLCtx (ot1 : op_type) (e2 : expr)
| CopyAllocIdRCtx (ot1 : op_type) (v1 : val)
| DerefCtx (o : order) (ot : op_type) (memcast : bool)
| CASLCtx (ot : op_type) (e2 e3 : expr)
| CASMCtx (ot : op_type) (v1 : val) (e3 : expr)
| CASRCtx (ot : op_type) (v1 v2 : val)
| CallLCtx (args : list expr)
| CallRCtx (f : val) (vl : list val) (el : list expr)
| ConcatCtx (vs : list val) (es : list expr)
| IfECtx (ot : op_type) (e2 e3 : expr)
| AllocCtx (ly : layout)
| SkipECtx
(* new constructors *)
| UseCtx (o : order) (ot : op_type) (memcast : bool)
| AddrOfCtx
| LValueCtx
| AnnotExprCtx (n : nat) {A} (a : A)
| LocInfoECtx (a : location_info)
(* the following would not work, thus we don't have a context, but prove a specialized bind rule*)
(*| StructInitCtx (ly : struct_layout) (vfs : list (string * val)) (id : string) (efs : list (string * expr))*)
| GetMemberCtx (s : struct_layout) (m : var_name)
| GetMemberUnionCtx (ul : union_layout) (m : var_name)
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | UnOpCtx op ot => UnOp op ot e
  | BinOpLCtx op ot1 ot2 e2 => BinOp op ot1 ot2 e e2
  | BinOpRCtx op ot1 ot2 v1 => BinOp op ot1 ot2 (Val v1) e
  | CopyAllocIdLCtx ot1 e2 => CopyAllocId ot1 e e2
  | CopyAllocIdRCtx ot1 v1 => CopyAllocId ot1 (Val v1) e
  | DerefCtx o ot mc => Deref o ot mc e
  | CASLCtx ot e2 e3 => CAS ot e e2 e3
  | CASMCtx ot v1 e3 => CAS ot (Val v1) e e3
  | CASRCtx ot v1 v2 => CAS ot (Val v1) (Val v2) e
  | CallLCtx args => Call e args
  | CallRCtx f vl el => Call (Val f) ((Val <$> vl) ++ e :: el)
  | ConcatCtx vs es => Concat ((Val <$> vs) ++ e :: es)
  | IfECtx ot e2 e3 => IfE ot e e2 e3
  | AllocCtx ly => Alloc ly e
  | SkipECtx => SkipE e
  | UseCtx o ot mc => Use o ot mc e
  | AddrOfCtx => AddrOf e
  | LValueCtx => LValue e
  | AnnotExprCtx n a => AnnotExpr n a e
  | LocInfoECtx a => LocInfoE a e
  | GetMemberCtx s m => GetMember e s m
  | GetMemberUnionCtx ul m => GetMemberUnion e ul m
  end.

Definition fill (K : list ectx_item) (e : expr) : expr := foldl (flip fill_item) e K.
Lemma fill_app (K1 K2 : list ectx_item) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

Fixpoint find_expr_fill (e : expr) (bind_val : bool) : option (list ectx_item * expr) :=
  match e with
  | Var _ => None
  | Val v => if bind_val then Some ([], Val v) else None
  | Loc l => if bind_val then Some ([], Loc l) else None
  | Expr e => Some ([], Expr e)
  | StuckE => Some ([], StuckE)
  | UnOp op ot e1 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [UnOpCtx op ot], e') else Some ([], e)
  | BinOp op ot1 ot2 e1 e2 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [BinOpLCtx op ot1 ot2 e2], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
           if e1 is Val v then Some (Ks ++ [BinOpRCtx op ot1 ot2 v], e') else None
         else Some ([], e)
  | CopyAllocId ot1 e1 e2 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CopyAllocIdLCtx ot1 e2], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
           if e1 is Val v then Some (Ks ++ [CopyAllocIdRCtx ot1 v], e') else None
         else Some ([], e)
  | CAS ot e1 e2 e3 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CASLCtx ot e2 e3], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
      if e1 is Val v1 then Some (Ks ++ [CASMCtx ot v1 e3], e') else None
    else if find_expr_fill e3 bind_val is Some (Ks, e') then
      if e1 is Val v1 then if e2 is Val v2 then Some (Ks ++ [CASRCtx ot v1 v2], e') else None else None
    else Some ([], e)
  | Call f args =>
    if find_expr_fill f bind_val is Some (Ks, e') then
      Some (Ks ++ [CallLCtx args], e') else
      (* TODO: handle arguments? *) None
  | Concat _ | MacroE _ _ _ | OffsetOf _ _ | OffsetOfUnion _ _ | LogicalAnd _ _ _ _ _ | LogicalOr _ _ _ _ _ => None
  | IfE ot e1 e2 e3 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [IfECtx ot e2 e3], e') else Some ([], e)
  | Alloc ly e1 =>
      if find_expr_fill e1 bind_val is Some (Ks, e') then
        Some (Ks ++ [AllocCtx ly], e') else Some ([], e)
  | SkipE e1 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [SkipECtx], e') else Some ([], e)
  | Deref o ot mc e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [DerefCtx o ot mc], e') else Some ([], e)
  | Use o ot mc e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [UseCtx o ot mc], e') else Some ([], e)
  | AddrOf e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [AddrOfCtx], e') else Some ([], e)
  | LValue e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [LValueCtx], e') else Some ([], e)
  | AnnotExpr n a e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [AnnotExprCtx n a], e') else Some ([], e)
  | LocInfoE a e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [LocInfoECtx a], e') else Some ([], e)
  | StructInit _ _ => None
  | GetMember e1 s m => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [GetMemberCtx s m], e') else Some ([], e)
  | GetMemberUnion e1 ul m => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [GetMemberUnionCtx ul m], e') else Some ([], e)
  end.

Lemma find_expr_fill_correct b e Ks e':
  find_expr_fill e b = Some (Ks, e') → e = fill Ks e'.
Proof.
  elim: e Ks e' => //= *;
     repeat (try case_match; simpl in *; simplify_eq => /=);
     rewrite ?fill_app /=; f_equal; eauto.
Qed.

Lemma ectx_item_correct Ks:
  ∃ Ks', ∀ e, to_rtexpr (to_expr (fill Ks e)) = ectxi_language.fill Ks' (to_rtexpr (to_expr e)).
Proof.
  elim/rev_ind: Ks; [by exists []|].
  move => K Ks [Ks' IH].
  eexists (Ks' ++ (ExprCtx <$> ?[K])) => ?. rewrite fill_app ectxi_language.fill_app /= -IH.
  only [K]: (destruct K; [
    apply: [lang.UnOpCtx _ _]|
    apply: [lang.BinOpLCtx _ _ _ _]|
    apply: [lang.BinOpRCtx _ _ _ _]|
    apply: [lang.CopyAllocIdLCtx _ _]|
    apply: [lang.CopyAllocIdRCtx _ _]|
    apply: [lang.DerefCtx _ _ _]|
    apply: [lang.CASLCtx _ _ _]|
    apply: [lang.CASMCtx _ _ _]|
    apply: [lang.CASRCtx _ _ _]|
    apply: [lang.CallLCtx _]|
    apply: [lang.CallRCtx _ _ _]|
    apply: [lang.ConcatCtx _ _]|
    apply: [lang.IfECtx _ _ _]|
    apply: [lang.AllocCtx _]|
    apply: [lang.SkipECtx]|
    apply: [lang.DerefCtx _ _ _]|
    apply: []|
    apply: []|
    apply: (replicate n lang.SkipECtx)|
    apply: []|
    apply: [lang.BinOpRCtx _ _ _ _]|
    apply: []|..
  ]).
  move: K => [||||||||||||||||||n|||] * //=.
  - (** Call *)
    do 2 f_equal.
    rewrite !fmap_app !fmap_cons. repeat f_equal; eauto.
    rewrite -!list_fmap_compose. by apply: list_fmap_ext.
  - (** Concat *)
    do 2 f_equal.
    rewrite !fmap_app !fmap_cons. repeat f_equal; eauto.
    rewrite -!list_fmap_compose. by apply: list_fmap_ext.
  - (** AnnotExpr *)
    elim: n; eauto.
    move => n. by rewrite /notation.AnnotExpr replicate_S_end fmap_app ectxi_language.fill_app /= => ->.
Qed.

Lemma to_expr_val_list (vl : list val) :
  to_expr <$> (Val <$> vl) = lang.Val <$> vl.
Proof. elim: vl => //; csimpl => *. by f_equal. Qed.

(*** Statements *)

Section stmt.
Local Unset Elimination Schemes.
Inductive stmt :=
| Goto (b : label)
| Return (e : expr)
| IfS (ot : op_type) (join : option label) (e : expr) (s1 s2 : stmt)
| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| Assign (o : order) (ot : op_type) (e1 e2 : expr) (s : stmt)
| Free (ly : layout) (e : expr) (s : stmt)
| SkipS (s : stmt)
| StuckS
| ExprS (e : expr) (s : stmt)

| Assert (ot : op_type) (e : expr) (s : stmt)
| AnnotStmt (n : nat) {A} (a : A) (s : stmt)
| LocInfoS (a : location_info) (s : stmt)
(* for opaque statements *)
| Stmt (s : lang.stmt).
End stmt.

Lemma stmt_ind (P : stmt → Prop):
  (∀ b : label, P (Goto b)) →
  (∀ e : expr, P (Return e)) →
  (∀ (ot : op_type) (join : option label) (e : expr) (s1 : stmt), P s1 → ∀ s2 : stmt, P s2 → P (IfS ot join e s1 s2)) →
  (∀ (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt), P def → Forall P bs → P (Switch it e m bs def)) →
  (∀ (o : order) (ot : op_type) (e1 e2 : expr) (s : stmt), P s → P (Assign o ot e1 e2 s)) →
  (∀ (ly : layout) (e : expr) (s : stmt), P s → P (Free ly e s)) →
  (∀ s : stmt, P s → P (SkipS s)) →
  (P StuckS) →
  (∀ (e : expr) (s : stmt), P s → P (ExprS e s)) →
  (∀ (ot : op_type) (e : expr) (s : stmt), P s → P (Assert ot e s)) →
  (∀ (n : nat) (A : Type) (a : A) (s : stmt), P s → P (AnnotStmt n a s)) →
  (∀ (a : location_info) (s : stmt), P s → P (LocInfoS a s)) →
  (∀ s : lang.stmt, P (Stmt s)) → ∀ s : stmt, P s.
Proof.
  move => *. generalize dependent P => P. match goal with | s : stmt |- _ => revert s end.
  fix FIX 1. move => [ ^s] ??? Hswitch *. 4: {
    apply Hswitch; first by apply: FIX. elim: sbs; auto.
  }
  all: auto.
Qed.


Fixpoint to_stmt (s : stmt) : lang.stmt :=
  match s with
  | Goto b => lang.Goto b
  | Return e => lang.Return (to_expr e)
  | IfS ot join e s1 s2 => (if{ot, join}: to_expr e then to_stmt s1 else to_stmt s2)%E
  | Switch it e m bs def => lang.Switch it (to_expr e) m (to_stmt <$> bs) (to_stmt def)
  | Assign o ot e1 e2 s => lang.Assign o ot (to_expr e1) (to_expr e2) (to_stmt s)
  | Free ly e s => lang.Free ly (to_expr e) (to_stmt s)
  | SkipS s => lang.SkipS (to_stmt s)
  | StuckS => lang.StuckS
  | ExprS e s => lang.ExprS (to_expr e) (to_stmt s)
  | Assert ot e s => (assert{ot}: to_expr e; to_stmt s)%E
  | AnnotStmt n a s => notation.AnnotStmt n a (to_stmt s)
  | LocInfoS a s => notation.LocInfo a (to_stmt s)
  | Stmt s => s
  end.

Ltac of_stmt s :=
  lazymatch s with
  | [] => constr:(@nil stmt)
  | ?s :: ?ss =>
    let s := of_stmt s in
    let ss := of_stmt ss in
    constr:(s :: ss)

  | notation.AnnotStmt ?n ?a ?s =>
    let s := of_stmt s in
    constr:(AnnotStmt n a s)
  | notation.LocInfo ?a ?s =>
    let s := of_stmt s in
    constr:(LocInfoS a s)
  | (assert{?ot}: ?e ; ?s)%E =>
    let e := of_expr e in
    let s := of_stmt s in
    constr:(Assert ot e s)
  | (if{?ot, ?join}: ?e then ?s1 else ?s2)%E =>
    let e := of_expr e in
    let s1 := of_stmt s1 in
    let s2 := of_stmt s2 in
    constr:(IfS ot join e s1 s2)
  | lang.Goto ?b => constr:(Goto b)
  | lang.Return ?e =>
    let e := of_expr e in constr:(Return e)
  | lang.Switch ?it ?e ?m ?bs ?def =>
    let e := of_expr e in
    let bs := of_stmt bs in
    let def := of_stmt def in
    constr:(Switch it e m bs def)
  | lang.Assign ?o ?ot ?e1 ?e2 ?s =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    let s := of_stmt s in
    constr:(Assign o ot e1 e2 s)
  | lang.Free ?ly ?e ?s =>
    let e := of_expr e in
    let s := of_stmt s in
    constr:(Free ly e s)
  | lang.SkipS ?s =>
    let s := of_stmt s in
    constr:(SkipS s)
  | lang.StuckS => constr:(StuckS s)
  | lang.ExprS ?e ?s =>
    let e := of_expr e in
    let s := of_stmt s in
    constr:(ExprS e s)
  | _ => constr:(Stmt s)
  end.

Inductive stmt_ectx :=
| AssignRCtx (o : order) (ot : op_type) (e1 : expr) (s : stmt)
| AssignLCtx (o : order) (ot : op_type) (v2 : val) (s : stmt)
| ReturnCtx
| IfSCtx (ot : op_type) (join: option label) (s1 s2 : stmt)
| SwitchCtx (it : int_type) (m: gmap Z nat) (bs : list stmt) (def : stmt)
| ExprSCtx (s : stmt)
| AssertCtx (ot : op_type) (s : stmt)
| FreeCtx (ly : layout) (s : stmt)
.

Definition stmt_fill (Ki : stmt_ectx) (e : expr) : stmt :=
  match Ki with
  | AssignRCtx o ot e1 s => Assign o ot e1 e s
  | AssignLCtx o ot v2 s => Assign o ot e (Val v2) s
  | ReturnCtx => Return e
  | ExprSCtx s => ExprS e s
  | IfSCtx ot join s1 s2 => IfS ot join e s1 s2
  | SwitchCtx it m bs def => Switch it e m bs def
  | AssertCtx ot s => Assert ot e s
  | FreeCtx ly s => Free ly e s
  end.

Definition find_stmt_fill (s : stmt) : option (stmt_ectx * expr) :=
  match s with
  | Goto _ | Stmt _ | AnnotStmt _ _ _ | LocInfoS _ _ | SkipS _ | StuckS => None
  | Return e => if e is (Val v) then None else Some (ReturnCtx, e)
  | ExprS e s => if e is (Val v) then None else Some (ExprSCtx s, e)
  | IfS ot join e s1 s2 => if e is (Val v) then None else Some (IfSCtx ot join s1 s2, e)
  | Switch it e m bs def => if e is (Val v) then None else Some (SwitchCtx it m bs def, e)
  | Assign o ot e1 e2 s => if e2 is (Val v) then if e1 is (Val v) then None else Some (AssignLCtx o ot v s, e1) else Some (AssignRCtx o ot e1 s, e2)
  | Assert ot e s => if e is (Val v) then None else Some (AssertCtx ot s, e)
  | Free ly e s => if e is (Val v) then None else Some (FreeCtx ly s, e)
  end.

Lemma find_stmt_fill_correct s Ks e:
  find_stmt_fill s = Some (Ks, e) → s = stmt_fill Ks e.
Proof.
  destruct s => *; repeat (try case_match; simpl in *; simplify_eq => //).
Qed.

Lemma stmt_fill_correct Ks rf:
  ∃ Ks', ∀ e, to_rtstmt rf (to_stmt (stmt_fill Ks e)) = ectxi_language.fill Ks' (to_rtexpr (to_expr e)).
Proof.
  move: Ks => [] *; [
  eexists ([StmtCtx (lang.AssignRCtx _ _ _ _) rf])|
  eexists ([StmtCtx (lang.AssignLCtx _ _ _ _) rf])|
  eexists ([StmtCtx (lang.ReturnCtx) rf])|
  eexists ([StmtCtx (lang.IfSCtx _ _ _ _) rf])|
  eexists ([StmtCtx (lang.SwitchCtx _ _ _ _) rf])|
  eexists ([StmtCtx (lang.ExprSCtx _) rf])|
  eexists ([StmtCtx (lang.IfSCtx _ _ _ _) rf])|
  eexists ([StmtCtx (lang.FreeCtx _ _) rf])|
..] => //=.
Qed.

(*** Substitution *)
Definition list_find_fast {A} (P : A → Prop) `{!∀ x, Decision (P x)} :=
  fix go (l : list A) : option A :=
    match l with
    | [] => None
    | x :: l => if decide (P x) then Some x else go l
    end.
Global Instance: Params (@list_find_fast) 3 := {}.

Fixpoint subst_l (xs : list (var_name * val)) (e : expr)  : expr :=
  match e with
  | Var y => if list_find_fast (λ x, x.1 = y) xs is Some (_, v) then Val v else Var y
  | Loc l => Loc l
  | Val v => Val v
  | UnOp op ot e => UnOp op ot (subst_l xs e)
  | BinOp op ot1 ot2 e1 e2 => BinOp op ot1 ot2 (subst_l xs e1) (subst_l xs e2)
  | CopyAllocId ot1 e1 e2 => CopyAllocId ot1 (subst_l xs e1) (subst_l xs e2)
  | Deref o ot mc e => Deref o ot mc (subst_l xs e)
  | CAS ot e1 e2 e3 => CAS ot (subst_l xs e1) (subst_l xs e2) (subst_l xs e3)
  | Call f args => Call (subst_l xs f) (subst_l xs <$> args)
  | Concat es => Concat (subst_l xs <$> es)
  | IfE ot e1 e2 e3 => IfE ot (subst_l xs e1) (subst_l xs e2) (subst_l xs e3)
  | Alloc ly e => Alloc ly (subst_l xs e)
  | SkipE e => SkipE (subst_l xs e)
  | StuckE => StuckE
  | LogicalAnd ot1 ot2 rit e1 e2 => LogicalAnd ot1 ot2 rit (subst_l xs e1) (subst_l xs e2)
  | LogicalOr ot1 ot2 rit e1 e2 => LogicalOr ot1 ot2 rit (subst_l xs e1) (subst_l xs e2)
  | Use o ot mc e => Use o ot mc (subst_l xs e)
  | AddrOf e => AddrOf (subst_l xs e)
  | LValue e => LValue (subst_l xs e)
  | AnnotExpr n a e => AnnotExpr n a (subst_l xs e)
  | LocInfoE a e => LocInfoE a (subst_l xs e)
  | StructInit ly fs => StructInit ly (prod_map id (subst_l xs) <$> fs)
  | GetMember e s m => GetMember (subst_l xs e) s m
  | GetMemberUnion e ul m => GetMemberUnion (subst_l xs e) ul m
  | OffsetOf s m => OffsetOf s m
  | OffsetOfUnion ul m => OffsetOfUnion ul m
  | MacroE m es wf => MacroE m (subst_l xs <$> es) wf
  | Expr e => Expr (lang.subst_l xs e)
  end.

Lemma to_expr_subst x v e :
  to_expr (subst_l [(x, v)] e) = lang.subst x v (to_expr e).
Proof.
  elim: e => *//; cbn -[notation.GetMember]; (repeat case_bool_decide) => //=; f_equal; eauto; try by case_decide.
  - (** Call *)
    revert select (Forall _ _) => /Forall_forall?.
    rewrite -!list_fmap_compose. apply list_fmap_ext => ?? /(list_elem_of_lookup_2 _ _ _).  naive_solver.
  - (** Concat *)
    revert select (Forall _ _) => /Forall_forall?.
    rewrite -!list_fmap_compose. apply list_fmap_ext => ?? /(list_elem_of_lookup_2 _ _ _).  naive_solver.
  - (** LogicalAnd *)
    rewrite /notation.LogicalAnd/=. do 2 f_equal; eauto.
  - (** LogicalOr *)
    rewrite /notation.LogicalOr/=. do 2 f_equal; eauto.
  - (** GetMember *)
    match goal with
    | _ : ?e1 = ?e2 |- _ => assert (e1 = e2) as -> by assumption
    end; done.
  - rewrite /notation.OffsetOf/=.
    match goal with | |- context [offset_of ?s ?m] => destruct (offset_of s m) end => //=.
    by match goal with | |- context [val_of_Z ?o ?it] => destruct (val_of_Z o it) end.
  - (** AnnotExpr *)
    match goal with
    | |- notation.AnnotExpr ?n _ _ = _ => generalize dependent n
    end.
    by rewrite /notation.AnnotExpr; elim; eauto => /= n ->.
  - (** StructInit *)
    match goal with | H : struct_layout |- _ => rename H into sl end.
    match goal with | H : list (string * expr) |- _ => rename H into fs end.
    rewrite /notation.StructInit; f_equal.
    generalize dependent fs.
    induction (sl_members sl) as [|[f ly] ? IHfs]; first done. move => fs Hf.
    rewrite fmap_cons IHfs //=; clear IHfs; f_equal.
    rewrite [X in _ = X]apply_default /=. f_equal. destruct f as [f|] => //=.
    rewrite !list_to_map_fmap !lookup_fmap. destruct (list_to_map fs !! f) as [e|] eqn:H; simpl; last done.
    f_equal. move: Hf => /Forall_forall IH. apply (IH _).
    simplify_eq. apply elem_of_list_to_map_2 in H. set_solver.
  - (** MacroE *)
    revert select (Forall _ _) => /Forall_forall?.
    rewrite /notation.MacroE macro_wf_subst. f_equal.
    rewrite -!list_fmap_compose. apply list_fmap_ext => ?? /(list_elem_of_lookup_2 _ _ _).  naive_solver.
Qed.

Lemma Forall_eq_fmap {A B} (xs : list A) (f1 f2 : A → B) :
  Forall (λ x, f1 x = f2 x) xs → f1 <$> xs = f2 <$> xs.
Proof. elim => //. csimpl. congruence. Qed.

Lemma fmap_snd_prod_map {A B C} (l : list (A * B)) (f1 f2 : B → C)  :
  f1 <$> l.*2 = f2 <$> l.*2 →
  prod_map id f1 <$> l = prod_map id f2 <$> l.
Proof. elim: l => // -[??] ? IH. csimpl => -[??]. rewrite IH //. congruence. Qed.

Lemma to_expr_subst_l xs e :
  to_expr (subst_l xs e) = lang.subst_l xs (to_expr e).
Proof.
  elim: xs e => //=.
  - elim => //= >; try congruence; try move => ->.
    all: try move => /Forall_eq_fmap; try move/fmap_snd_prod_map.
    all: by move => <-; by rewrite -list_fmap_compose.
  - move => [x v] xs IH e. rewrite -to_expr_subst -IH. f_equal.
    elim: e => //= >; try congruence; try move => ->.
    all: try move => /Forall_eq_fmap; try move/fmap_snd_prod_map.
    all: try by move => ->; by rewrite -list_fmap_compose.
    case_decide => //.
Qed.

Fixpoint subst_stmt (xs : list (var_name * val)) (s : stmt) : stmt :=
  match s with
  | Goto b => Goto b
  | Return e => Return (subst_l xs e)
  | IfS ot join e s1 s2 => IfS ot join (subst_l xs e) (subst_stmt xs s1) (subst_stmt xs s2)
  | Switch it e m' bs def => Switch it (subst_l xs e) m' (subst_stmt xs <$> bs) (subst_stmt xs def)
  | Assign o ot e1 e2 s => Assign o ot (subst_l xs e1) (subst_l xs e2) (subst_stmt xs s)
  | Free ly e s => Free ly (subst_l xs e) (subst_stmt xs s)
  | SkipS s => SkipS (subst_stmt xs s)
  | StuckS => StuckS
  | ExprS e s => ExprS (subst_l xs e) (subst_stmt xs s)
  | Assert ot e s => Assert ot (subst_l xs e) (subst_stmt xs s)
  | AnnotStmt n a s => AnnotStmt n a (subst_stmt xs s)
  | LocInfoS a s => LocInfoS a (subst_stmt xs s)
  | Stmt s => Stmt (lang.subst_stmt xs s)
  end.

Lemma to_stmt_subst xs s :
  to_stmt (subst_stmt xs s) = lang.subst_stmt xs (to_stmt s).
Proof.
  elim: s => * //=; repeat rewrite to_expr_subst_l //; repeat f_equal => //; repeat rewrite -list_fmap_compose.
  - by apply Forall_fmap_ext_1.
  - rewrite /notation.Assert. by f_equal.
  - match goal with
    | |- notation.AnnotStmt ?n _ _ = _ => generalize dependent n
    end.
    by rewrite /notation.AnnotStmt; elim; eauto => /= n ->.
Qed.
End W.

(** Substitution *)
Ltac simpl_subst :=
  (* We need to be careful to never call simpl on the goal as that may
  become quite slow. TODO: vm_compute seems to perform a lot better
  than simpl but it reduces to much. Can we somehow still use it?  *)
  repeat (lazymatch goal with
          | |- context C [subst_stmt ?xs ?s] =>
            let s' := W.of_stmt s in
            let P := context C [subst_stmt xs (W.to_stmt s')] in
            change_no_check P; rewrite <-(W.to_stmt_subst xs)
          end);
  repeat (lazymatch goal with
          | |- context C [W.to_stmt (W.subst_stmt ?xs ?s)] =>
            let s' := eval simpl in (W.subst_stmt xs s) in
            let s' := eval unfold W.to_stmt, W.to_expr in (W.to_stmt s') in
            let s' := eval simpl in s' in
            let P := context C [s'] in
            change_no_check P
          end).
Arguments W.to_expr : simpl never.
Arguments W.to_stmt : simpl never.
Arguments subst : simpl never.
Arguments subst_l : simpl never.
Arguments subst_stmt : simpl never.

Ltac inv_stmt_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : stmt_step ?e _ _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
(*      and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Ltac inv_expr_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : expr_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
(*      and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Ltac solve_struct_obligations := done.
