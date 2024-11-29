From refinedc.typing Require Import base.

Inductive to_uninit_annot : Set :=
  ToUninit.

Inductive stop_annot : Set :=
  StopAnnot.

Inductive share_annot : Set :=
  ShareAnnot.

Inductive unfold_once_annot : Set :=
  UnfoldOnceAnnot.

Inductive learn_annot : Set :=
  LearnAnnot.

Inductive learn_alignment_annot : Set :=
  LearnAlignmentAnnot.

Inductive LockAnnot : Set := LockA | UnlockA.

Inductive reduce_annot : Set :=
  ReduceAnnot.

Inductive assert_annot : Set :=
  AssertAnnot (s : string).
