From refinedc.typing Require Export typing.
From refinedc.examples.scheduler.src.fdsched Require Export axioms.

Notation pdata := (list Z) (only parsing).

Class PacketArrivals := {
  packet_arrivals : FD → nat → option pdata
}.

Definition max_msg_len : Z :=
  (4096 - ly_size u8 - ly_size size_t - ly_size void* ).
Global Opaque max_msg_len.

Global Instance packet_ID_inhabited : Inhabited packet_ID :=
  populate {|fd := inhabitant; read_index := inhabitant |}.

Global Instance DecisionID : EqDecision packet_ID.
Proof.
  solve_decision.
Qed.

(* Since Cerberus sets the value of EWOULDBLOCK, we also define the value
   of the errorcode EWOULDBLOCK to be [80]. *)
(* Link to Cerberus definition : https://github.com/rems-project/cerberus/blob/84d9b28a6af7453e3591e353cf1de08963a2bb40/frontend/model/builtins.lem#L169 *)
Definition EWOULDBLOCK : nat := 80.

Section ReadIndex.
  Context `{typeG Σ}.
  Global Instance curr_read_index_related_to A t :
    RelatedTo (Σ := Σ) (λ x : A,curr_read_index (t x)) :=
    {|rt_fic := FindDirect (λ t, curr_read_index t)%I |}.

  Lemma subsume_curr_read_index B M t t1 G:
    (∃ x, ⌜t = t1 x⌝ ∗ G x)
    ⊢ subsume (Σ := Σ) (curr_read_index t) M (λ x : B, curr_read_index (t1 x)) G.
  Proof. iIntros "(%x & -> & ?) Hcurr !>". iExists _. iFrame. Qed.
  Definition subsume_curr_read_index_inst := [instance subsume_curr_read_index].
  Global Existing Instance subsume_curr_read_index_inst.

End ReadIndex.

Section ReadSpecs.
  Context `{!PacketArrivals}.

  Definition get_packet_data (ID : packet_ID) : pdata :=
    take (Z.to_nat max_msg_len) (default inhabitant (packet_arrivals ID.(fd) ID.(read_index))).

   Definition get_packet_data_option (ID : option packet_ID) : pdata:=
     from_option get_packet_data inhabitant ID.

End ReadSpecs.

Global Opaque get_packet_data.
