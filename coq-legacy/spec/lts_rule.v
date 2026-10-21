(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   The rule for LongToShortNoEndCarry with 7 input values and 64-bit output limbs. The input assumption
   PRE_lts is the input's shape only: exactly 7 values, which are integers and may be negative. The relation
   REL_lts: out has exactly 8 limbs, each in [0, 2^64); the value of out equals the value of the input; every
   running carry lies in [0, 2^67); and ENVELOPE: the first input lies in [0, 2^131) and every later one in
   (-2^67, 2^131). `adequate`: for every input of that shape, a circuit accepts exactly the pairs the relation
   accepts. Checked examples follow: pairs the relation accepts, one of them with a negative input, and pairs
   it rejects.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition N_BITS : Z := 64.
Definition K : nat := 7.
Definition B : Z := 2 ^ N_BITS.

Definition LOGK : Z := Z.log2 (Z.of_nat K) + 1.

Definition VAL (v : list Z) : Z := fold_right (fun x acc => x + B * acc) 0 v.

Definition limb_ok (x : Z) : Prop := 0 <= x < B.

Definition CARRY (inp out : list Z) (i : nat) : Z :=
  (VAL (firstn (S i) inp) - VAL (firstn (S i) out)) / B ^ Z.of_nat (S i).

(* The input assumption: the input's shape only, exactly 7 values. No range is assumed. *)
Definition PRE_lts (inp : list Z) : Prop := length inp = K.

(* The input range the circuit enforces, stated as part of the relation so that it is claimed, not
   assumed. It follows from the relation's other conjuncts and the input's shape (ENVELOPE_is_redundant,
   in lts_soundness.v). *)
Definition ENVELOPE (inp : list Z) : Prop :=
  0 <= nth 0 inp 0 < 2 ^ (2 * N_BITS + LOGK) /\
  (forall i, (0 < i < K)%nat ->
     - 2 ^ (N_BITS + LOGK) < nth i inp 0 < 2 ^ (2 * N_BITS + LOGK)).

(* The relation: 8 output limbs in range, equal values as integers, every running carry in [0, 2^67),
   and the envelope. *)
Definition REL_lts (inp out : list Z) : Prop :=
  length out = S K /\ Forall limb_ok out /\ VAL out = VAL inp /\
  (forall i, (i < K)%nat -> 0 <= CARRY inp out i < 2 ^ (N_BITS + LOGK)) /\
  ENVELOPE inp.

(* Adequacy: for every input of the right shape, acceptance and the relation coincide. *)
Definition adequate (accepts : list Z -> list Z -> Prop) : Prop :=
  forall inp out, PRE_lts inp -> (accepts inp out <-> REL_lts inp out).

From Coq Require Import Lia.

Lemma N_BITS_val : N_BITS = 64. Proof. reflexivity. Qed.
Lemma K_val : K = 7%nat. Proof. reflexivity. Qed.

Lemma LOGK_is_3 : LOGK = 3. Proof. vm_compute. reflexivity. Qed.

Lemma carry_width_is_67 : N_BITS + LOGK = 67.
Proof. rewrite LOGK_is_3. reflexivity. Qed.

Lemma B_value : B = 18446744073709551616.
Proof. unfold B, N_BITS. vm_compute. reflexivity. Qed.

Lemma B_pos : 0 < B.
Proof. rewrite B_value. lia. Qed.

Lemma VAL_nil : VAL [] = 0. Proof. reflexivity. Qed.
Lemma VAL_cons : forall x t, VAL (x :: t) = x + B * VAL t. Proof. reflexivity. Qed.

Lemma VAL_firstn_skipn : forall n v,
  VAL v = VAL (firstn n v) + B ^ Z.of_nat n * VAL (skipn n v).
Proof.
  induction n as [|n IH]; intro v.
  - cbn [firstn skipn Z.of_nat]. rewrite Z.pow_0_r, VAL_nil. ring.
  - destruct v as [|x t].
    + cbn [firstn skipn]. rewrite VAL_nil. ring.
    + cbn [firstn skipn]. rewrite !VAL_cons, (IH t).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma CARRY_exact : forall inp out i,
  VAL out = VAL inp ->
  VAL (firstn (S i) inp) - VAL (firstn (S i) out)
  = B ^ Z.of_nat (S i) * (VAL (skipn (S i) out) - VAL (skipn (S i) inp)).
Proof.
  intros inp out i Heq.
  pose proof (VAL_firstn_skipn (S i) inp) as Hi.
  pose proof (VAL_firstn_skipn (S i) out) as Ho.
  rewrite Heq in Ho.
  rewrite Z.mul_sub_distr_l. lia.
Qed.

Lemma B_pow_nonzero : forall n, B ^ Z.of_nat n <> 0.
Proof. intro n. apply Z.pow_nonzero; [ rewrite B_value; lia | lia ]. Qed.

Theorem CARRY_is_suffix_difference : forall inp out i,
  VAL out = VAL inp ->
  CARRY inp out i = VAL (skipn (S i) out) - VAL (skipn (S i) inp).
Proof.
  intros inp out i Heq. unfold CARRY.
  rewrite (CARRY_exact inp out i Heq), Z.mul_comm.
  apply Z.div_mul. apply B_pow_nonzero.
Qed.

Ltac carries := intros i Hi; unfold N_BITS; rewrite LOGK_is_3; unfold K in Hi;
  do 7 (destruct i as [|i]; [vm_compute; split; congruence|]); lia.
Ltac env := unfold ENVELOPE, N_BITS; rewrite LOGK_is_3; split;
  [ vm_compute; split; congruence
  | intros i Hi; unfold K in Hi; do 7 (destruct i as [|i]; [try lia; vm_compute; split; congruence|]); lia ].
Ltac rel_row := split; [reflexivity|]; split; [repeat constructor; vm_compute; congruence|];
  split; [vm_compute; reflexivity|]; split; [carries| env].

Definition OK_IN  : list Z := [2^130; 0; 0; 0; 0; 0; 0].
Definition OK_OUT : list Z := [0; 0; 4; 0; 0; 0; 0; 0].
Example ok_row_pre : PRE_lts OK_IN. Proof. reflexivity. Qed.
Example ok_row_rel : REL_lts OK_IN OK_OUT. Proof. unfold OK_IN, OK_OUT. rel_row. Qed.

Definition SQ : Z := (2^64 - 1) * (2^64 - 1).
Definition CONV_IN  : list Z := [SQ; 2*SQ; 3*SQ; 4*SQ; 3*SQ; 2*SQ; SQ].
Definition CONV_OUT : list Z := [1; 0; 0; 0; 2^64-2; 2^64-1; 2^64-1; 2^64-1].
Example conv_row_rel : REL_lts CONV_IN CONV_OUT.
Proof. unfold CONV_IN, CONV_OUT, SQ. rel_row. Qed.

Definition WRAP_IN  : list Z := [(2^67-1)*2^64; -(2^67-1); 0; 0; 0; 0; 0].
Definition WRAP_OUT : list Z := [0; 0; 0; 0; 0; 0; 0; 0].
Example wrap_row_rel : REL_lts WRAP_IN WRAP_OUT.
Proof. unfold WRAP_IN, WRAP_OUT. rel_row. Qed.

Definition CX2_IN  : list Z := [2^131-2^64; 2^131-2^64; 0;0;0;0;0].
Definition CX2_OUT : list Z := [0; 2^64-1; 6; 8; 0;0;0;0].
Example cx2_val_equal : VAL CX2_OUT = VAL CX2_IN. Proof. vm_compute. reflexivity. Qed.
Example cx2_carry1 : CARRY CX2_IN CX2_OUT 1 = 2^67 + 6. Proof. vm_compute. reflexivity. Qed.
Example cx2_envelope : ENVELOPE CX2_IN. Proof. unfold CX2_IN. env. Qed.
Example cx2_not_rel : ~ REL_lts CX2_IN CX2_OUT.
Proof.
  intros [_ [_ [_ [H _]]]]. specialize (H 1%nat ltac:(unfold K; lia)).
  rewrite cx2_carry1 in H. unfold N_BITS in H. rewrite LOGK_is_3 in H.
  vm_compute in H. destruct H as [_ H]. discriminate.
Qed.

Definition FRAUD_OUT : list Z := [0; 0; 5; 0; 0; 0; 0; 0].
Example fraud_row_refused : ~ REL_lts OK_IN FRAUD_OUT.
Proof. intros [_ [_ [H _]]]. vm_compute in H. discriminate. Qed.

Example neg0_not_rel : forall out, ~ REL_lts [-1;0;0;0;0;0;0] out.
Proof. intros out [_ [_ [_ [_ [[H _] _]]]]]. vm_compute in H. apply H. reflexivity. Qed.

Example envelope_top_edge : (2^67-1)*2^64 + (2^64-1) = 2^(2*N_BITS+LOGK) - 1.
Proof. unfold N_BITS; rewrite LOGK_is_3. vm_compute. reflexivity. Qed.

Print Assumptions N_BITS_val.
Print Assumptions K_val.
Print Assumptions LOGK_is_3.
Print Assumptions carry_width_is_67.
Print Assumptions B_value.
Print Assumptions B_pos.
Print Assumptions VAL_nil.
Print Assumptions VAL_cons.
Print Assumptions VAL_firstn_skipn.
Print Assumptions CARRY_exact.
Print Assumptions B_pow_nonzero.
Print Assumptions CARRY_is_suffix_difference.
Print Assumptions ok_row_pre.
Print Assumptions ok_row_rel.
Print Assumptions conv_row_rel.
Print Assumptions wrap_row_rel.
Print Assumptions cx2_val_equal.
Print Assumptions cx2_carry1.
Print Assumptions cx2_envelope.
Print Assumptions cx2_not_rel.
Print Assumptions fraud_row_refused.
Print Assumptions neg0_not_rel.
Print Assumptions envelope_top_edge.
