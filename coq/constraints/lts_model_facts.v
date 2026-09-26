(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Facts about the model used by the proofs. In every accepted filling the output limbs lie in [0, 2^64)
   (out_limbs_in_range) and the seven carry cells in [0, 2^67) (carry_cells_in_range); the output limbs
   agree with the public cells. The input cells are read signed by the half-field rule. For every modulus
   P >= 2^132 - 1 that reading returns every value in (-2^67, 2^131) exactly
   (signed_reading_is_exact_above_the_threshold); at a modulus below that threshold it does not
   (signed_reading_fails_below_the_threshold); the Pasta prime clears it (pasta_clears_the_threshold).
   Also: each input cell is read by exactly one polynomial constraint, the input assumption is shape only,
   the envelope is a conjunct of the relation, and the relation puts the output's value below 2^512
   (NoEndCarry_is_a_consequence).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.lts_model_gen.
Require Import Generated.lts_scaffold_gen.
Require Import Constraints.lts_semantic.
Require lts_rule.

Theorem one_member_of_a_family :
  lts_rule.N_BITS = 64 /\ lts_rule.K = 7%nat /\ lts_rule.N_BITS <= 126
  /\ lts_rule.LOGK = 3.
Proof. split; [ reflexivity | split; [ reflexivity | split ] ]; [ unfold lts_rule.N_BITS; lia | exact lts_rule.LOGK_is_3 ]. Qed.

Theorem the_in_decode_is_signed_by_the_half_field_rule : forall a i,
  (i < 7)%nat ->
  nth i (inp_l a) 0
  = if dc a i <=? (p - 1) / 2 then dc a i else dc a i - p.
Proof. intros a i Hi. rewrite (inp_l_nth a i Hi). reflexivity. Qed.

Definition sdec_at (P x : Z) : Z := if x <=? (P - 1) / 2 then x else x - P.

Theorem signed_reading_is_exact_above_the_threshold : forall P z,
  2 ^ 132 - 1 <= P -> - 2 ^ 67 < z < 2 ^ 131 ->
  sdec_at P (z mod P) = z.
Proof.
  intros P z HP Hz.
  assert (H132 : 2 ^ 132 = 2 * 2 ^ 131) by reflexivity.
  assert (H67 : 2 ^ 67 <= 2 ^ 131) by (apply Z.pow_le_mono_r; lia).
  set (X := 2 ^ 131) in *. set (Y := 2 ^ 67) in *.
  assert (HX : 0 < Y) by (unfold Y; apply Z.pow_pos_nonneg; lia).
  assert (Hh : X - 1 <= (P - 1) / 2).
  { apply Z.div_le_lower_bound; lia. }
  unfold sdec_at. destruct (Z.leb_spec 0 z) as [Hz0|Hz0].
  - rewrite Z.mod_small by lia. destruct (Z.leb_spec z ((P - 1) / 2)); lia.
  - assert (Hm : z mod P = z + P).
    { rewrite <- (Z.mod_add z 1 P) by lia. rewrite Z.mod_small by lia. ring. }
    rewrite Hm. destruct (Z.leb_spec (z + P) ((P - 1) / 2)) as [Hle|Hgt].
    + exfalso. pose proof (Z.mul_div_le (P - 1) 2 ltac:(lia)). lia.
    + ring.
Qed.

Definition P_BELOW : Z := 2 ^ 131 + 2 ^ 70 + 1.

Theorem signed_reading_fails_below_the_threshold :
  P_BELOW < 2 ^ 132 - 1
  /\ sdec_at P_BELOW ((2 ^ 131 - 1) mod P_BELOW) <> 2 ^ 131 - 1.
Proof. split; vm_compute; [ reflexivity | discriminate ]. Qed.

Theorem pasta_clears_the_threshold : 2 ^ 132 - 1 <= p.
Proof. exact pasta_margin. Qed.

Theorem out_limbs_in_range : forall a,
  sat deployed_model a -> Forall lts_rule.limb_ok (out_l a).
Proof.
  intros a Hs. unfold out_l.
  pose proof (rng_out a Hs) as H. unfold lts_rule.limb_ok. rewrite lts_rule.B_value.

  apply Forall_cons; [ exact (H 0%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 1%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 2%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 3%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 4%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 5%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 6%nat ltac:(lia)) | ].
  apply Forall_cons; [ exact (H 7%nat ltac:(lia)) | ].
  apply Forall_nil.
Qed.

Theorem carry_cells_in_range : forall a,
  sat deployed_model a ->
  forall i, (i < 7)%nat -> 0 <= cc a i < 2 ^ (lts_rule.N_BITS + lts_rule.LOGK).
Proof.
  intros a Hs i Hi. rewrite lts_rule.carry_width_is_67.
  change (2 ^ 67) with 147573952589676412928. exact (rng_c a Hs i Hi).
Qed.

Theorem each_in_cell_is_read_by_exactly_one_gate :
  map (fun i => length (filter (reads_b (i, 0%nat)) deployed_gates)) (seq 0 7)
  = [1; 1; 1; 1; 1; 1; 1]%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem in_cell_indices_lie_below_OUTBIT_BASE :
  OUTBIT_BASE = 22%nat /\ (forall c, (c < 7)%nat -> (c < OUTBIT_BASE)%nat).
Proof. split; [ reflexivity | intros c Hc; unfold OUTBIT_BASE; lia ]. Qed.

Theorem PRE_is_shape_only : forall inp, lts_rule.PRE_lts inp <-> length inp = 7%nat.
Proof. intro inp. unfold lts_rule.PRE_lts, lts_rule.K. tauto. Qed.

Theorem ENVELOPE_is_a_conjunct_of_REL : forall inp out,
  lts_rule.REL_lts inp out -> lts_rule.ENVELOPE inp.
Proof. intros inp out [_ [_ [_ [_ H]]]]. exact H. Qed.

Lemma VAL_bounds_8 : forall o,
  length o = 8%nat -> Forall lts_rule.limb_ok o ->
  0 <= lts_rule.VAL o < lts_rule.B ^ 8.
Proof.
  intros o Hl Hf.
  destruct o as [|o0 [|o1 [|o2 [|o3 [|o4 [|o5 [|o6 [|o7 [|x t]]]]]]]]]; cbn [length] in Hl; try lia.
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
  unfold lts_rule.limb_ok in *. unfold lts_rule.VAL. cbn [fold_right].
  rewrite lts_rule.B_value in *. lia.
Qed.

Theorem NoEndCarry_is_a_consequence : forall inp out,
  lts_rule.REL_lts inp out -> 0 <= lts_rule.VAL out < lts_rule.B ^ 8.
Proof. intros inp out [Hl [Hf _]]. exact (VAL_bounds_8 out Hl Hf). Qed.

Theorem out_limbs_are_pinned_to_public_cells : forall a,
  sat deployed_model a -> PINS_lts a.
Proof. exact answer_pins_are_DERIVED. Qed.

Print Assumptions one_member_of_a_family.
Print Assumptions the_in_decode_is_signed_by_the_half_field_rule.
Print Assumptions signed_reading_is_exact_above_the_threshold.
Print Assumptions signed_reading_fails_below_the_threshold.
Print Assumptions pasta_clears_the_threshold.
Print Assumptions out_limbs_in_range.
Print Assumptions carry_cells_in_range.
Print Assumptions each_in_cell_is_read_by_exactly_one_gate.
Print Assumptions in_cell_indices_lie_below_OUTBIT_BASE.
Print Assumptions PRE_is_shape_only.
Print Assumptions ENVELOPE_is_a_conjunct_of_REL.
Print Assumptions VAL_bounds_8.
Print Assumptions NoEndCarry_is_a_consequence.
Print Assumptions out_limbs_are_pinned_to_public_cells.
