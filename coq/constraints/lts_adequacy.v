(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Completeness (bridge_complete), and soundness and completeness as one theorem: for every input of 7
   values, the circuit accepts a pair exactly when the relation does (policy_adequacy_lts; the two directions
   stated separately in policy_adequacy_lts_conj). Acceptance (accepts_lts) is defined on signed values.
   Also: a pair with a negative input is accepted (the_wrap_band_row_is_ACCEPTED); acceptance does not reduce
   inputs modulo p (accepts_is_not_mod_q_invariant); and no output is accepted for an input whose first
   value is -1 (no_out_is_accepted_for_the_neg0_input).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.lts_model_gen.
Require Import Generated.lts_wires_gen.
Require Import Generated.lts_scaffold_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require Import Constraints.bits_kit.
Require Import Constraints.lts_semantic.
Require Import Constraints.lts_model_facts.
Require Import Constraints.lts_soundness.
Require lts_rule.

Lemma bitsum_ext : forall n (f g : nat -> Z),
  (forall j, (j < n)%nat -> f j = g j) -> bitsum f n = bitsum g n.
Proof.
  induction n as [|n IH]; intros f g H; [ reflexivity | ].
  cbn [bitsum]. rewrite (IH f g) by (intros j Hj; apply H; lia).
  rewrite (H n) by lia. reflexivity.
Qed.

Lemma bitsum67_bits_of : forall d, 0 <= d < 147573952589676412928 ->
  bitsum (bits_of d) 67 = d.
Proof.
  intros d [Hlo Hhi]. rewrite (bitsum_bits_of 67 d Hlo).
  rewrite wpow67_val. apply Z.mod_small. lia.
Qed.

Lemma in_firstn_or_skipn : forall (A : Type) (n : nat) (l : list A) (x : A),
  In x l -> In x (firstn n l) \/ In x (skipn n l).
Proof. intros A n l x H. rewrite <- (firstn_skipn n l) in H. apply in_app_or. exact H. Qed.

Lemma nat_split : forall k q r, (0 < k)%nat -> (r < k)%nat ->
  ((q * k + r) / k = q)%nat /\ ((q * k + r) mod k = r)%nat.
Proof.
  intros k q r Hk Hr.
  assert (Hd : ((q * k + r) / k = q)%nat).
  { rewrite Nat.div_add_l by lia. rewrite (Nat.div_small r k Hr). lia. }
  split; [ exact Hd | ].
  pose proof (Nat.div_mod_eq (q * k + r) k) as H. rewrite Hd in H. lia.
Qed.

Lemma list_seven : forall (v : list Z), length v = 7%nat ->
  v = [nth 0 v 0; nth 1 v 0; nth 2 v 0; nth 3 v 0; nth 4 v 0; nth 5 v 0; nth 6 v 0].
Proof.
  intros v Hl. destruct v as [|a [|b [|c [|d [|e [|f [|g [|h v]]]]]]]]; cbn [length] in Hl; try lia.
  reflexivity.
Qed.

Lemma list_eight : forall (v : list Z), length v = 8%nat ->
  v = [nth 0 v 0; nth 1 v 0; nth 2 v 0; nth 3 v 0; nth 4 v 0; nth 5 v 0; nth 6 v 0; nth 7 v 0].
Proof.
  intros v Hl. destruct v as [|a [|b [|c [|d [|e [|f [|g [|h [|i v]]]]]]]]]; cbn [length] in Hl; try lia.
  reflexivity.
Qed.

Lemma B64_lt_p : 18446744073709551616 < p.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Definition cellv (ins outs cs : list Z) (c : nat) : Z :=
  if (c <? 7)%nat then nth c ins 0
  else if (c <? 15)%nat then nth (c - 7) outs 0
  else if (c <? 22)%nat then nth (c - 15) cs 0
  else if (c <? 534)%nat then bits_of (nth ((c - 22) / 64) outs 0) ((c - 22) mod 64)
  else if (c <? 1003)%nat then bits_of (nth ((c - 534) / 67) cs 0) ((c - 534) mod 67)
  else 0.

Definition mkW (ins outs cs : list Z) : Assignment :=
  fun cl => if Nat.eqb (fst cl) 3000 then nth (snd cl) outs 0
            else if Nat.eqb (snd cl) 0 then cellv ins outs cs (fst cl) else 0.

Section Builder.
Variables ins outs cs : list Z.

Lemma mkW_cell : forall c, (c < 1003)%nat -> mkW ins outs cs (c, 0%nat) = cellv ins outs cs c.
Proof.
  intros c Hc. unfold mkW. cbn [fst snd].
  rewrite (proj2 (Nat.eqb_neq c 3000) ltac:(lia)). reflexivity.
Qed.

Lemma mkW_in : forall c, (c < 7)%nat -> mkW ins outs cs (c, 0%nat) = nth c ins 0.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_lt c 7) Hc). reflexivity.
Qed.

Lemma mkW_out : forall c, (7 <= c < 15)%nat -> mkW ins outs cs (c, 0%nat) = nth (c - 7) outs 0.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 7) ltac:(lia)), (proj2 (Nat.ltb_lt c 15) ltac:(lia)). reflexivity.
Qed.

Lemma mkW_cc : forall c, (15 <= c < 22)%nat -> mkW ins outs cs (c, 0%nat) = nth (c - 15) cs 0.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 7) ltac:(lia)), (proj2 (Nat.ltb_ge c 15) ltac:(lia)),
          (proj2 (Nat.ltb_lt c 22) ltac:(lia)). reflexivity.
Qed.

Lemma mkW_pub : forall j, mkW ins outs cs (3000%nat, j) = nth j outs 0.
Proof. intro j. reflexivity. Qed.

Lemma mkW_bool : forall c, (22 <= c < 1003)%nat ->
  mkW ins outs cs (c, 0%nat) = 0 \/ mkW ins outs cs (c, 0%nat) = 1.
Proof.
  intros c Hc. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 7) ltac:(lia)), (proj2 (Nat.ltb_ge c 15) ltac:(lia)),
          (proj2 (Nat.ltb_ge c 22) ltac:(lia)).
  destruct (c <? 534)%nat; [ apply bits_of_bool | ].
  rewrite (proj2 (Nat.ltb_lt c 1003) ltac:(lia)). apply bits_of_bool.
Qed.

Lemma bat_out : forall i j, (i < 8)%nat -> (j < 64)%nat ->
  bits_at (mkW ins outs cs) (22 + 64 * i)%nat j = bits_of (nth i outs 0) j.
Proof.
  intros i j Hi Hj. unfold bits_at. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge (22 + 64 * i + j) 7) ltac:(lia)),
          (proj2 (Nat.ltb_ge (22 + 64 * i + j) 15) ltac:(lia)),
          (proj2 (Nat.ltb_ge (22 + 64 * i + j) 22) ltac:(lia)),
          (proj2 (Nat.ltb_lt (22 + 64 * i + j) 534) ltac:(lia)).
  replace (22 + 64 * i + j - 22)%nat with (i * 64 + j)%nat by lia.
  destruct (nat_split 64 i j ltac:(lia) Hj) as [Hd Hm]. rewrite Hd, Hm. reflexivity.
Qed.

Lemma bat_c : forall i j, (i < 7)%nat -> (j < 67)%nat ->
  bits_at (mkW ins outs cs) (534 + 67 * i)%nat j = bits_of (nth i cs 0) j.
Proof.
  intros i j Hi Hj. unfold bits_at. rewrite mkW_cell by lia. unfold cellv.
  rewrite (proj2 (Nat.ltb_ge (534 + 67 * i + j) 7) ltac:(lia)),
          (proj2 (Nat.ltb_ge (534 + 67 * i + j) 15) ltac:(lia)),
          (proj2 (Nat.ltb_ge (534 + 67 * i + j) 22) ltac:(lia)),
          (proj2 (Nat.ltb_ge (534 + 67 * i + j) 534) ltac:(lia)),
          (proj2 (Nat.ltb_lt (534 + 67 * i + j) 1003) ltac:(lia)).
  replace (534 + 67 * i + j - 534)%nat with (i * 67 + j)%nat by lia.
  destruct (nat_split 67 i j ltac:(lia) Hj) as [Hd Hm]. rewrite Hd, Hm. reflexivity.
Qed.

Lemma g_bool : forall j, (j < 981)%nat -> gate_holds (mkW ins outs cs) (bool_gate (22 + j)%nat).
Proof.
  intros j Hj. unfold gate_holds, bool_gate. cbn [eval].
  destruct (mkW_bool (22 + j)%nat ltac:(lia)) as [E|E]; rewrite E;
    [ replace (0 * (0 - 1)) with 0 by ring | replace (1 * (1 - 1)) with 0 by ring ];
    apply Zmod_0_l.
Qed.

Theorem mkW_copies_hold : copy_holds (mkW ins outs cs) deployed_copy.
Proof.
  intros e Hin. cbn [deployed_copy In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [ cbn [fst snd]; rewrite mkW_out by lia; reflexivity | ]).
  destruct Hin.
Qed.

End Builder.

Definition carries_of (inp out : list Z) : list Z :=
  map (lts_rule.CARRY inp out) (seq 0 7).

Definition ASG (inp out : list Z) : Assignment := mkW inp out (carries_of inp out).

Lemma nth_carries : forall inp out k, (k < 7)%nat ->
  nth k (carries_of inp out) 0 = lts_rule.CARRY inp out k.
Proof. intros inp out k Hk. do 7 (destruct k as [|k]; [ reflexivity | ]). lia. Qed.

Section Witness.
Variables inp out : list Z.

Lemma g_rec_out : lts_rule.REL_lts inp out ->
  forall k, (k < 8)%nat -> gate_holds (ASG inp out) (nth k tg_rec_out (EConst 0)).
Proof.
  intros [Hlo [Hf _]] k Hk. unfold gate_holds, ASG.
  destruct k as [|k].
  { rewrite ev_rec_out_0.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 22) (bits_of (nth 0 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 0 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 0 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 7) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_1.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 86) (bits_of (nth 1 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 1 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 1 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 8) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_2.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 150) (bits_of (nth 2 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 2 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 2 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 9) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_3.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 214) (bits_of (nth 3 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 3 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 3 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 10) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_4.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 278) (bits_of (nth 4 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 4 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 4 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 11) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_5.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 342) (bits_of (nth 5 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 5 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 5 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 12) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_6.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 406) (bits_of (nth 6 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 6 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 6 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 13) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_out_7.
    rewrite (bitsum_ext 64 (bits_at (mkW inp out (carries_of inp out)) 470) (bits_of (nth 7 out 0))
              (fun j Hj => bat_out inp out (carries_of inp out) 7 j ltac:(lia) Hj)).
    rewrite bitsum64_bits_of by (pose proof (limb_nth out 7 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)); lia).
    rewrite (mkW_out inp out (carries_of inp out) 14) by lia. cbn [Nat.sub].
    rewrite Z.sub_diag. apply Zmod_0_l. }
  lia.
Qed.

Lemma carry_bound : lts_rule.REL_lts inp out ->
  forall k, (k < 7)%nat -> 0 <= lts_rule.CARRY inp out k < 147573952589676412928.
Proof.
  intros [_ [_ [_ [Hc _]]]] k Hk. rewrite <- B_value_67. apply Hc. unfold lts_rule.K. lia.
Qed.

Lemma g_rec_c : lts_rule.REL_lts inp out ->
  forall k, (k < 7)%nat -> gate_holds (ASG inp out) (nth k tg_rec_c (EConst 0)).
Proof.
  intros HR k Hk. unfold gate_holds, ASG.
  destruct k as [|k].
  { rewrite ev_rec_c_0.
    rewrite (bitsum_ext 67 (bits_at (mkW inp out (carries_of inp out)) 534) (bits_of (nth 0 (carries_of inp out) 0))
              (fun j Hj => bat_c inp out (carries_of inp out) 0 j ltac:(lia) Hj)).
    rewrite (nth_carries inp out 0) by lia.
    rewrite bitsum67_bits_of by (apply (carry_bound HR 0%nat); lia).
    rewrite (mkW_cc inp out (carries_of inp out) 15) by lia. cbn [Nat.sub].
    rewrite (nth_carries inp out 0) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_1.
    rewrite (bitsum_ext 67 (bits_at (mkW inp out (carries_of inp out)) 601) (bits_of (nth 1 (carries_of inp out) 0))
              (fun j Hj => bat_c inp out (carries_of inp out) 1 j ltac:(lia) Hj)).
    rewrite (nth_carries inp out 1) by lia.
    rewrite bitsum67_bits_of by (apply (carry_bound HR 1%nat); lia).
    rewrite (mkW_cc inp out (carries_of inp out) 16) by lia. cbn [Nat.sub].
    rewrite (nth_carries inp out 1) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_2.
    rewrite (bitsum_ext 67 (bits_at (mkW inp out (carries_of inp out)) 668) (bits_of (nth 2 (carries_of inp out) 0))
              (fun j Hj => bat_c inp out (carries_of inp out) 2 j ltac:(lia) Hj)).
    rewrite (nth_carries inp out 2) by lia.
    rewrite bitsum67_bits_of by (apply (carry_bound HR 2%nat); lia).
    rewrite (mkW_cc inp out (carries_of inp out) 17) by lia. cbn [Nat.sub].
    rewrite (nth_carries inp out 2) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_3.
    rewrite (bitsum_ext 67 (bits_at (mkW inp out (carries_of inp out)) 735) (bits_of (nth 3 (carries_of inp out) 0))
              (fun j Hj => bat_c inp out (carries_of inp out) 3 j ltac:(lia) Hj)).
    rewrite (nth_carries inp out 3) by lia.
    rewrite bitsum67_bits_of by (apply (carry_bound HR 3%nat); lia).
    rewrite (mkW_cc inp out (carries_of inp out) 18) by lia. cbn [Nat.sub].
    rewrite (nth_carries inp out 3) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_4.
    rewrite (bitsum_ext 67 (bits_at (mkW inp out (carries_of inp out)) 802) (bits_of (nth 4 (carries_of inp out) 0))
              (fun j Hj => bat_c inp out (carries_of inp out) 4 j ltac:(lia) Hj)).
    rewrite (nth_carries inp out 4) by lia.
    rewrite bitsum67_bits_of by (apply (carry_bound HR 4%nat); lia).
    rewrite (mkW_cc inp out (carries_of inp out) 19) by lia. cbn [Nat.sub].
    rewrite (nth_carries inp out 4) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_5.
    rewrite (bitsum_ext 67 (bits_at (mkW inp out (carries_of inp out)) 869) (bits_of (nth 5 (carries_of inp out) 0))
              (fun j Hj => bat_c inp out (carries_of inp out) 5 j ltac:(lia) Hj)).
    rewrite (nth_carries inp out 5) by lia.
    rewrite bitsum67_bits_of by (apply (carry_bound HR 5%nat); lia).
    rewrite (mkW_cc inp out (carries_of inp out) 20) by lia. cbn [Nat.sub].
    rewrite (nth_carries inp out 5) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_rec_c_6.
    rewrite (bitsum_ext 67 (bits_at (mkW inp out (carries_of inp out)) 936) (bits_of (nth 6 (carries_of inp out) 0))
              (fun j Hj => bat_c inp out (carries_of inp out) 6 j ltac:(lia) Hj)).
    rewrite (nth_carries inp out 6) by lia.
    rewrite bitsum67_bits_of by (apply (carry_bound HR 6%nat); lia).
    rewrite (mkW_cc inp out (carries_of inp out) 21) by lia. cbn [Nat.sub].
    rewrite (nth_carries inp out 6) by lia.
    rewrite Z.sub_diag. apply Zmod_0_l. }
  lia.
Qed.

Lemma g_chain : lts_rule.REL_lts inp out ->
  forall k, (k < 7)%nat -> gate_holds (ASG inp out) (nth k tg_chain (EConst 0)).
Proof.
  intros [_ [_ [Hv _]]] k Hk. unfold gate_holds, ASG.
  pose proof (REL_running inp out Hv) as HR.
  destruct k as [|k].
  { rewrite ev_chain_0. unfold RW0.
    rewrite (mkW_in inp out (carries_of inp out) 0) by lia.
    rewrite (mkW_out inp out (carries_of inp out) 7) by lia.
    rewrite (mkW_cc inp out (carries_of inp out) 15) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HR 0%nat) as H. cbn [prevc] in H. rewrite lts_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_1. unfold RW1.
    rewrite (mkW_in inp out (carries_of inp out) 1) by lia.
    rewrite (mkW_out inp out (carries_of inp out) 8) by lia.
    rewrite (mkW_cc inp out (carries_of inp out) 15) by lia; rewrite (mkW_cc inp out (carries_of inp out) 16) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HR 1%nat) as H. cbn [prevc] in H. rewrite lts_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_2. unfold RW2.
    rewrite (mkW_in inp out (carries_of inp out) 2) by lia.
    rewrite (mkW_out inp out (carries_of inp out) 9) by lia.
    rewrite (mkW_cc inp out (carries_of inp out) 16) by lia; rewrite (mkW_cc inp out (carries_of inp out) 17) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HR 2%nat) as H. cbn [prevc] in H. rewrite lts_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_3. unfold RW3.
    rewrite (mkW_in inp out (carries_of inp out) 3) by lia.
    rewrite (mkW_out inp out (carries_of inp out) 10) by lia.
    rewrite (mkW_cc inp out (carries_of inp out) 17) by lia; rewrite (mkW_cc inp out (carries_of inp out) 18) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HR 3%nat) as H. cbn [prevc] in H. rewrite lts_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_4. unfold RW4.
    rewrite (mkW_in inp out (carries_of inp out) 4) by lia.
    rewrite (mkW_out inp out (carries_of inp out) 11) by lia.
    rewrite (mkW_cc inp out (carries_of inp out) 18) by lia; rewrite (mkW_cc inp out (carries_of inp out) 19) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HR 4%nat) as H. cbn [prevc] in H. rewrite lts_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_5. unfold RW5.
    rewrite (mkW_in inp out (carries_of inp out) 5) by lia.
    rewrite (mkW_out inp out (carries_of inp out) 12) by lia.
    rewrite (mkW_cc inp out (carries_of inp out) 19) by lia; rewrite (mkW_cc inp out (carries_of inp out) 20) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HR 5%nat) as H. cbn [prevc] in H. rewrite lts_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  destruct k as [|k].
  { rewrite ev_chain_6. unfold RW6.
    rewrite (mkW_in inp out (carries_of inp out) 6) by lia.
    rewrite (mkW_out inp out (carries_of inp out) 13) by lia.
    rewrite (mkW_cc inp out (carries_of inp out) 20) by lia; rewrite (mkW_cc inp out (carries_of inp out) 21) by lia.
    cbn [Nat.sub]. rewrite !nth_carries by lia.
    pose proof (HR 6%nat) as H. cbn [prevc] in H. rewrite lts_rule.B_value in H.
    replace (_ - _) with 0 by lia. apply Zmod_0_l. }
  lia.
Qed.

Lemma g_end : lts_rule.PRE_lts inp -> lts_rule.REL_lts inp out ->
  gate_holds (ASG inp out) (nth 0 tg_end (EConst 0)).
Proof.
  intros Hpre [Hlo [_ [Hv _]]]. unfold gate_holds, ASG.
  rewrite ev_end. unfold RWEND.
  rewrite (mkW_cc inp out (carries_of inp out) 21) by lia.
  rewrite (mkW_out inp out (carries_of inp out) 14) by lia.
  cbn [Nat.sub]. rewrite nth_carries by lia.
  rewrite (the_last_carry_is_out_k inp out Hpre Hlo Hv).
  rewrite Z.sub_diag. apply Zmod_0_l.
Qed.

Theorem all_gates_hold : lts_rule.PRE_lts inp -> lts_rule.REL_lts inp out ->
  gates_hold (ASG inp out) deployed_gates.
Proof.
  intros Hpre HR g Hin.
  destruct (in_firstn_or_skipn _ 981 deployed_gates g Hin) as [Hh|Ht].
  - rewrite head_is_the_booleanity_bank in Hh.
    apply in_map_iff in Hh. destruct Hh as [j [Hj Hseq]].
    apply in_seq in Hseq. subst g. apply g_bool. lia.
  - change (skipn 981 deployed_gates) with tail_gates in Ht.
    rewrite <- tail_split_is_a_partition in Ht.
    repeat (apply in_app_or in Ht; destruct Ht as [Ht|Ht]).
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_out_len in Hk. subst g. apply g_rec_out; assumption.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_c_len in Hk. subst g. apply g_rec_c; assumption.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_chain_len in Hk. subst g. apply g_chain; assumption.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_end_len in Hk. assert (k = 0%nat) by lia. subst k g.
      apply g_end; assumption.
Qed.

Theorem ASG_sat : lts_rule.PRE_lts inp -> lts_rule.REL_lts inp out ->
  sat deployed_model (ASG inp out).
Proof.
  intros Hpre HR. split; [ exact (all_gates_hold Hpre HR) | apply mkW_copies_hold ].
Qed.

Lemma envelope_nth : lts_rule.ENVELOPE inp ->
  forall i, (i < 7)%nat -> - 2 ^ 67 < nth i inp 0 < 2 ^ 131.
Proof.
  intros [H0 H] i Hi. rewrite lts_rule.LOGK_is_3 in *. unfold lts_rule.N_BITS in *.
  change (2 ^ (2 * 64 + 3)) with (2 ^ 131) in *. change (2 ^ (64 + 3)) with (2 ^ 67) in *.
  destruct i as [|j].
  - assert (0 < 2 ^ 67) by (apply Z.pow_pos_nonneg; lia). lia.
  - apply H. unfold lts_rule.K. lia.
Qed.

Lemma decode_in : lts_rule.PRE_lts inp -> lts_rule.REL_lts inp out ->
  inp_l (ASG inp out) = inp.
Proof.
  intros Hpre [_ [_ [_ [_ Henv]]]].
  pose proof (envelope_nth Henv) as HE.
  unfold inp_l, in_cells, dc, ASG. cbn [map].
  rewrite !(mkW_in inp out (carries_of inp out)) by lia.
  rewrite !sdec_exact_on_the_envelope by (apply HE; lia).
  symmetry. apply list_seven. exact Hpre.
Qed.

Lemma decode_out : lts_rule.REL_lts inp out -> out_l (ASG inp out) = out.
Proof.
  intros [Hlo [Hf _]].
  assert (HR : forall j, (j < 8)%nat -> (nth j out 0) mod p = nth j out 0).
  { intros j Hj. apply Z.mod_small.
    pose proof (limb_nth out j Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)).
    pose proof B64_lt_p. lia. }
  unfold out_l, dc, ASG.
  rewrite !(mkW_out inp out (carries_of inp out)) by lia. cbn [Nat.sub].
  rewrite !HR by lia.
  symmetry. apply list_eight. exact Hlo.
Qed.

End Witness.

(* Completeness: for every input of 7 values and every output the relation accepts with it, there is a
   filling the circuit accepts that reads back as exactly that pair. *)
Theorem bridge_complete : forall inp out,
  lts_rule.PRE_lts inp ->
  lts_rule.REL_lts inp out ->
  exists al, sat deployed_model al /\ CANON_lts al
             /\ inp_l al = inp /\ out_l al = out.
Proof.
  intros inp out Hpre HR. exists (ASG inp out).
  split; [ exact (ASG_sat inp out Hpre HR) | ].
  split; [ apply CANON_is_free | ].
  split; [ exact (decode_in inp out Hpre HR) | exact (decode_out inp out HR) ].
Qed.

(* Acceptance of an integer pair: every input lies within (p - 1)/2 of zero, and some accepted filling
   reads back as exactly the pair, its input cells read signed and its output cells canonically. *)
Definition accepts_lts (inp out : list Z) : Prop :=
  (forall i, (i < lts_rule.K)%nat -> - ((p - 1) / 2) <= nth i inp 0 <= (p - 1) / 2)
  /\ exists al, sat deployed_model al /\ CANON_lts al
                /\ map sdec (in_cells al) = inp /\ out_l al = out.

(* Soundness and completeness as one theorem. *)
Theorem policy_adequacy_lts : lts_rule.adequate accepts_lts.
Proof.
  intros inp out Hpre. split.
  - intros [_ [al [Hs [Hc [Hin Hout]]]]].
    change (map sdec (in_cells al)) with (inp_l al) in Hin.
    rewrite <- Hin, <- Hout. exact (bridge_sound al Hs Hc (inp_l_length al)).
  - intros HR. split.
    + intros i Hi. destruct HR as [_ [_ [_ [_ Henv]]]].
      pose proof (envelope_nth inp Henv i Hi). pose proof envelope_fits_signed_range.
      unfold HALF in *. assert (2 ^ 67 <= 2 ^ 131) by (apply Z.pow_le_mono_r; lia). lia.
    + destruct (bridge_complete inp out Hpre HR) as [al [Hs [Hc [Hin Hout]]]].
      exists al. split; [ exact Hs | ]. split; [ exact Hc | ].
      split; [ exact Hin | exact Hout ].
Qed.

Theorem policy_adequacy_lts_conj :
  (forall a, sat deployed_model a -> CANON_lts a -> lts_rule.PRE_lts (inp_l a) ->
             lts_rule.REL_lts (inp_l a) (out_l a))
  /\
  (forall inp out, lts_rule.PRE_lts inp -> lts_rule.REL_lts inp out ->
     exists al, sat deployed_model al /\ CANON_lts al /\ inp_l al = inp /\ out_l al = out).
Proof. split; [ exact bridge_sound | exact bridge_complete ]. Qed.

Theorem the_wrap_band_row_is_ACCEPTED : accepts_lts lts_rule.WRAP_IN lts_rule.WRAP_OUT.
Proof. apply policy_adequacy_lts; [ reflexivity | exact lts_rule.wrap_row_rel ]. Qed.

Theorem the_wrap_cell_holds_q_minus_2_67_plus_1 :
  dc (ASG lts_rule.WRAP_IN lts_rule.WRAP_OUT) 1 = p - 2 ^ 67 + 1
  /\ nth 1 (inp_l (ASG lts_rule.WRAP_IN lts_rule.WRAP_OUT)) 0 = - (2 ^ 67 - 1).
Proof. split; vm_compute; reflexivity. Qed.

Theorem completeness_hypothesis_is_INHABITED :
  lts_rule.PRE_lts lts_rule.CONV_IN /\ lts_rule.REL_lts lts_rule.CONV_IN lts_rule.CONV_OUT.
Proof. split; [ reflexivity | exact lts_rule.conv_row_rel ]. Qed.

Theorem accepts_is_not_mod_q_invariant :
  accepts_lts lts_rule.OK_IN lts_rule.OK_OUT
  /\ ~ accepts_lts [2 ^ 130 + p; 0; 0; 0; 0; 0; 0] lts_rule.OK_OUT.
Proof.
  split.
  - apply policy_adequacy_lts; [ reflexivity | exact lts_rule.ok_row_rel ].
  - intros [H _]. specialize (H 0%nat ltac:(unfold lts_rule.K; lia)).
    cbn [nth] in H. vm_compute in H. destruct H as [_ H]. apply H. reflexivity.
Qed.

Theorem no_out_is_accepted_for_the_neg0_input : forall out,
  ~ accepts_lts [-1; 0; 0; 0; 0; 0; 0] out.
Proof.
  intros out Hacc. apply (lts_rule.neg0_not_rel out).
  apply (proj1 (policy_adequacy_lts [-1; 0; 0; 0; 0; 0; 0] out ltac:(reflexivity))).
  exact Hacc.
Qed.

Print Assumptions bitsum67_bits_of.
Print Assumptions mkW_copies_hold.
Print Assumptions all_gates_hold.
Print Assumptions ASG_sat.
Print Assumptions decode_in.
Print Assumptions decode_out.
Print Assumptions bridge_complete.
Print Assumptions policy_adequacy_lts.
Print Assumptions policy_adequacy_lts_conj.
Print Assumptions the_wrap_band_row_is_ACCEPTED.
Print Assumptions the_wrap_cell_holds_q_minus_2_67_plus_1.
Print Assumptions completeness_hypothesis_is_INHABITED.
Print Assumptions accepts_is_not_mod_q_invariant.
Print Assumptions no_out_is_accepted_for_the_neg0_input.
