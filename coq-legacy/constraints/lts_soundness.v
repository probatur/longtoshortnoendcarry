(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Soundness: every accepted filling yields a pair the relation accepts. The only input assumption is the
   number of inputs, which every filling meets (bridge_sound; bridge_sound_needs_only_sat states it without
   the assumption). The relation's envelope follows from its other conjuncts and the input's shape (ENVELOPE_is_redundant), and
   the last running carry equals the top output limb (the_last_carry_is_out_k). Also: an accepted filling
   decodes to the anchor pair; no accepted filling has a negative first input, or decodes to a named pair
   whose values agree but whose second running carry is out of range.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.lts_model_gen.
Require Import Generated.lts_wires_gen.
Require Import Generated.lts_scaffold_gen.
Require Import Generated.lts_necessity_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require Import Constraints.bits_kit.
Require Import Constraints.lts_semantic.
Require Import Constraints.lts_model_facts.
Require lts_rule.

Lemma VAL_firstn_S : forall i v,
  lts_rule.VAL (firstn (S i) v)
  = lts_rule.VAL (firstn i v) + lts_rule.B ^ Z.of_nat i * nth i v 0.
Proof.
  induction i as [|i IH]; intro v; destruct v as [|x t].
  - cbn [firstn nth Z.of_nat]. rewrite lts_rule.VAL_nil. ring.
  - cbn [firstn nth Z.of_nat]. rewrite lts_rule.VAL_cons, !lts_rule.VAL_nil. ring.
  - cbn [firstn nth]. rewrite lts_rule.VAL_nil. ring.
  - change (firstn (S (S i)) (x :: t)) with (x :: firstn (S i) t).
    change (firstn (S i) (x :: t)) with (x :: firstn i t).
    change (nth (S i) (x :: t) 0) with (nth i t 0).
    rewrite !lts_rule.VAL_cons, (IH t).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Definition prevc (c : nat -> Z) (i : nat) : Z :=
  match i with O => 0 | S j => c j end.

Theorem prefix_telescopes : forall (s o : list Z) (c : nat -> Z) n,
  (forall i, (i <= n)%nat -> nth i s 0 - nth i o 0 = c i * lts_rule.B - prevc c i) ->
  lts_rule.VAL (firstn (S n) s) - lts_rule.VAL (firstn (S n) o)
  = c n * lts_rule.B ^ Z.of_nat (S n).
Proof.
  intros s o c n. induction n as [|n IH]; intro H.
  - rewrite !(VAL_firstn_S 0). cbn [firstn Z.of_nat]. rewrite lts_rule.VAL_nil.
    pose proof (H 0%nat ltac:(lia)) as H0. cbn [prevc] in H0.
    rewrite Z.pow_0_r. rewrite Z.pow_1_r. lia.
  - rewrite !(VAL_firstn_S (S n)).
    pose proof (IH (fun i Hi => H i ltac:(lia))) as IHn.
    pose proof (H (S n) ltac:(lia)) as Hs. cbn [prevc] in Hs.
    replace (lts_rule.VAL (firstn (S n) s) + lts_rule.B ^ Z.of_nat (S n) * nth (S n) s 0 -
             (lts_rule.VAL (firstn (S n) o) + lts_rule.B ^ Z.of_nat (S n) * nth (S n) o 0))
       with ((lts_rule.VAL (firstn (S n) s) - lts_rule.VAL (firstn (S n) o))
             + lts_rule.B ^ Z.of_nat (S n) * (nth (S n) s 0 - nth (S n) o 0)) by ring.
    rewrite IHn, Hs.
    rewrite (Nat2Z.inj_succ (S n)), (Z.pow_succ_r _ (Z.of_nat (S n))) by lia. ring.
Qed.

Theorem CARRY_of_running : forall (s o : list Z) (c : nat -> Z) n,
  (forall i, (i <= n)%nat -> nth i s 0 - nth i o 0 = c i * lts_rule.B - prevc c i) ->
  lts_rule.CARRY s o n = c n.
Proof.
  intros s o c n H. unfold lts_rule.CARRY.
  rewrite (prefix_telescopes s o c n H). apply Z.div_mul. apply lts_rule.B_pow_nonzero.
Qed.

Lemma VAL_skipn_S : forall i v,
  lts_rule.VAL (skipn i v) = nth i v 0 + lts_rule.B * lts_rule.VAL (skipn (S i) v).
Proof.
  induction i as [|i IH]; intro v; destruct v as [|x t].
  - cbn [skipn nth]. rewrite lts_rule.VAL_nil. ring.
  - cbn [skipn nth]. rewrite lts_rule.VAL_cons. ring.
  - cbn [skipn nth]. rewrite lts_rule.VAL_nil. ring.
  - change (skipn (S i) (x :: t)) with (skipn i t).
    change (skipn (S (S i)) (x :: t)) with (skipn (S i) t).
    change (nth (S i) (x :: t) 0) with (nth i t 0). apply IH.
Qed.

Theorem REL_running : forall inp out,
  lts_rule.VAL out = lts_rule.VAL inp ->
  forall i, nth i inp 0 - nth i out 0
            = lts_rule.CARRY inp out i * lts_rule.B - prevc (lts_rule.CARRY inp out) i.
Proof.
  intros inp out Heq i.
  rewrite (lts_rule.CARRY_is_suffix_difference inp out i Heq).
  pose proof (VAL_skipn_S i inp) as Hi. pose proof (VAL_skipn_S i out) as Ho.

  destruct i as [|j]; cbn [prevc].
  -
    change (skipn 0 inp) with inp in Hi. change (skipn 0 out) with out in Ho.
    rewrite lts_rule.B_value in *. lia.
  - rewrite (lts_rule.CARRY_is_suffix_difference inp out j Heq).
    rewrite lts_rule.B_value in *. lia.
Qed.

Lemma B_value_67 : 2 ^ (lts_rule.N_BITS + lts_rule.LOGK) = 147573952589676412928.
Proof. rewrite lts_rule.carry_width_is_67. reflexivity. Qed.

Lemma limb_nth : forall out i, Forall lts_rule.limb_ok out -> (i < length out)%nat ->
  0 <= nth i out 0 < 18446744073709551616.
Proof.
  intros out i Hf Hi. rewrite Forall_forall in Hf. rewrite <- lts_rule.B_value.
  apply Hf. apply nth_In. exact Hi.
Qed.

Theorem ENVELOPE_is_redundant : forall inp out,
  length inp = lts_rule.K ->
  length out = S lts_rule.K ->
  Forall lts_rule.limb_ok out ->
  lts_rule.VAL out = lts_rule.VAL inp ->
  (forall i, (i < lts_rule.K)%nat ->
     0 <= lts_rule.CARRY inp out i < 2 ^ (lts_rule.N_BITS + lts_rule.LOGK)) ->
  lts_rule.ENVELOPE inp.
Proof.
  intros inp out Hli Hlo Hf Heq Hc.
  rewrite B_value_67 in Hc.
  pose proof (REL_running inp out Heq) as HR.
  unfold lts_rule.ENVELOPE. rewrite lts_rule.LOGK_is_3. unfold lts_rule.N_BITS.
  change (2 ^ (2 * 64 + 3)) with 2722258935367507707706996859454145691648.
  change (2 ^ (64 + 3)) with 147573952589676412928.
  split.
  - pose proof (HR 0%nat) as H0. cbn [prevc] in H0. rewrite lts_rule.B_value in H0.
    pose proof (Hc 0%nat ltac:(unfold lts_rule.K; lia)).
    pose proof (limb_nth out 0 Hf ltac:(rewrite Hlo; unfold lts_rule.K; lia)). lia.
  - intros i Hi. destruct i as [|j]; [ lia | ].
    pose proof (HR (S j)) as H0. cbn [prevc] in H0. rewrite lts_rule.B_value in H0.
    pose proof (Hc (S j) ltac:(unfold lts_rule.K in *; lia)).
    pose proof (Hc j ltac:(unfold lts_rule.K in *; lia)).
    pose proof (limb_nth out (S j) Hf ltac:(rewrite Hlo; unfold lts_rule.K in *; lia)). lia.
Qed.

Theorem the_last_carry_is_out_k : forall inp out,
  length inp = lts_rule.K -> length out = S lts_rule.K ->
  lts_rule.VAL out = lts_rule.VAL inp ->
  lts_rule.CARRY inp out 6 = nth 7 out 0.
Proof.
  intros inp out Hli Hlo Heq.
  rewrite (lts_rule.CARRY_is_suffix_difference inp out 6 Heq).
  rewrite (skipn_all2 inp) by (rewrite Hli; unfold lts_rule.K; lia).
  rewrite (VAL_skipn_S 7 out), (skipn_all2 out) by (rewrite Hlo; unfold lts_rule.K; lia).
  rewrite lts_rule.VAL_nil. ring.
Qed.

Lemma cong_add : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x + y) mod p = (x' + y') mod p.
Proof. intros. rewrite Zplus_mod, H, H0, <- Zplus_mod. reflexivity. Qed.
Lemma cong_sub : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x - y) mod p = (x' - y') mod p.
Proof. intros. rewrite Zminus_mod, H, H0, <- Zminus_mod. reflexivity. Qed.
Lemma cong_mul : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x * y) mod p = (x' * y') mod p.
Proof. intros. rewrite Zmult_mod, H, H0, <- Zmult_mod. reflexivity. Qed.
Lemma cong_opp : forall x x', x mod p = x' mod p -> (- x) mod p = (- x') mod p.
Proof.
  intros x x' H. replace (- x) with (0 - x) by ring. replace (- x') with (0 - x') by ring.
  rewrite Zminus_mod, H, <- Zminus_mod. reflexivity.
Qed.
Lemma cong_dc : forall a c, (dc a c) mod p = (a (c, 0%nat)) mod p.
Proof. intros. unfold dc. apply Zmod_mod. Qed.
Lemma cong_cc : forall a i, (cc a i) mod p = (a ((15 + i)%nat, 0%nat)) mod p.
Proof. intros. unfold cc. apply cong_dc. Qed.

Lemma cong_sdec : forall a c, (sdec (dc a c)) mod p = (a (c, 0%nat)) mod p.
Proof. intros. rewrite sdec_cong. apply cong_dc. Qed.

Ltac cong := repeat first
  [ apply cong_sdec | apply cong_dc | apply cong_cc | apply cong_opp
  | apply cong_mul | apply cong_sub | apply cong_add | reflexivity ].

Lemma p_pos : 0 < p. Proof. pose proof p_ge2. lia. Qed.
Definition E0 (a : Assignment) : Z := sdec (dc a 0) - dc a (7 + 0) - cc a 0 * 18446744073709551616.
Definition RW0 (a : Assignment) : Z := a (0%nat, 0%nat) - a (7%nat, 0%nat) - a (15%nat, 0%nat) * 18446744073709551616.
Definition E1 (a : Assignment) : Z := sdec (dc a 1) - dc a (7 + 1) + cc a 0 - cc a 1 * 18446744073709551616.
Definition RW1 (a : Assignment) : Z := a (1%nat, 0%nat) - a (8%nat, 0%nat) + a (15%nat, 0%nat) - a (16%nat, 0%nat) * 18446744073709551616.
Definition E2 (a : Assignment) : Z := sdec (dc a 2) - dc a (7 + 2) + cc a 1 - cc a 2 * 18446744073709551616.
Definition RW2 (a : Assignment) : Z := a (2%nat, 0%nat) - a (9%nat, 0%nat) + a (16%nat, 0%nat) - a (17%nat, 0%nat) * 18446744073709551616.
Definition E3 (a : Assignment) : Z := sdec (dc a 3) - dc a (7 + 3) + cc a 2 - cc a 3 * 18446744073709551616.
Definition RW3 (a : Assignment) : Z := a (3%nat, 0%nat) - a (10%nat, 0%nat) + a (17%nat, 0%nat) - a (18%nat, 0%nat) * 18446744073709551616.
Definition E4 (a : Assignment) : Z := sdec (dc a 4) - dc a (7 + 4) + cc a 3 - cc a 4 * 18446744073709551616.
Definition RW4 (a : Assignment) : Z := a (4%nat, 0%nat) - a (11%nat, 0%nat) + a (18%nat, 0%nat) - a (19%nat, 0%nat) * 18446744073709551616.
Definition E5 (a : Assignment) : Z := sdec (dc a 5) - dc a (7 + 5) + cc a 4 - cc a 5 * 18446744073709551616.
Definition RW5 (a : Assignment) : Z := a (5%nat, 0%nat) - a (12%nat, 0%nat) + a (19%nat, 0%nat) - a (20%nat, 0%nat) * 18446744073709551616.
Definition E6 (a : Assignment) : Z := sdec (dc a 6) - dc a (7 + 6) + cc a 5 - cc a 6 * 18446744073709551616.
Definition RW6 (a : Assignment) : Z := a (6%nat, 0%nat) - a (13%nat, 0%nat) + a (20%nat, 0%nat) - a (21%nat, 0%nat) * 18446744073709551616.
Definition EEND (a : Assignment) : Z := cc a 6 - dc a (7 + 7).
Definition RWEND (a : Assignment) : Z := a (21%nat, 0%nat) - a (14%nat, 0%nat).

Lemma ev_chain_0 : forall a, eval a (nth 0 tg_chain (EConst 0)) = RW0 a.
Proof. intro a. unfold RW0. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_1 : forall a, eval a (nth 1 tg_chain (EConst 0)) = RW1 a.
Proof. intro a. unfold RW1. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_2 : forall a, eval a (nth 2 tg_chain (EConst 0)) = RW2 a.
Proof. intro a. unfold RW2. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_3 : forall a, eval a (nth 3 tg_chain (EConst 0)) = RW3 a.
Proof. intro a. unfold RW3. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_4 : forall a, eval a (nth 4 tg_chain (EConst 0)) = RW4 a.
Proof. intro a. unfold RW4. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_5 : forall a, eval a (nth 5 tg_chain (EConst 0)) = RW5 a.
Proof. intro a. unfold RW5. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_6 : forall a, eval a (nth 6 tg_chain (EConst 0)) = RW6 a.
Proof. intro a. unfold RW6. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_end : forall a, eval a (nth 0 tg_end (EConst 0)) = RWEND a.
Proof. intro a. unfold RWEND. cbn [nth tg_end eval]. ring. Qed.

Lemma cong_E0 : forall a, (E0 a) mod p = (RW0 a) mod p.
Proof. intro a. unfold E0, RW0. cong. Qed.
Lemma cong_E1 : forall a, (E1 a) mod p = (RW1 a) mod p.
Proof. intro a. unfold E1, RW1. cong. Qed.
Lemma cong_E2 : forall a, (E2 a) mod p = (RW2 a) mod p.
Proof. intro a. unfold E2, RW2. cong. Qed.
Lemma cong_E3 : forall a, (E3 a) mod p = (RW3 a) mod p.
Proof. intro a. unfold E3, RW3. cong. Qed.
Lemma cong_E4 : forall a, (E4 a) mod p = (RW4 a) mod p.
Proof. intro a. unfold E4, RW4. cong. Qed.
Lemma cong_E5 : forall a, (E5 a) mod p = (RW5 a) mod p.
Proof. intro a. unfold E5, RW5. cong. Qed.
Lemma cong_E6 : forall a, (E6 a) mod p = (RW6 a) mod p.
Proof. intro a. unfold E6, RW6. cong. Qed.
Lemma cong_EEND : forall a, (EEND a) mod p = (RWEND a) mod p.
Proof. intro a. unfold EEND, RWEND. cong. Qed.

Lemma E0_zero : forall a, sat deployed_model a -> E0 a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E0, <- ev_chain_0. destruct Hs as [Hg _].
        exact (Hg _ (tg_chain_in 0%nat ltac:(lia))). }
  all: pose proof (sdec_range (dc a 0) (dc_range a 0));
       pose proof (rng_out a Hs 0%nat ltac:(lia));
       pose proof (rng_c a Hs 0%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E0; lia.
Qed.
Lemma E1_zero : forall a, sat deployed_model a -> E1 a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E1, <- ev_chain_1. destruct Hs as [Hg _].
        exact (Hg _ (tg_chain_in 1%nat ltac:(lia))). }
  all: pose proof (sdec_range (dc a 1) (dc_range a 1));
       pose proof (rng_out a Hs 1%nat ltac:(lia));
       pose proof (rng_c a Hs 1%nat ltac:(lia));
       pose proof (rng_c a Hs 0%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E1; lia.
Qed.
Lemma E2_zero : forall a, sat deployed_model a -> E2 a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E2, <- ev_chain_2. destruct Hs as [Hg _].
        exact (Hg _ (tg_chain_in 2%nat ltac:(lia))). }
  all: pose proof (sdec_range (dc a 2) (dc_range a 2));
       pose proof (rng_out a Hs 2%nat ltac:(lia));
       pose proof (rng_c a Hs 2%nat ltac:(lia));
       pose proof (rng_c a Hs 1%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E2; lia.
Qed.
Lemma E3_zero : forall a, sat deployed_model a -> E3 a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E3, <- ev_chain_3. destruct Hs as [Hg _].
        exact (Hg _ (tg_chain_in 3%nat ltac:(lia))). }
  all: pose proof (sdec_range (dc a 3) (dc_range a 3));
       pose proof (rng_out a Hs 3%nat ltac:(lia));
       pose proof (rng_c a Hs 3%nat ltac:(lia));
       pose proof (rng_c a Hs 2%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E3; lia.
Qed.
Lemma E4_zero : forall a, sat deployed_model a -> E4 a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E4, <- ev_chain_4. destruct Hs as [Hg _].
        exact (Hg _ (tg_chain_in 4%nat ltac:(lia))). }
  all: pose proof (sdec_range (dc a 4) (dc_range a 4));
       pose proof (rng_out a Hs 4%nat ltac:(lia));
       pose proof (rng_c a Hs 4%nat ltac:(lia));
       pose proof (rng_c a Hs 3%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E4; lia.
Qed.
Lemma E5_zero : forall a, sat deployed_model a -> E5 a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E5, <- ev_chain_5. destruct Hs as [Hg _].
        exact (Hg _ (tg_chain_in 5%nat ltac:(lia))). }
  all: pose proof (sdec_range (dc a 5) (dc_range a 5));
       pose proof (rng_out a Hs 5%nat ltac:(lia));
       pose proof (rng_c a Hs 5%nat ltac:(lia));
       pose proof (rng_c a Hs 4%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E5; lia.
Qed.
Lemma E6_zero : forall a, sat deployed_model a -> E6 a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_E6, <- ev_chain_6. destruct Hs as [Hg _].
        exact (Hg _ (tg_chain_in 6%nat ltac:(lia))). }
  all: pose proof (sdec_range (dc a 6) (dc_range a 6));
       pose proof (rng_out a Hs 6%nat ltac:(lia));
       pose proof (rng_c a Hs 6%nat ltac:(lia));
       pose proof (rng_c a Hs 5%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold E6; lia.
Qed.
Lemma EEND_zero : forall a, sat deployed_model a -> EEND a = 0.
Proof.
  intros a Hs. apply (no_wrap_zero p); [ exact p_pos | | | ].
  3: { rewrite cong_EEND, <- ev_end. destruct Hs as [Hg _]. exact (Hg _ tg_end_in). }
  all: pose proof (rng_out a Hs 7%nat ltac:(lia));
       pose proof (rng_c a Hs 6%nat ltac:(lia));
       pose proof p_odd; pose proof HALF_big;
       change (2 ^ 140) with 1393796574908163946345982392040522594123776 in *;
       unfold EEND; lia.
Qed.

Theorem circuit_running : forall a, sat deployed_model a ->
  forall i, (i <= 6)%nat ->
    nth i (inp_l a) 0 - nth i (out_l a) 0 = cc a i * lts_rule.B - prevc (cc a) i.
Proof.
  intros a Hs i Hi. rewrite (inp_l_nth a i ltac:(lia)), (out_l_nth a i ltac:(lia)).
  rewrite lts_rule.B_value.
  destruct i as [|i]; [ pose proof (E0_zero a Hs) as HE; unfold E0 in HE; cbn [prevc]; lia | ].
  destruct i as [|i]; [ pose proof (E1_zero a Hs) as HE; unfold E1 in HE; cbn [prevc]; lia | ].
  destruct i as [|i]; [ pose proof (E2_zero a Hs) as HE; unfold E2 in HE; cbn [prevc]; lia | ].
  destruct i as [|i]; [ pose proof (E3_zero a Hs) as HE; unfold E3 in HE; cbn [prevc]; lia | ].
  destruct i as [|i]; [ pose proof (E4_zero a Hs) as HE; unfold E4 in HE; cbn [prevc]; lia | ].
  destruct i as [|i]; [ pose proof (E5_zero a Hs) as HE; unfold E5 in HE; cbn [prevc]; lia | ].
  destruct i as [|i]; [ pose proof (E6_zero a Hs) as HE; unfold E6 in HE; cbn [prevc]; lia | ].
  lia.
Qed.

Lemma inp_l_firstn : forall a, firstn 7 (inp_l a) = inp_l a.
Proof. reflexivity. Qed.
Lemma out_l_skipn : forall a, skipn 7 (out_l a) = [dc a (7 + 7)].
Proof. reflexivity. Qed.

Theorem values_agree : forall a, sat deployed_model a ->
  lts_rule.VAL (out_l a) = lts_rule.VAL (inp_l a).
Proof.
  intros a Hs.
  pose proof (prefix_telescopes (inp_l a) (out_l a) (cc a) 6
                (fun i Hi => circuit_running a Hs i Hi)) as T.
  rewrite inp_l_firstn in T.
  pose proof (lts_rule.VAL_firstn_skipn 7 (out_l a)) as S7.
  rewrite out_l_skipn in S7.
  pose proof (EEND_zero a Hs) as HE. unfold EEND in HE.
  assert (Hv : lts_rule.VAL [dc a (7 + 7)] = dc a (7 + 7))
    by (rewrite lts_rule.VAL_cons, lts_rule.VAL_nil; ring).
  rewrite Hv in S7.
  assert (HB : cc a 6 * lts_rule.B ^ Z.of_nat 7 = dc a (7 + 7) * lts_rule.B ^ Z.of_nat 7)
    by (f_equal; lia).
  lia.
Qed.

Theorem CARRY_is_the_carry_cell : forall a, sat deployed_model a ->
  forall i, (i <= 6)%nat -> lts_rule.CARRY (inp_l a) (out_l a) i = cc a i.
Proof.
  intros a Hs i Hi. apply CARRY_of_running.
  intros j Hj. apply circuit_running; [ exact Hs | lia ].
Qed.

(* Soundness, for every accepted filling (the input assumption, 7 values, holds for all of them). *)
Theorem bridge_sound : forall a,
  sat deployed_model a ->
  CANON_lts a ->
  lts_rule.PRE_lts (inp_l a) ->
  lts_rule.REL_lts (inp_l a) (out_l a).
Proof.
  intros a Hs _ _.
  pose proof (values_agree a Hs) as Hval.
  assert (Hcb : forall i, (i < lts_rule.K)%nat ->
            0 <= lts_rule.CARRY (inp_l a) (out_l a) i < 2 ^ (lts_rule.N_BITS + lts_rule.LOGK)).
  { intros i Hi. unfold lts_rule.K in Hi.
    rewrite (CARRY_is_the_carry_cell a Hs i ltac:(lia)).
    exact (carry_cells_in_range a Hs i Hi). }
  split; [ reflexivity | ].
  split; [ exact (out_limbs_in_range a Hs) | ].
  split; [ exact Hval | ].
  split; [ exact Hcb | ].

  exact (ENVELOPE_is_redundant (inp_l a) (out_l a) (inp_l_length a) (out_l_length a)
           (out_limbs_in_range a Hs) Hval Hcb).
Qed.

Theorem bridge_sound_needs_only_sat : forall a,
  sat deployed_model a -> lts_rule.REL_lts (inp_l a) (out_l a).
Proof. intros a Hs. exact (bridge_sound a Hs (CANON_is_free a) (inp_l_length a)). Qed.

Theorem nonvacuity_the_honest_row_decodes_to_the_anchor :
  sat deployed_model wit_honest_lts
  /\ inp_l wit_honest_lts = lts_rule.OK_IN
  /\ out_l wit_honest_lts = lts_rule.OK_OUT.
Proof.
  split; [ exact honest_full_sat_lts | ].
  split; vm_compute; reflexivity.
Qed.

Theorem nonvacuity_the_anchor_is_ACCEPTED :
  lts_rule.REL_lts (inp_l wit_honest_lts) (out_l wit_honest_lts).
Proof. exact (bridge_sound_needs_only_sat _ honest_full_sat_lts). Qed.

Theorem no_satisfying_row_has_a_negative_in0 : forall a,
  sat deployed_model a -> 0 <= nth 0 (inp_l a) 0.
Proof.
  intros a Hs. destruct (bridge_sound_needs_only_sat a Hs) as [_ [_ [_ [_ [[H _] _]]]]].
  exact H.
Qed.

Theorem no_satisfying_row_decodes_to_cx2 : forall a,
  sat deployed_model a ->
  ~ (inp_l a = lts_rule.CX2_IN /\ out_l a = lts_rule.CX2_OUT).
Proof.
  intros a Hs [Hi Ho]. apply lts_rule.cx2_not_rel.
  rewrite <- Hi, <- Ho. exact (bridge_sound_needs_only_sat a Hs).
Qed.

Print Assumptions VAL_firstn_S.
Print Assumptions prefix_telescopes.
Print Assumptions CARRY_of_running.
Print Assumptions VAL_skipn_S.
Print Assumptions REL_running.
Print Assumptions ENVELOPE_is_redundant.
Print Assumptions the_last_carry_is_out_k.
Print Assumptions circuit_running.
Print Assumptions values_agree.
Print Assumptions CARRY_is_the_carry_cell.
Print Assumptions bridge_sound.
Print Assumptions bridge_sound_needs_only_sat.
Print Assumptions nonvacuity_the_honest_row_decodes_to_the_anchor.
Print Assumptions nonvacuity_the_anchor_is_ACCEPTED.
Print Assumptions no_satisfying_row_has_a_negative_in0.
Print Assumptions no_satisfying_row_decodes_to_cx2.
