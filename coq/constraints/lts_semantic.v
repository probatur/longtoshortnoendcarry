(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Reading the pair off a filling: each cell as its canonical remainder modulo p (dc); the input cells read as
   signed integers by the half-field rule (sdec: a residue above (p - 1)/2 reads as that residue minus p),
   giving inp_l; the output cells read canonically, giving out_l; and the canonicity predicate CANON_lts, which
   every filling satisfies (CANON_is_free). Also the public cells' agreement with the output cells, derived
   from the copy constraints (answer_pins_are_DERIVED), the checked count of polynomial constraints (dg_len),
   the range bounds every accepted filling puts on its output cells and its seven carry cells (rng_out,
   rng_c), and the Pasta prime's room for the signed reading (envelope_fits_signed_range).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.lts_model_gen.
Require Import Generated.lts_wires_gen.
Require Import Generated.lts_scaffold_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require lts_rule.

Lemma p_eq_pasta : p = pasta_p.
Proof. reflexivity. Qed.

Lemma p_prime : prime p.
Proof. rewrite p_eq_pasta. exact pasta_prime. Qed.

Lemma p_ge2 : 2 <= p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition HALF : Z := (p - 1) / 2.

Lemma p_odd : p = 2 * HALF + 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pasta_margin : 2 ^ 132 - 1 <= p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem envelope_fits_signed_range : 2 ^ 131 - 1 <= HALF.
Proof.
  pose proof pasta_margin as Hm. rewrite p_odd in Hm.
  assert (H2 : 2 ^ 132 = 2 * 2 ^ 131) by reflexivity.
  set (X := 2 ^ 131) in *. lia.
Qed.

Lemma HALF_big : 2 ^ 140 <= HALF.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition sdec (x : Z) : Z := if x <=? HALF then x else x - p.

Theorem sdec_range : forall x, 0 <= x < p -> - HALF <= sdec x <= HALF.
Proof.
  intros x Hx. pose proof p_odd. unfold sdec.
  destruct (Z.leb_spec x HALF); lia.
Qed.

Theorem sdec_cong : forall x, (sdec x) mod p = x mod p.
Proof.
  intro x. pose proof p_ge2. unfold sdec.
  destruct (x <=? HALF); [ reflexivity | ].
  replace (x - p) with (x + (-1) * p) by ring. apply Z.mod_add. lia.
Qed.

Theorem sdec_agree : forall z, - HALF <= z <= HALF -> sdec (z mod p) = z.
Proof.
  intros z Hz. pose proof p_odd as Hp. pose proof p_ge2.
  destruct (Z.leb_spec 0 z) as [Hz0|Hz0].
  - rewrite Z.mod_small by lia. unfold sdec.
    destruct (Z.leb_spec z HALF); lia.
  - assert (Hm : z mod p = z + p).
    { rewrite <- (Z.mod_add z 1 p) by lia. rewrite Z.mod_small by lia. ring. }
    rewrite Hm. unfold sdec. destruct (Z.leb_spec (z + p) HALF); lia.
Qed.

Theorem sdec_injective : forall x y, 0 <= x < p -> 0 <= y < p ->
  sdec x = sdec y -> x = y.
Proof.
  intros x y Hx Hy. pose proof p_odd. unfold sdec.
  destruct (Z.leb_spec x HALF), (Z.leb_spec y HALF); lia.
Qed.

Corollary sdec_injective_on_the_envelope : forall x y,
  0 <= x < p -> 0 <= y < p ->
  - 2 ^ 67 < sdec x < 2 ^ 131 -> - 2 ^ 67 < sdec y < 2 ^ 131 ->
  sdec x = sdec y -> x = y.
Proof. intros x y Hx Hy _ _. apply sdec_injective; assumption. Qed.

Theorem sdec_exact_on_the_envelope : forall z,
  - 2 ^ 67 < z < 2 ^ 131 -> sdec (z mod p) = z.
Proof.
  intros z Hz. apply sdec_agree.
  pose proof envelope_fits_signed_range. pose proof HALF_big.
  assert (2 ^ 67 <= 2 ^ 131) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Definition dc (a : Assignment) (c : nat) : Z := (a (c, 0%nat)) mod p.

Definition IN_BASE     : nat := 0.
Definition OUT_BASE    : nat := 7.
Definition C_BASE      : nat := 15.
Definition OUTBIT_BASE : nat := 22.
Definition CBIT_BASE   : nat := 534.
Definition N_ADVICE    : nat := 1003.
Definition TAG_BASE    : nat := 3000.

Definition in_cells (a : Assignment) : list Z :=
  [dc a 0; dc a 1; dc a 2; dc a 3; dc a 4; dc a 5; dc a 6].

Definition inp_l (a : Assignment) : list Z := map sdec (in_cells a).
Definition out_l (a : Assignment) : list Z :=
  [dc a 7; dc a 8; dc a 9; dc a 10; dc a 11; dc a 12; dc a 13; dc a 14].

Definition cc (a : Assignment) (i : nat) : Z := dc a (15 + i).

Lemma inp_l_length : forall a, length (inp_l a) = lts_rule.K.
Proof. reflexivity. Qed.
Lemma out_l_length : forall a, length (out_l a) = S lts_rule.K.
Proof. reflexivity. Qed.

Lemma inp_l_nth : forall a i, (i < 7)%nat -> nth i (inp_l a) 0 = sdec (dc a i).
Proof. intros a i Hi. do 7 (destruct i as [|i]; [ reflexivity | ]). lia. Qed.
Lemma out_l_nth : forall a i, (i < 8)%nat -> nth i (out_l a) 0 = dc a (7 + i).
Proof. intros a i Hi. do 8 (destruct i as [|i]; [ reflexivity | ]). lia. Qed.

Lemma dc_range : forall a c, 0 <= dc a c < p.
Proof. intros a c. unfold dc. apply Z.mod_pos_bound. pose proof p_ge2. lia. Qed.

Definition bool_gate (c : nat) : Expr :=
  EMul (ECell (c, 0%nat)) (ESub (ECell (c, 0%nat)) (EConst 1)).

Lemma in_firstn_in : forall (A : Type) n (l : list A) x,
  In x (firstn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [ destruct H | ].
  destruct l as [|y l]; [ destruct H | ].
  cbn [firstn] in H. destruct H as [->|H]; [ left; reflexivity | ].
  right. exact (IH l x H).
Qed.

Lemma in_skipn_in : forall (A : Type) n (l : list A) x,
  In x (skipn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [ exact H | ].
  destruct l as [|y l]; [ destruct H | ].
  cbn [skipn] in H. right. exact (IH l x H).
Qed.

Theorem head_is_the_booleanity_bank :
  firstn 981 deployed_gates = map (fun j => bool_gate (22 + j)) (seq 0 981).
Proof. vm_compute. reflexivity. Qed.

Lemma bool_gate_in_model : forall j, (j < 981)%nat ->
  In (bool_gate (22 + j)) deployed_gates.
Proof.
  intros j Hj. apply (in_firstn_in _ 981).
  rewrite head_is_the_booleanity_bank.
  apply (in_map (fun k => bool_gate (22 + k)%nat)). apply in_seq. lia.
Qed.

Definition tail_gates : list Expr := Eval vm_compute in (skipn 981 deployed_gates).

Lemma tail_gates_length : length tail_gates = 23%nat.
Proof. reflexivity. Qed.

(* The model has 1,004 polynomial constraints (the 8 copy constraints are separate). *)
Lemma dg_len : length deployed_gates = 1004%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma head_and_tail_exhaust_the_model :
  (981 + length tail_gates)%nat = length deployed_gates.
Proof. rewrite tail_gates_length, dg_len. reflexivity. Qed.

Definition tg_rec_out : list Expr := Eval vm_compute in (firstn 8 tail_gates).
Definition tg_rec_c   : list Expr := Eval vm_compute in (firstn 7 (skipn 8 tail_gates)).
Definition tg_chain   : list Expr := Eval vm_compute in (firstn 7 (skipn 15 tail_gates)).
Definition tg_end     : list Expr := Eval vm_compute in (skipn 22 tail_gates).

Lemma tg_rec_out_eq : tg_rec_out = firstn 8 tail_gates. Proof. vm_compute. reflexivity. Qed.
Lemma tg_rec_c_eq : tg_rec_c = firstn 7 (skipn 8 tail_gates). Proof. vm_compute. reflexivity. Qed.
Lemma tg_chain_eq : tg_chain = firstn 7 (skipn 15 tail_gates). Proof. vm_compute. reflexivity. Qed.
Lemma tg_end_eq : tg_end = skipn 22 tail_gates. Proof. vm_compute. reflexivity. Qed.

Theorem tail_split_is_a_partition :
  tg_rec_out ++ tg_rec_c ++ tg_chain ++ tg_end = tail_gates.
Proof. vm_compute. reflexivity. Qed.

Lemma tg_rec_out_len : length tg_rec_out = 8%nat. Proof. reflexivity. Qed.
Lemma tg_rec_c_len   : length tg_rec_c   = 7%nat. Proof. reflexivity. Qed.
Lemma tg_chain_len   : length tg_chain   = 7%nat. Proof. reflexivity. Qed.
Lemma tg_end_len     : length tg_end     = 1%nat. Proof. reflexivity. Qed.

Lemma in_tail_in_model : forall x, In x tail_gates -> In x deployed_gates.
Proof.
  intros x H. apply (in_skipn_in _ 981).
  change (skipn 981 deployed_gates) with tail_gates. exact H.
Qed.

Lemma tg_rec_out_in : forall k, (k < 8)%nat -> In (nth k tg_rec_out (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_firstn_in _ 8).
  rewrite <- tg_rec_out_eq. apply nth_In. rewrite tg_rec_out_len. exact Hk.
Qed.
Lemma tg_rec_c_in : forall k, (k < 7)%nat -> In (nth k tg_rec_c (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 8). apply (in_firstn_in _ 7).
  rewrite <- tg_rec_c_eq. apply nth_In. rewrite tg_rec_c_len. exact Hk.
Qed.
Lemma tg_chain_in : forall k, (k < 7)%nat -> In (nth k tg_chain (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 15). apply (in_firstn_in _ 7).
  rewrite <- tg_chain_eq. apply nth_In. rewrite tg_chain_len. exact Hk.
Qed.
Lemma tg_end_in : In (nth 0 tg_end (EConst 0)) deployed_gates.
Proof.
  apply in_tail_in_model. apply (in_skipn_in _ 22).
  rewrite <- tg_end_eq. apply nth_In. rewrite tg_end_len. lia.
Qed.

Definition CANON_lts (a : Assignment) : Prop :=
  (forall i, (i < 7)%nat -> 0 <= dc a (0 + i) < p)
  /\ (forall i, (i < 8)%nat -> 0 <= dc a (7 + i) < p).

Theorem CANON_is_free : forall a, CANON_lts a.
Proof. intro a. split; intros i _; apply dc_range. Qed.

Definition PINS_lts (a : Assignment) : Prop :=
  forall j, (j < 8)%nat -> dc a (7 + j) = (a (3000%nat, j)) mod p.

Theorem answer_pins_are_DERIVED : forall a, sat deployed_model a -> PINS_lts a.
Proof.
  intros a [_ Hc] j Hj. unfold dc.
  do 8 (destruct j as [|j];
    [ first [ exact (copy_get a _ _ Hc in_copy_1) | exact (copy_get a _ _ Hc in_copy_2)
            | exact (copy_get a _ _ Hc in_copy_3) | exact (copy_get a _ _ Hc in_copy_4)
            | exact (copy_get a _ _ Hc in_copy_5) | exact (copy_get a _ _ Hc in_copy_6)
            | exact (copy_get a _ _ Hc in_copy_7) | exact (copy_get a _ _ Hc in_copy_8) ] | ]).
  lia.
Qed.

Theorem every_bit_cell_is_boolean : forall a,
  sat deployed_model a ->
  forall j, (j < 981)%nat ->
    (a ((22 + j)%nat, 0%nat)) mod p = 0 \/ (a ((22 + j)%nat, 0%nat)) mod p = 1.
Proof.
  intros a [Hg _] j Hj.
  pose proof (Hg _ (bool_gate_in_model j Hj)) as H.
  unfold gate_holds in H. cbn [eval] in H.
  apply (range_field.bool_mod_forces_01 p p_prime).
  replace (a ((22 + j)%nat, 0%nat) * a ((22 + j)%nat, 0%nat) - a ((22 + j)%nat, 0%nat))
     with (a ((22 + j)%nat, 0%nat) * (a ((22 + j)%nat, 0%nat) - 1)) by ring.
  exact H.
Qed.

Definition bits_at (a : Assignment) (b : nat) : nat -> Z :=
  fun j => a ((b + j)%nat, 0%nat).

Lemma bank_bits_boolean : forall a,
  sat deployed_model a ->
  forall b n, (22 <= b)%nat -> (b + n <= 1003)%nat ->
  forall j, (j < n)%nat ->
    (bits_at a b j) mod p = 0 \/ (bits_at a b j) mod p = 1.
Proof.
  intros a Hs b n Hb Hbn j Hj. unfold bits_at.
  replace (b + j)%nat with (22 + (b - 22 + j))%nat by lia.
  apply (every_bit_cell_is_boolean a Hs). lia.
Qed.

Lemma wpow64_le_p : wpow 64 <= p.
Proof. rewrite p_eq_pasta. exact wpow64_le_pasta. Qed.
Lemma wpow67_le_p : wpow 67 <= p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma wpow64_val : wpow 64 = 18446744073709551616.
Proof. vm_compute. reflexivity. Qed.
Lemma wpow67_val : wpow 67 = 147573952589676412928.
Proof. vm_compute. reflexivity. Qed.

Lemma range_from_gate : forall a b n v,
  sat deployed_model a ->
  (22 <= b)%nat -> (b + n <= 1003)%nat ->
  wpow n <= p ->
  (bitsum (bits_at a b) n - v) mod p = 0 ->
  0 <= v mod p < wpow n.
Proof.
  intros a b n v Hs Hb Hbn Hw Hres.
  destruct (order_lift p p_ge2 (bits_at a b) n v Hw
              (bank_bits_boolean a Hs b n Hb Hbn) Hres) as [_ Hr].
  exact Hr.
Qed.
Lemma ev_rec_out_0 : forall a, eval a (nth 0 tg_rec_out (EConst 0))
  = bitsum (bits_at a 22) 64 - a (7%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_1 : forall a, eval a (nth 1 tg_rec_out (EConst 0))
  = bitsum (bits_at a 86) 64 - a (8%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_2 : forall a, eval a (nth 2 tg_rec_out (EConst 0))
  = bitsum (bits_at a 150) 64 - a (9%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_3 : forall a, eval a (nth 3 tg_rec_out (EConst 0))
  = bitsum (bits_at a 214) 64 - a (10%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_4 : forall a, eval a (nth 4 tg_rec_out (EConst 0))
  = bitsum (bits_at a 278) 64 - a (11%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_5 : forall a, eval a (nth 5 tg_rec_out (EConst 0))
  = bitsum (bits_at a 342) 64 - a (12%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_6 : forall a, eval a (nth 6 tg_rec_out (EConst 0))
  = bitsum (bits_at a 406) 64 - a (13%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_7 : forall a, eval a (nth 7 tg_rec_out (EConst 0))
  = bitsum (bits_at a 470) 64 - a (14%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_0 : forall a, eval a (nth 0 tg_rec_c (EConst 0))
  = bitsum (bits_at a 534) 67 - a (15%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_1 : forall a, eval a (nth 1 tg_rec_c (EConst 0))
  = bitsum (bits_at a 601) 67 - a (16%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_2 : forall a, eval a (nth 2 tg_rec_c (EConst 0))
  = bitsum (bits_at a 668) 67 - a (17%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_3 : forall a, eval a (nth 3 tg_rec_c (EConst 0))
  = bitsum (bits_at a 735) 67 - a (18%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_4 : forall a, eval a (nth 4 tg_rec_c (EConst 0))
  = bitsum (bits_at a 802) 67 - a (19%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_5 : forall a, eval a (nth 5 tg_rec_c (EConst 0))
  = bitsum (bits_at a 869) 67 - a (20%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_6 : forall a, eval a (nth 6 tg_rec_c (EConst 0))
  = bitsum (bits_at a 936) 67 - a (21%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.

Theorem rng_out : forall a, sat deployed_model a ->
  forall i, (i < 8)%nat -> 0 <= dc a (7 + i) < 18446744073709551616.
Proof.
  intros a Hs i Hi. unfold dc. rewrite <- wpow64_val.
  destruct Hs as [Hg Hc].
  destruct i as [|i].
  { apply (range_from_gate a 22 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_0. exact (Hg _ (tg_rec_out_in 0 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 86 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_1. exact (Hg _ (tg_rec_out_in 1 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 150 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_2. exact (Hg _ (tg_rec_out_in 2 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 214 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_3. exact (Hg _ (tg_rec_out_in 3 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 278 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_4. exact (Hg _ (tg_rec_out_in 4 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 342 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_5. exact (Hg _ (tg_rec_out_in 5 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 406 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_6. exact (Hg _ (tg_rec_out_in 6 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 470 64 _ (conj Hg Hc)); [ lia | lia | exact wpow64_le_p | ].
    rewrite <- ev_rec_out_7. exact (Hg _ (tg_rec_out_in 7 ltac:(lia))). }
  lia.
Qed.

Theorem rng_c : forall a, sat deployed_model a ->
  forall i, (i < 7)%nat -> 0 <= cc a i < 147573952589676412928.
Proof.
  intros a Hs i Hi. unfold cc, dc. rewrite <- wpow67_val.
  destruct Hs as [Hg Hc].
  destruct i as [|i].
  { apply (range_from_gate a 534 67 _ (conj Hg Hc)); [ lia | lia | exact wpow67_le_p | ].
    rewrite <- ev_rec_c_0. exact (Hg _ (tg_rec_c_in 0 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 601 67 _ (conj Hg Hc)); [ lia | lia | exact wpow67_le_p | ].
    rewrite <- ev_rec_c_1. exact (Hg _ (tg_rec_c_in 1 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 668 67 _ (conj Hg Hc)); [ lia | lia | exact wpow67_le_p | ].
    rewrite <- ev_rec_c_2. exact (Hg _ (tg_rec_c_in 2 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 735 67 _ (conj Hg Hc)); [ lia | lia | exact wpow67_le_p | ].
    rewrite <- ev_rec_c_3. exact (Hg _ (tg_rec_c_in 3 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 802 67 _ (conj Hg Hc)); [ lia | lia | exact wpow67_le_p | ].
    rewrite <- ev_rec_c_4. exact (Hg _ (tg_rec_c_in 4 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 869 67 _ (conj Hg Hc)); [ lia | lia | exact wpow67_le_p | ].
    rewrite <- ev_rec_c_5. exact (Hg _ (tg_rec_c_in 5 ltac:(lia))). }
  destruct i as [|i].
  { apply (range_from_gate a 936 67 _ (conj Hg Hc)); [ lia | lia | exact wpow67_le_p | ].
    rewrite <- ev_rec_c_6. exact (Hg _ (tg_rec_c_in 6 ltac:(lia))). }
  lia.
Qed.

Print Assumptions p_prime.
Print Assumptions p_odd.
Print Assumptions pasta_margin.
Print Assumptions envelope_fits_signed_range.
Print Assumptions HALF_big.
Print Assumptions sdec_range.
Print Assumptions sdec_cong.
Print Assumptions sdec_agree.
Print Assumptions sdec_injective.
Print Assumptions sdec_injective_on_the_envelope.
Print Assumptions sdec_exact_on_the_envelope.
Print Assumptions head_is_the_booleanity_bank.
Print Assumptions head_and_tail_exhaust_the_model.
Print Assumptions tail_split_is_a_partition.
Print Assumptions CANON_is_free.
Print Assumptions answer_pins_are_DERIVED.
Print Assumptions every_bit_cell_is_boolean.
Print Assumptions rng_out.
Print Assumptions rng_c.
