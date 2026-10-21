(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Each copy constraint is necessary: the model with any one of the eight copy constraints removed no
   longer refines the intended public interface (mutant_wcopy_1_not_refines and its seven siblings), shown
   by an explicit filling. lts_all_wires_closed_gen collects these facts with the full model's refinement.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith List Lia. Import ListNotations. Open Scope Z_scope.
Require Import Generated.lts_model_gen.
Require Import Generated.lts_wires_gen.
Require Import Generated.lts_scaffold_gen.

Fixpoint expr_eqb (x y:Expr) : bool :=
  match x, y with
  | EConst a, EConst b       => Z.eqb a b
  | ECell a, ECell b         => cell_eqb a b
  | EAdd a1 a2, EAdd b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | ESub a1 a2, ESub b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | EMul a1 a2, EMul b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | ENeg a, ENeg b           => expr_eqb a b
  | EScaled a z1, EScaled b z2 => andb (expr_eqb a b) (Z.eqb z1 z2)
  | _, _                     => false
  end.

Definition cut_edge_lts (e:Cell*Cell) : list (Cell*Cell) :=
  filter (fun f => negb (cellpair_eqb f e)) deployed_copy.
Definition cut_copy_model_lts (e:Cell*Cell) : CircuitModel :=
  mk_model p deployed_gates (cut_edge_lts e).

Definition no_gate_reads_lts (t:Cell) : Prop := forall g, In g deployed_gates -> reads_b t g = false.
Ltac noreads_tac :=
  let g := fresh "g" in let Hin := fresh "Hin" in
  intros g Hin; cbn in Hin;
  repeat (destruct Hin as [<-|Hin]; [vm_compute; reflexivity| ]);
  contradiction.

Definition wit_honest_lts : Assignment := fun c =>
  if cell_eqb c (0%nat, 0%nat) then 1361129467683753853853498429727072845824 else
  if cell_eqb c (9%nat, 0%nat) then 4 else
  if cell_eqb c (15%nat, 0%nat) then 73786976294838206464 else
  if cell_eqb c (16%nat, 0%nat) then 4 else
  if cell_eqb c (152%nat, 0%nat) then 1 else
  if cell_eqb c (600%nat, 0%nat) then 1 else
  if cell_eqb c (603%nat, 0%nat) then 1 else
  if cell_eqb c (3000%nat, 2%nat) then 4 else
  0.

Lemma honest_full_sat_lts : sat deployed_model wit_honest_lts.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.

Definition mutant_wcopy_1_model : CircuitModel := cut_copy_model_lts ((7%nat, 0%nat), (3000%nat, 0%nat)).
Definition wit_wcopy_1 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 0%nat) then 1 else
  wit_honest_lts c.
Lemma wcopy_1_split_sat : sat mutant_wcopy_1_model wit_wcopy_1.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_1_not_refines : ~ refinesD_lts_gen mutant_wcopy_1_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_1 wcopy_1_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj1 H) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_2_model : CircuitModel := cut_copy_model_lts ((8%nat, 0%nat), (3000%nat, 1%nat)).
Definition wit_wcopy_2 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 1%nat) then 1 else
  wit_honest_lts c.
Lemma wcopy_2_split_sat : sat mutant_wcopy_2_model wit_wcopy_2.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_2_not_refines : ~ refinesD_lts_gen mutant_wcopy_2_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_2 wcopy_2_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj1 (proj2 H)) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_3_model : CircuitModel := cut_copy_model_lts ((9%nat, 0%nat), (3000%nat, 2%nat)).
Definition wit_wcopy_3 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 2%nat) then 5 else
  wit_honest_lts c.
Lemma wcopy_3_split_sat : sat mutant_wcopy_3_model wit_wcopy_3.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_3_not_refines : ~ refinesD_lts_gen mutant_wcopy_3_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_3 wcopy_3_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj1 (proj2 (proj2 H))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_4_model : CircuitModel := cut_copy_model_lts ((10%nat, 0%nat), (3000%nat, 3%nat)).
Definition wit_wcopy_4 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 3%nat) then 1 else
  wit_honest_lts c.
Lemma wcopy_4_split_sat : sat mutant_wcopy_4_model wit_wcopy_4.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_4_not_refines : ~ refinesD_lts_gen mutant_wcopy_4_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_4 wcopy_4_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 H)))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_5_model : CircuitModel := cut_copy_model_lts ((11%nat, 0%nat), (3000%nat, 4%nat)).
Definition wit_wcopy_5 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 4%nat) then 1 else
  wit_honest_lts c.
Lemma wcopy_5_split_sat : sat mutant_wcopy_5_model wit_wcopy_5.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_5_not_refines : ~ refinesD_lts_gen mutant_wcopy_5_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_5 wcopy_5_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 H))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_6_model : CircuitModel := cut_copy_model_lts ((12%nat, 0%nat), (3000%nat, 5%nat)).
Definition wit_wcopy_6 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 5%nat) then 1 else
  wit_honest_lts c.
Lemma wcopy_6_split_sat : sat mutant_wcopy_6_model wit_wcopy_6.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_6_not_refines : ~ refinesD_lts_gen mutant_wcopy_6_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_6 wcopy_6_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_7_model : CircuitModel := cut_copy_model_lts ((13%nat, 0%nat), (3000%nat, 6%nat)).
Definition wit_wcopy_7 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 6%nat) then 1 else
  wit_honest_lts c.
Lemma wcopy_7_split_sat : sat mutant_wcopy_7_model wit_wcopy_7.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_7_not_refines : ~ refinesD_lts_gen mutant_wcopy_7_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_7 wcopy_7_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_8_model : CircuitModel := cut_copy_model_lts ((14%nat, 0%nat), (3000%nat, 7%nat)).
Definition wit_wcopy_8 : Assignment := fun c =>
  if cell_eqb c (3000%nat, 7%nat) then 1 else
  wit_honest_lts c.
Lemma wcopy_8_split_sat : sat mutant_wcopy_8_model wit_wcopy_8.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_8_not_refines : ~ refinesD_lts_gen mutant_wcopy_8_model intact_ports_lts_gen.
Proof.
  unfold refinesD_lts_gen. intro H. specialize (H wit_wcopy_8 wcopy_8_split_sat).
  unfold RD_lts_gen in H. cbn [ intact_ports_lts_gen] in H.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Theorem lts_all_wires_closed_gen :
  (In ((7%nat, 0%nat), (3000%nat, 0%nat)) deployed_copy /\
   In ((8%nat, 0%nat), (3000%nat, 1%nat)) deployed_copy /\
   In ((9%nat, 0%nat), (3000%nat, 2%nat)) deployed_copy /\
   In ((10%nat, 0%nat), (3000%nat, 3%nat)) deployed_copy /\
   In ((11%nat, 0%nat), (3000%nat, 4%nat)) deployed_copy /\
   In ((12%nat, 0%nat), (3000%nat, 5%nat)) deployed_copy /\
   In ((13%nat, 0%nat), (3000%nat, 6%nat)) deployed_copy /\
   In ((14%nat, 0%nat), (3000%nat, 7%nat)) deployed_copy) /\
  (refinesD_lts_gen deployed_model intact_ports_lts_gen /\
   sat deployed_model wit_honest_lts) /\
  (~ refinesD_lts_gen mutant_wcopy_1_model intact_ports_lts_gen /\
   ~ refinesD_lts_gen mutant_wcopy_2_model intact_ports_lts_gen /\
   ~ refinesD_lts_gen mutant_wcopy_3_model intact_ports_lts_gen /\
   ~ refinesD_lts_gen mutant_wcopy_4_model intact_ports_lts_gen /\
   ~ refinesD_lts_gen mutant_wcopy_5_model intact_ports_lts_gen /\
   ~ refinesD_lts_gen mutant_wcopy_6_model intact_ports_lts_gen /\
   ~ refinesD_lts_gen mutant_wcopy_7_model intact_ports_lts_gen /\
   ~ refinesD_lts_gen mutant_wcopy_8_model intact_ports_lts_gen).
Proof.
  split; [| split].
  - repeat split;
      first [ exact in_copy_1
            | exact in_copy_2
            | exact in_copy_3
            | exact in_copy_4
            | exact in_copy_5
            | exact in_copy_6
            | exact in_copy_7
            | exact in_copy_8 ].
  - split; [ exact deployed_refines_RD_lts_gen | exact honest_full_sat_lts ].
  - exact (conj mutant_wcopy_1_not_refines
      (conj mutant_wcopy_2_not_refines
      (conj mutant_wcopy_3_not_refines
      (conj mutant_wcopy_4_not_refines
      (conj mutant_wcopy_5_not_refines
      (conj mutant_wcopy_6_not_refines
      (conj mutant_wcopy_7_not_refines
      (mutant_wcopy_8_not_refines)))))))).
Qed.
