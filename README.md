<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd -->

# Our LongToShortNoEndCarry circuit, verified: sound and complete

A formally verified LongToShortNoEndCarry circuit of our own, soundness and completeness, kernel-checked, with
seven input values and output limbs of 64 bits (*n* = 64, *k* = 7).

LongToShortNoEndCarry is the carry step of big-integer arithmetic in the circom-bigint library. After a
multiplication, each position holds a sum that can exceed 64 bits; the template is meant to turn *k* such "long"
values into *k* + 1 proper 64-bit limbs with the same value, carrying the overflow from limb to limb. The member
*k* = 7 is the one the library's `BigMult(64, 4)` uses. The public audit of that library, *Auditing Report for
circom-bigint (circomlib)* (0xPARC Community, Ethereum Foundation and Veridise Inc., 2022), lists
LongToShortNoEndCarry as "In Progress" in its table of Coda verification results and gives no specification of
it. Coda, the open-source Coq library the audit used, contains no statement or proof of it (repository
`Veridise/Coda`, commit `96e5c94e`, its main branch on 2026-09-25).

This repository holds **our own circuit** for that job and **our own written rule** for it, and a proof, checked
by the Coq kernel, that the two agree exactly:

- **sound**: every filling of the circuit's cells that the circuit accepts yields an input-output pair the rule
  accepts, with no assumption on the inputs beyond their number;
- **complete**: every pair of seven inputs and an output that the rule accepts is realised by some filling the
  circuit accepts.

The two directions are one theorem, `policy_adequacy_lts`. The audit set out to verify a fixed circuit it did not
design; we designed ours to fit the rule. This proof is of our circuit against our rule: our own implementation of
the template's function, never a proof about the template itself. The rule is written by us, since neither the
report nor Coda states one, from the template's constraints and the library's own conventions. No code from
circom-bigint is in this repository.

## Check it yourself

```
git clone https://github.com/probatur/longtoshortnoendcarry
cd longtoshortnoendcarry
docker build .
```

The build compiles every proof from source in the public Coq 8.20.1 image, pinned by digest in the Dockerfile,
then re-checks the whole development, together with the parts of Coq's standard library it uses, with coqchk,
Coq's independent kernel checker. It fails unless coqchk accepts everything and reports no axioms, and its last
step prints the theorem exactly as the kernel states it, with the two definitions it is stated with (reproduced
below). With BuildKit, add `--progress=plain` to see every line. The same build runs on every push, from
`.github/workflows/check.yml`. If you run it, you are welcome to add a line to [REPRODUCTIONS.md](REPRODUCTIONS.md).

## The theorem, as the kernel states it

<!-- STATEMENT:BEGIN (filled from the check's own output; never edited by hand) -->

```
policy_adequacy_lts
     : lts_rule.adequate accepts_lts
lts_rule.adequate =
fun accepts : list BinNums.Z -> list BinNums.Z -> Prop =>
forall inp out : list BinNums.Z,
lts_rule.PRE_lts inp -> accepts inp out <-> lts_rule.REL_lts inp out
     : (list BinNums.Z -> list BinNums.Z -> Prop) -> Prop

Arguments lts_rule.adequate accepts%function_scope
accepts_lts =
fun inp out : list BinNums.Z =>
(forall i : nat,
 i < lts_rule.K ->
 BinInt.Z.le
   (BinInt.Z.opp
      (BinInt.Z.div (BinInt.Z.sub lts_model_gen.p (BinNums.Zpos BinNums.xH))
         (BinNums.Zpos (BinNums.xO BinNums.xH))))
   (List.nth i inp BinNums.Z0) /\
 BinInt.Z.le (List.nth i inp BinNums.Z0)
   (BinInt.Z.div (BinInt.Z.sub lts_model_gen.p (BinNums.Zpos BinNums.xH))
      (BinNums.Zpos (BinNums.xO BinNums.xH)))) /\
(exists al : lts_scaffold_gen.Assignment,
   lts_scaffold_gen.sat lts_model_gen.deployed_model al /\
   lts_semantic.CANON_lts al /\
   List.map lts_semantic.sdec (lts_semantic.in_cells al) = inp /\
   lts_semantic.out_l al = out)
     : list BinNums.Z -> list BinNums.Z -> Prop

Arguments accepts_lts (inp out)%list_scope
```

<!-- STATEMENT:END -->

## The theorem in plain language

### The two objects it connects

**The circuit.** A fixed arithmetic circuit over the prime field of the 255-bit Pasta prime
2^254 + 45560315531419706090280762371685220353. It is a table of cells, each holding a field element, together
with 1,004 polynomial constraints, each of which must evaluate to zero in the field, and 8 copy constraints, each
requiring an output cell and a public cell to hold the same value. A filling of the cells that passes all 1,004
polynomial constraints and all 8 copy constraints is an **accepted assignment** (`sat deployed_model` in the
development). That is the whole acceptance condition: the model contains no lookup tables and no other kind of
constraint.

**The rule** (`coq/spec/lts_rule.v`), written by us, about pairs (*in*, *out*). The inputs are integers and may be
negative; an output limb is a whole number from 0 up to, but not including, 2^64; a vector's value `VAL` is its
little-endian base-2^64 reading. The rule has two parts:

- **the input assumption** `PRE_lts`: *in* has exactly 7 values. That is its shape only; no range is assumed.
- **the relation** `REL_lts`, about the whole pair: *out* has exactly 8 limbs, all in range; `VAL out = VAL in`,
  as an equality of integers; every running carry lies in [0, 2^67); and the **envelope** `ENVELOPE`: the first
  input lies in [0, 2^131) and every later one in (−2^67, 2^131). The envelope is the input range the circuit
  enforces, stated in the relation so that it is claimed, not assumed.

**What "accepts" means** (`accepts_lts`): the circuit accepts a pair when every input value lies between
−(*p* − 1)/2 and (*p* − 1)/2 for the field prime *p*, and there is an accepted assignment whose input cells, read
as signed integers by the half-field rule (a residue above (*p* − 1)/2 reads as that residue minus *p*), are
exactly *in*, and whose output cells, read as their canonical integers in [0, *p*), are exactly *out*. It is false
for any *in* that is not a list of such signed values; acceptance does not reduce inputs modulo *p*
(`accepts_is_not_mod_q_invariant`). The theorem, `adequate accepts_lts`, says: for every *in* of seven values and
every *out*, the circuit accepts (*in*, *out*) **exactly when** the relation holds.

### Soundness: nothing the circuit accepts escapes the rule

For every accepted assignment, read the fifteen operand cells: the seven input cells as signed integers by the
half-field rule, the eight output cells as their canonical remainders modulo the field prime. The pair so read
satisfies the relation, envelope and carry bounds included (`bridge_sound_needs_only_sat`).

- No input range is assumed: the only input assumption is the number of inputs, which every filling meets. The
  envelope is therefore enforced by the circuit, and the rule states it as a claim.
- The output's range is not assumed: every accepted filling has its eight output limbs in [0, 2^64)
  (`out_limbs_in_range`), and its seven carry cells in [0, 2^67) (`carry_cells_in_range`).
- The public cells are not assumed to agree with the output cells: that agreement is derived from the copy
  constraints (`answer_pins_are_DERIVED`).

### Completeness: nothing the rule accepts is beyond the circuit

For every input of seven values and every output that together satisfy the relation, there is a filling that the
circuit accepts, passing all 1,004 polynomial constraints and all 8 copy constraints, whose operand cells read back
as **exactly that pair**, limb for limb (`bridge_complete`). This covers negative inputs within the envelope: the
development shows a pair with an input of −(2^67 − 1) accepted (`the_wrap_band_row_is_ACCEPTED`), its cell holding
*p* − 2^67 + 1 (`the_wrap_cell_holds_q_minus_2_67_plus_1`). This direction is ours: the audit's certification
criterion is one-directional.

### Two things that are easy to confuse

- **The signed reading and the library's documentation.** The library's own helper `isNegative` reads a field
  element above half the field (the BN254 scalar field, which its threshold is set for) as negative, and the
  template's constraints accept a band of such values: small negative numbers. The rule describes those inputs
  rather than quietly excluding them. The documentation beside this template, the comment on `BigMultNoCarry`,
  whose output `BigMult` passes to it, describes that template's inputs as NONNEGATIVE. A different library comment, about
  "potentially negative" registers, documents a helper this template does not call, and is not the ground here.
- **The field the rule is read in.** The rule is about integers. Reading field values as those integers is exact,
  on every value the envelope allows, for any modulus of at least 2^132 − 1
  (`signed_reading_is_exact_above_the_threshold`), and fails at a modulus below it
  (`signed_reading_fails_below_the_threshold`). The Pasta prime clears it (`pasta_clears_the_threshold`), as the
  development proves. Any statement of this rule over another field needs that hypothesis.

## Where each part of the rule comes from

| part of the rule | what it says | where it comes from |
|---|---|---|
| `PRE_lts` | *in* has exactly 7 values | the template's *k* inputs, *k* = 7; shape only, no range assumed |
| `REL_lts`, first two conjuncts | *out* has exactly 8 limbs, each in [0, 2^64) | the template's *k* + 1 outputs, each range-checked with `Num2Bits(n)` |
| `REL_lts`, third conjunct | `VAL out = VAL in` | the template's purpose: the same value, carried from limb to limb by its running-carry constraints |
| `REL_lts`, fourth conjunct | every running carry in [0, 2^67) | the template's running-carry range checks, `Num2Bits(n + log_ceil(k))`: 67 bits at *n* = 64, *k* = 7 |
| `ENVELOPE` | first input in [0, 2^131), later inputs in (−2^67, 2^131) | the band the template's constraints enforce, claimed rather than assumed |
| the signed reading of inputs | a residue above (*p* − 1)/2 reads as negative | the library's `isNegative`, and the band the constraints accept |
| `adequate` | the two directions together | ours |

The template is `LongToShortNoEndCarry(n, k)` in circom-bigint, `circuits/bigint.circom`, lines 221–275 at commit
`7505e5c60b8bc76cfb5cc06646d81aafbae66180` (the commit the audit's engineers worked on), and byte-identical at
lines 246–300 of commit `2eceb9c` (the version in the report's application summary): the output range checks at
lines 256–260 and the running-carry constraints and their range checks at lines 262–274 of `7505e5c`. `isNegative`
is at lines 3–6 of `circuits/bigint_func.circom`, and the comment on `BigMultNoCarry` at lines 175–178 of
`circuits/bigint.circom`, both at `7505e5c`.

## Reading notes

1. **Counting the constraints.** The circuit has 1,004 polynomial constraints and 8 copy constraints; the theorem
   covers exactly the set of fillings that passes both kinds together. The count of 1,004 polynomial constraints,
   beside the 8 copy constraints, is itself a checked fact of the development (`dg_len`).
2. **Completeness is universal.** It holds for every pair that satisfies the relation. The development also shows
   instances, such as the pair with a negative input above; those are instances shown, not the evidence.
3. **A premise that does no work, and the development proves it.** The soundness statement carries a canonicity
   condition, `CANON_lts`; it is provably satisfied by every filling (`CANON_is_free`), so it narrows nothing.
4. **Two conditions of the rule follow from the others, and the development proves it.** The envelope follows
   from the relation's other conjuncts and the input's shape (`ENVELOPE_is_redundant`); it is stated so that it is claimed. The last
   running carry equals the top output limb (`the_last_carry_is_out_k`), so its 67-bit bound is implied by the
   output's 64-bit range. The circuit keeps a range check on every carry cell, as the template does.
5. **Every copy constraint is needed.** With any one of the 8 copy constraints removed, the model no longer
   meets its intended public interface, shown by an explicit filling for each (`lts_all_wires_closed_gen`).
6. **Scope.** Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them.

## What is not claimed

- **Nothing about circom-bigint's own circuit, or about Coda's development**, beyond the facts cited above: the
  template's text and the library's `isNegative`, and that neither the report nor Coda states a rule for this
  template. The circuit proved here is ours, built for the same function; the rule is ours. We designed our circuit
  to meet our rule.
- **Nothing beyond the parameter set *n* = 64, *k* = 7.** The theorem is about our circuit, over the Pasta field;
  nothing is claimed about any other (*n*, *k*), or about any circuit over another field. The rule is not claimed
  to describe the template over any field other than the BN254 scalar field it is written for.
- **Nothing about the layers below the formal model.** That the generated constraint model (the 1,004 polynomial
  constraints, the 8 copy constraints, the field prime, the cell layout, and the absence of lookups and of other
  constraint kinds) faithfully mirrors the circuit implementation is outside this claim, as are the
  implementation, the prover and the verifier themselves.
- **Nothing about inputs that are not signed values for the field prime**: acceptance is false for them.

## A proof about a circuit, not a proof made by one

Two different objects are called "proofs" around circuits like this one. This repository contains the first: a
single machine-checked argument, in Coq, about what the circuit's constraints accept. It is checked once, and it
does not depend on any execution. The circuit itself, when used, produces a different kind of proof, a
zero-knowledge proof for each execution. None of those is in this repository, and nothing here depends on them.

## Files

| file | what it holds |
|---|---|
| `coq/spec/lts_rule.v` | the rule: `PRE_lts`, `ENVELOPE`, `REL_lts`, `adequate`, and facts about it |
| `coq/constraints/gen/lts_model_gen.v` | the circuit's constraint model: the field prime, the 1,004 polynomial constraints, the 8 copy constraints |
| `coq/constraints/gen/lts_scaffold_gen.v` | cells, assignments, evaluation, and the acceptance predicate `sat` |
| `coq/constraints/gen/lts_wires_gen.v` | the eight copy wires, from the output cells to the public cells |
| `coq/constraints/gen/lts_necessity_gen.v` | each copy constraint is necessary: with any one of the eight removed, the model no longer refines the intended public interface (`mutant_wcopy_1_not_refines` and its seven siblings) |
| `coq/constraints/pfcs.v` | a Coq embedding of prime-field constraint systems, following the PFCS formalism |
| `coq/constraints/range_field.v`, `coq/constraints/range_field_pasta.v` | range checks over a prime field, and a primality certificate for the Pasta prime |
| `coq/constraints/field_order_lift.v`, `coq/constraints/bits_kit.v` | lifting facts from the field to the integers; bit decompositions |
| `coq/constraints/lts_semantic.v` | reading pairs off a filling, with the signed reading of the inputs |
| `coq/constraints/lts_model_facts.v` | facts about the model: range bounds on output and carry cells, the signed reading's threshold |
| `coq/constraints/lts_soundness.v` | soundness (`bridge_sound`, `bridge_sound_needs_only_sat`) |
| `coq/constraints/lts_adequacy.v` | completeness, and the two directions as one theorem (`policy_adequacy_lts`) |

## Credits

- The PFCS formalism: A. Coglio, E. McCarthy, E. W. Smith, *Formal Verification of Zero-Knowledge Circuits*,
  arXiv:2311.08858 (ACL2 Workshop 2023). `coq/constraints/pfcs.v` follows it.
- circom-bigint, by its authors (GPL-3.0), whose LongToShortNoEndCarry template this work answers to. Its
  behaviour is described here; none of its code is copied.
- *Auditing Report for circom-bigint (circomlib)*, 0xPARC Community, Ethereum Foundation and Veridise Inc., 2022.

## Licence

Apache-2.0: see [LICENSE](LICENSE) and [NOTICE](NOTICE).

## Contact

Probatur is published by Next Ridge Solutions Ltd: [nxridge.com](https://nxridge.com).
