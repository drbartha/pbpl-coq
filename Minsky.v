(** * Minsky: 2-counter Minsky machine *)

Require Import ZArith List Arith Lia.
Import ListNotations.

(** ** Counters *)

Inductive counter := C1 | C2.

(** ** Instructions *)

Inductive minsky_instr :=
  | MInc  : counter -> nat -> minsky_instr         (* inc counter, goto label *)
  | MDec  : counter -> nat -> nat -> minsky_instr   (* dec counter, goto-if-nz, goto-if-z *)
  | MHalt : minsky_instr.

Definition minsky_program := list minsky_instr.

(** ** Configuration: (pc, counter1, counter2) *)

Definition minsky_config := (nat * nat * nat)%type.

(** ** Small-step semantics *)

Inductive minsky_step (P : minsky_program) : minsky_config -> minsky_config -> Prop :=
  | ms_inc_c1 : forall pc c1 c2 next,
      nth_error P pc = Some (MInc C1 next) ->
      minsky_step P (pc, c1, c2) (next, S c1, c2)
  | ms_inc_c2 : forall pc c1 c2 next,
      nth_error P pc = Some (MInc C2 next) ->
      minsky_step P (pc, c1, c2) (next, c1, S c2)
  | ms_dec_c1_nz : forall pc c1 c2 next_nz next_z,
      nth_error P pc = Some (MDec C1 next_nz next_z) ->
      c1 > 0 ->
      minsky_step P (pc, c1, c2) (next_nz, pred c1, c2)
  | ms_dec_c1_z : forall pc c2 next_nz next_z,
      nth_error P pc = Some (MDec C1 next_nz next_z) ->
      minsky_step P (pc, 0, c2) (next_z, 0, c2)
  | ms_dec_c2_nz : forall pc c1 c2 next_nz next_z,
      nth_error P pc = Some (MDec C2 next_nz next_z) ->
      c2 > 0 ->
      minsky_step P (pc, c1, c2) (next_nz, c1, pred c2)
  | ms_dec_c2_z : forall pc c1 next_nz next_z,
      nth_error P pc = Some (MDec C2 next_nz next_z) ->
      minsky_step P (pc, c1, 0) (next_z, c1, 0).
