(** * Compile: Minsky machine → Brick Tree → PBPL program *)

Require Import ZArith List Arith Lia.
Require Import PBPL.Util PBPL.BrickTree PBPL.PBPL PBPL.Minsky.
Import ListNotations.
Open Scope nat_scope.

(** ** Counter to variable mapping *)

Definition counter_var (c : counter) : var :=
  match c with
  | C1 => VarA
  | C2 => VarB
  end.

(** ** Compile a single Minsky instruction to PBPL statements.
    Label scheme: instruction i → main label 2*i, aux label 2*i+1 *)

Definition compile_instr (i : nat) (instr : minsky_instr) : list (label * stmt) :=
  match instr with
  | MInc c next =>
      [(2*i, SInc (counter_var c) (2*next))]
  | MDec c next_nz next_z =>
      [(2*i,     SIf (EVar (counter_var c)) CmpEq (ENum 0%Z) (2*next_z) (2*i+1));
       (2*i+1,   SDec (counter_var c) (2*next_nz))]
  | MHalt =>
      [(2*i, SHalt)]
  end.

(** ** Compile entire Minsky program *)

Fixpoint compile_aux (i : nat) (mp : minsky_program) : program :=
  match mp with
  | [] => []
  | instr :: rest => compile_instr i instr ++ compile_aux (S i) rest
  end.

Definition compile (mp : minsky_program) : program :=
  compile_aux 0 mp.

(** ** Brick tree compilation *)

Definition compile_instr_tree (i : nat) (instr : minsky_instr) : brick_tree :=
  match instr with
  | MInc c next =>
      BTNode (TLabel) (BTNode (TNum (2*i))
        (BTNode TSemi (BTNode TInc (BTNode (TVar (counter_var c))
          (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next)))))))))
  | MDec c next_nz next_z =>
      BTIf (BTLeaf (TVar (counter_var c)))
           (BTLeaf TCmpEq)
           (BTLeaf (TNum 0))
           (BTNode TGoto (BTLeaf (TNum (2*next_z))))
           (BTNode (TLabel) (BTNode (TNum (2*i+1))
             (BTNode TSemi (BTNode TDec (BTNode (TVar (counter_var c))
               (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next_nz))))))))))
  | MHalt =>
      BTNode TLabel (BTNode (TNum (2*i)) (BTLeaf THalt))
  end.

Fixpoint compile_tree_aux (i : nat) (mp : minsky_program) : list brick_tree :=
  match mp with
  | [] => []
  | instr :: rest => compile_instr_tree i instr :: compile_tree_aux (S i) rest
  end.

Definition chain_trees (ts : list brick_tree) : brick_tree :=
  match ts with
  | [] => BTLeaf THalt
  | t :: _ => t
  end.

Definition compile_tree (mp : minsky_program) : brick_tree :=
  chain_trees (compile_tree_aux 0 mp).

(** ** Well-formedness of compiled trees *)

Lemma compile_instr_tree_wf : forall i instr,
  wf_tree (compile_instr_tree i instr).
Proof.
  intros. destruct instr.
  - destruct c; simpl; repeat constructor.
  - destruct c; simpl; repeat constructor; simpl; auto.
  - simpl. repeat constructor.
Qed.

Theorem compile_wf : forall mp,
  wf_tree (compile_tree mp).
Proof.
  intros. unfold compile_tree.
  destruct mp as [|instr rest].
  - simpl. constructor.
  - simpl. destruct rest; apply compile_instr_tree_wf.
Qed.

(** ** Fetch helpers *)

Lemma fetch_app_l : forall P1 P2 l s,
  fetch P1 l = Some s ->
  fetch (P1 ++ P2) l = Some s.
Proof.
  induction P1; intros.
  - discriminate.
  - destruct a as [l' s']. simpl in *. destruct (Nat.eqb l l').
    + exact H.
    + apply IHP1. exact H.
Qed.

Lemma fetch_app_r : forall P1 P2 l,
  fetch P1 l = None ->
  fetch (P1 ++ P2) l = fetch P2 l.
Proof.
  induction P1; intros.
  - reflexivity.
  - destruct a as [l' s']. simpl in *. destruct (Nat.eqb l l').
    + discriminate.
    + apply IHP1. exact H.
Qed.

(** compile_instr returns None for labels outside its range *)
Lemma fetch_compile_instr_none : forall i instr l,
  l < 2 * i \/ l >= 2 * i + 2 ->
  fetch (compile_instr i instr) l = None.
Proof.
  intros i instr l Hrange.
  assert (Hne_main: l <> 2 * i) by lia.
  assert (Hne_aux: l <> 2 * i + 1) by lia.
  destruct instr; unfold compile_instr;
    unfold fetch; fold fetch;
    rewrite (proj2 (Nat.eqb_neq _ _) Hne_main);
    try reflexivity.
  unfold fetch. rewrite (proj2 (Nat.eqb_neq _ _) Hne_aux). reflexivity.
Qed.

(** ** Key fetch lemmas - proved by induction on mp *)

(** The step case tactic: skip past compile_instr j a *)
Ltac skip_instr :=
  change (compile_aux ?j (?a :: ?mp)) with
    (compile_instr j a ++ compile_aux (S j) mp);
  rewrite fetch_app_r;
  [ replace (S ?j) with (?j + 1) by lia | apply fetch_compile_instr_none; lia ].

Lemma fetch_compile_aux_inc : forall mp j i c next,
  nth_error mp i = Some (MInc c next) ->
  fetch (compile_aux j mp) (2 * (j + i)) = Some (SInc (counter_var c) (2 * next)).
Proof.
  induction mp; intros.
  - destruct i; discriminate.
  - destruct i.
    + simpl in H. inversion H. subst.
      change (compile_aux j (MInc c next :: mp)) with
        (compile_instr j (MInc c next) ++ compile_aux (S j) mp).
      replace (j + 0) with j by lia.
      apply fetch_app_l. unfold compile_instr, fetch.
      rewrite Nat.eqb_refl. reflexivity.
    + change (compile_aux j (a :: mp)) with
        (compile_instr j a ++ compile_aux (S j) mp).
      rewrite fetch_app_r.
      * replace (S j) with (j + 1) by lia.
        specialize (IHmp (j + 1) i c next H).
        replace (j + 1 + i) with (j + S i) in IHmp by lia.
        exact IHmp.
      * apply fetch_compile_instr_none. lia.
Qed.

Lemma fetch_compile_aux_if : forall mp j i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  fetch (compile_aux j mp) (2 * (j + i)) =
    Some (SIf (EVar (counter_var c)) CmpEq (ENum 0%Z) (2 * next_z) (2 * (j + i) + 1)).
Proof.
  induction mp; intros.
  - destruct i; discriminate.
  - destruct i.
    + simpl in H. inversion H. subst.
      change (compile_aux j (MDec c next_nz next_z :: mp)) with
        (compile_instr j (MDec c next_nz next_z) ++ compile_aux (S j) mp).
      replace (j + 0) with j by lia.
      apply fetch_app_l. unfold compile_instr, fetch.
      rewrite Nat.eqb_refl. reflexivity.
    + change (compile_aux j (a :: mp)) with
        (compile_instr j a ++ compile_aux (S j) mp).
      rewrite fetch_app_r.
      * replace (S j) with (j + 1) by lia.
        specialize (IHmp (j + 1) i c next_nz next_z H).
        replace (j + 1 + i) with (j + S i) in IHmp by lia.
        exact IHmp.
      * apply fetch_compile_instr_none. lia.
Qed.

Lemma fetch_compile_aux_dec : forall mp j i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  fetch (compile_aux j mp) (2 * (j + i) + 1) =
    Some (SDec (counter_var c) (2 * next_nz)).
Proof.
  induction mp; intros.
  - destruct i; discriminate.
  - destruct i.
    + simpl in H. inversion H. subst.
      change (compile_aux j (MDec c next_nz next_z :: mp)) with
        (compile_instr j (MDec c next_nz next_z) ++ compile_aux (S j) mp).
      replace (j + 0) with j by lia.
      apply fetch_app_l. unfold compile_instr, fetch. fold fetch.
      rewrite (proj2 (Nat.eqb_neq (2 * j + 1) (2 * j)) (ltac:(lia))).
      unfold fetch. rewrite Nat.eqb_refl. reflexivity.
    + change (compile_aux j (a :: mp)) with
        (compile_instr j a ++ compile_aux (S j) mp).
      rewrite fetch_app_r.
      * replace (S j) with (j + 1) by lia.
        specialize (IHmp (j + 1) i c next_nz next_z H).
        replace (j + 1 + i) with (j + S i) in IHmp by lia.
        exact IHmp.
      * apply fetch_compile_instr_none. lia.
Qed.

Lemma fetch_compile_aux_halt : forall mp j i,
  nth_error mp i = Some MHalt ->
  fetch (compile_aux j mp) (2 * (j + i)) = Some SHalt.
Proof.
  induction mp; intros.
  - destruct i; discriminate.
  - destruct i.
    + simpl in H. inversion H. subst.
      change (compile_aux j (MHalt :: mp)) with
        (compile_instr j MHalt ++ compile_aux (S j) mp).
      replace (j + 0) with j by lia.
      apply fetch_app_l. unfold compile_instr, fetch.
      rewrite Nat.eqb_refl. reflexivity.
    + change (compile_aux j (a :: mp)) with
        (compile_instr j a ++ compile_aux (S j) mp).
      rewrite fetch_app_r.
      * replace (S j) with (j + 1) by lia.
        specialize (IHmp (j + 1) i H).
        replace (j + 1 + i) with (j + S i) in IHmp by lia.
        exact IHmp.
      * apply fetch_compile_instr_none. lia.
Qed.

(** ** Top-level fetch lemmas used by Simulation *)

Lemma fetch_compile_inc : forall mp i c next,
  nth_error mp i = Some (MInc c next) ->
  fetch (compile mp) (2 * i) = Some (SInc (counter_var c) (2 * next)).
Proof.
  intros. unfold compile.
  replace (2 * i) with (2 * (0 + i)) by lia.
  apply fetch_compile_aux_inc. exact H.
Qed.

Lemma fetch_compile_if : forall mp i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  fetch (compile mp) (2 * i) =
    Some (SIf (EVar (counter_var c)) CmpEq (ENum 0%Z) (2 * next_z) (2 * i + 1)).
Proof.
  intros. unfold compile.
  replace (2 * i) with (2 * (0 + i)) by lia.
  replace (2 * i + 1) with (2 * (0 + i) + 1) by lia.
  eapply fetch_compile_aux_if. exact H.
Qed.

Lemma fetch_compile_dec : forall mp i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  fetch (compile mp) (2 * i + 1) =
    Some (SDec (counter_var c) (2 * next_nz)).
Proof.
  intros. unfold compile.
  replace (2 * i + 1) with (2 * (0 + i) + 1) by lia.
  eapply fetch_compile_aux_dec. exact H.
Qed.

Lemma fetch_compile_halt : forall mp i,
  nth_error mp i = Some MHalt ->
  fetch (compile mp) (2 * i) = Some SHalt.
Proof.
  intros. unfold compile.
  replace (2 * i) with (2 * (0 + i)) by lia.
  apply fetch_compile_aux_halt. exact H.
Qed.
