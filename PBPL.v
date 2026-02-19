(** * PBPL: Minimal PBPL syntax and small-step semantics *)

Require Import ZArith List Arith Lia.
Require Import PBPL.Util PBPL.BrickTree.
Import ListNotations.
Open Scope Z_scope.

(** ** Abstract syntax *)

Inductive expr :=
  | ENum : Z -> expr
  | EVar : var -> expr.

Inductive cmp := CmpEq.

Definition label := nat.

(** All statements have explicit control flow targets *)
Inductive stmt :=
  | SInc  : var -> label -> stmt        (* inc v; goto l *)
  | SDec  : var -> label -> stmt        (* dec v; goto l *)
  | SIf   : expr -> cmp -> expr -> label -> label -> stmt  (* if e1==e2 goto lt else goto lf *)
  | SGoto : label -> stmt               (* goto l *)
  | SHalt : stmt.                       (* halt *)

Definition program := list (label * stmt).

(** ** Evaluation *)

Definition eval_expr (s : store) (e : expr) : Z :=
  match e with
  | ENum n => n
  | EVar v => s v
  end.

(** ** Program lookup *)

Fixpoint fetch (P : program) (l : label) : option stmt :=
  match P with
  | [] => None
  | (l', s) :: rest =>
      if Nat.eqb l l' then Some s
      else fetch rest l
  end.

Lemma fetch_cons : forall l l' s rest,
  fetch ((l', s) :: rest) l =
  if Nat.eqb l l' then Some s else fetch rest l.
Proof. reflexivity. Qed.

Lemma fetch_eq : forall l s rest,
  fetch ((l, s) :: rest) l = Some s.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma fetch_neq : forall l l' s rest,
  l <> l' -> fetch ((l', s) :: rest) l = fetch rest l.
Proof.
  intros. simpl. destruct (Nat.eqb l l') eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

(** ** Configuration *)

Definition config := (label * store)%type.

(** ** Small-step semantics *)

Inductive step (P : program) : config -> config -> Prop :=
  | step_inc : forall l s v l_next,
      fetch P l = Some (SInc v l_next) ->
      step P (l, s) (l_next, update s v (s v + 1))
  | step_dec : forall l s v l_next,
      fetch P l = Some (SDec v l_next) ->
      step P (l, s) (l_next, update s v (s v - 1))
  | step_if_true : forall l s e1 e2 lt lf,
      fetch P l = Some (SIf e1 CmpEq e2 lt lf) ->
      eval_expr s e1 = eval_expr s e2 ->
      step P (l, s) (lt, s)
  | step_if_false : forall l s e1 e2 lt lf,
      fetch P l = Some (SIf e1 CmpEq e2 lt lf) ->
      eval_expr s e1 <> eval_expr s e2 ->
      step P (l, s) (lf, s)
  | step_goto : forall l s l_target,
      fetch P l = Some (SGoto l_target) ->
      step P (l, s) (l_target, s).
