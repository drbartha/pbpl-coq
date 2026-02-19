(** * Util: Shared helpers for the PBPL Turing-completeness proof *)

Require Import ZArith List Arith Lia.
Import ListNotations.
Open Scope Z_scope.

(** ** Variables *)

Inductive var := VarA | VarB | VarC.

Definition var_eqb (v1 v2 : var) : bool :=
  match v1, v2 with
  | VarA, VarA => true
  | VarB, VarB => true
  | VarC, VarC => true
  | _, _ => false
  end.

Lemma var_eqb_refl : forall v, var_eqb v v = true.
Proof. destruct v; reflexivity. Qed.

Lemma var_eqb_eq : forall v1 v2, var_eqb v1 v2 = true <-> v1 = v2.
Proof.
  destruct v1, v2; simpl; split; intros; try reflexivity; try discriminate; try congruence.
Qed.

Lemma var_eqb_neq : forall v1 v2, var_eqb v1 v2 = false <-> v1 <> v2.
Proof.
  destruct v1, v2; simpl; split; intros; try discriminate; try congruence; auto.
Qed.

Lemma var_eq_dec : forall (v1 v2 : var), {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Defined.

(** ** Stores (variable -> Z) *)

Definition store := var -> Z.

Definition empty_store : store := fun _ => 0.

Definition update (s : store) (v : var) (val : Z) : store :=
  fun v' => if var_eqb v v' then val else s v'.

Lemma update_eq : forall s v val, update s v val v = val.
Proof. intros. unfold update. rewrite var_eqb_refl. reflexivity. Qed.

Lemma update_neq : forall s v1 v2 val,
  v1 <> v2 -> update s v1 val v2 = s v2.
Proof.
  intros. unfold update.
  destruct (var_eqb v1 v2) eqn:E.
  - apply var_eqb_eq in E. congruence.
  - reflexivity.
Qed.

(** ** Reflexive transitive closure *)

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | star_refl : forall x, star R x x
  | star_step : forall x y z, R x y -> star R y z -> star R x z.

Lemma star_one : forall {A} (R : A -> A -> Prop) x y,
  R x y -> star R x y.
Proof.
  intros. eapply star_step; eauto. constructor.
Qed.

Lemma star_trans : forall {A} (R : A -> A -> Prop) x y z,
  star R x y -> star R y z -> star R x z.
Proof.
  intros A R x y z H1. revert z.
  induction H1; intros.
  - assumption.
  - eapply star_step; eauto.
Qed.

(** ** Nat helper *)

Lemma nth_error_app_l : forall {A} (l1 l2 : list A) (n : nat),
  (n < length l1)%nat ->
  nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
  intros A l1. induction l1; intros; simpl in *.
  - lia.
  - destruct n; auto. apply IHl1. lia.
Qed.

Lemma nth_error_app_r : forall {A} (l1 l2 : list A) (n : nat),
  nth_error (l1 ++ l2) (length l1 + n) = nth_error l2 n.
Proof.
  intros A l1. induction l1; intros; simpl.
  - reflexivity.
  - apply IHl1.
Qed.
