(** * BrickTree: Physical brick tree model *)

Require Import ZArith List Arith Lia.
Require Import PBPL.Util.
Import ListNotations.
Open Scope Z_scope.

(** ** Token type (matches physical brick types) *)

Inductive token :=
  | TVar   : var -> token
  | TNum   : nat -> token
  | TInc   : token
  | TDec   : token
  | TLet   : token
  | TSemi  : token
  | TIf    : token
  | TIfSep : token
  | TCmpEq : token
  | TGoto  : token
  | TLabel : token
  | THalt  : token.

Definition token_eqb (t1 t2 : token) : bool :=
  match t1, t2 with
  | TVar v1, TVar v2 => var_eqb v1 v2
  | TNum n1, TNum n2 => Nat.eqb n1 n2
  | TInc, TInc => true
  | TDec, TDec => true
  | TLet, TLet => true
  | TSemi, TSemi => true
  | TIf, TIf => true
  | TIfSep, TIfSep => true
  | TCmpEq, TCmpEq => true
  | TGoto, TGoto => true
  | TLabel, TLabel => true
  | THalt, THalt => true
  | _, _ => false
  end.

(** ** Brick tree structure *)

Inductive brick_tree :=
  | BTLeaf : token -> brick_tree
  | BTNode : token -> brick_tree -> brick_tree
  | BTIf   : brick_tree -> brick_tree -> brick_tree ->
             brick_tree -> brick_tree -> brick_tree.
(* BTIf left_cond mid_cond right_cond true_branch false_branch *)

(** ** Expression-only predicate for IF condition sub-connectors *)

Definition is_expr_token (t : token) : Prop :=
  match t with
  | TVar _ | TNum _ | TInc | TDec => True
  | _ => False
  end.

Definition is_cmp_token (t : token) : Prop :=
  match t with
  | TCmpEq => True
  | _ => False
  end.

Inductive is_expr_tree : brick_tree -> Prop :=
  | expr_leaf : forall t, is_expr_token t -> is_expr_tree (BTLeaf t)
  | expr_node : forall t child, is_expr_token t -> is_expr_tree child -> is_expr_tree (BTNode t child).

Inductive is_cmp_tree : brick_tree -> Prop :=
  | cmp_leaf : forall t, is_cmp_token t -> is_cmp_tree (BTLeaf t).

(** ** Well-formedness *)

Inductive wf_tree : brick_tree -> Prop :=
  | wf_leaf : forall t, wf_tree (BTLeaf t)
  | wf_node : forall t child, wf_tree child -> wf_tree (BTNode t child)
  | wf_if : forall lc mc rc tb fb,
      is_expr_tree lc -> is_cmp_tree mc -> is_expr_tree rc ->
      wf_tree tb -> wf_tree fb ->
      wf_tree (BTIf lc mc rc tb fb).

(** ** Flatten *)

Fixpoint flatten (t : brick_tree) : list token :=
  match t with
  | BTLeaf tok => [tok]
  | BTNode tok child => [tok] ++ flatten child
  | BTIf lc mc rc tb fb =>
      [TIf] ++ flatten lc ++ flatten mc ++ flatten rc ++
      [TSemi] ++ flatten tb ++ [TIfSep] ++ flatten fb ++ [TIfSep]
  end.

(** Basic flatten lemmas *)

Lemma flatten_nonempty : forall t, flatten t <> [].
Proof.
  destruct t; simpl; discriminate.
Qed.
