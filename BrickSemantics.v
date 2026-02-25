(** * BrickSemantics: Mathematical PBPL machine semantics via brick trees *)

(** A [btree_program] maps each label to an instruction subtree.
    [bt_step] is the step relation of the mathematical PBPL machine.
    [pbpl_machine_tc] is the top-level Turing-completeness theorem
    stated in terms of physical brick trees. *)

Require Import ZArith List Arith Lia.
Require Import PBPL.Util PBPL.BrickTree PBPL.PBPL PBPL.Minsky PBPL.Compile PBPL.Simulation.
Import ListNotations.
Open Scope nat_scope.

(** ** Brick program: list of (label, instruction-subtree) pairs *)

Definition btree_program := list (label * brick_tree).

(** ** Lookup *)

Fixpoint bt_fetch (bp : btree_program) (l : label) : option brick_tree :=
  match bp with
  | [] => None
  | (l', t) :: rest =>
      if Nat.eqb l l' then Some t else bt_fetch rest l
  end.

Lemma bt_fetch_eq : forall l t rest,
  bt_fetch ((l, t) :: rest) l = Some t.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma bt_fetch_neq : forall l l' t rest,
  l <> l' -> bt_fetch ((l', t) :: rest) l = bt_fetch rest l.
Proof.
  intros. simpl. rewrite (proj2 (Nat.eqb_neq _ _) H). reflexivity.
Qed.

Lemma bt_fetch_app_l : forall bp1 bp2 l t,
  bt_fetch bp1 l = Some t ->
  bt_fetch (bp1 ++ bp2) l = Some t.
Proof.
  induction bp1; intros.
  - discriminate.
  - destruct a as [l' t']. simpl in *.
    destruct (Nat.eqb l l').
    + exact H.
    + apply IHbp1. exact H.
Qed.

Lemma bt_fetch_app_r : forall bp1 bp2 l,
  bt_fetch bp1 l = None ->
  bt_fetch (bp1 ++ bp2) l = bt_fetch bp2 l.
Proof.
  induction bp1; intros.
  - reflexivity.
  - destruct a as [l' t']. simpl in *.
    destruct (Nat.eqb l l').
    + discriminate.
    + apply IHbp1. exact H.
Qed.

(** ** Compile Minsky instruction to btree_program entries *)

(** Each [MInc] becomes one entry; each [MDec] becomes two entries
    (label [2*i] for the IF test, label [2*i+1] for the decrement). *)

Definition compile_instr_btree (i : nat) (instr : minsky_instr) : btree_program :=
  match instr with
  | MInc c next =>
      [(2*i, BTNode TInc (BTNode (TVar (counter_var c))
               (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next)))))))]
  | MDec c next_nz next_z =>
      [(2*i,   BTIf (BTLeaf (TVar (counter_var c)))
                    (BTLeaf TCmpEq)
                    (BTLeaf (TNum 0))
                    (BTNode TGoto (BTLeaf (TNum (2*next_z))))
                    (BTNode TGoto (BTLeaf (TNum (2*i+1)))));
       (2*i+1, BTNode TDec (BTNode (TVar (counter_var c))
                 (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next_nz)))))))]
  | MHalt =>
      [(2*i, BTLeaf THalt)]
  end.

Fixpoint compile_btree_aux (i : nat) (mp : minsky_program) : btree_program :=
  match mp with
  | [] => []
  | instr :: rest => compile_instr_btree i instr ++ compile_btree_aux (S i) rest
  end.

Definition compile_btree (mp : minsky_program) : btree_program :=
  compile_btree_aux 0 mp.

(** ** Evaluate one instruction brick tree *)

(** [eval_tree] interprets the brick tree rooted at a label,
    returning the next [(label, store)] or [None] for [BTLeaf THalt]. *)

Definition eval_tree (t : brick_tree) (s : store) : option (label * store) :=
  match t with
  | BTNode TInc (BTNode (TVar v) (BTNode TSemi (BTNode TGoto (BTLeaf (TNum l_next))))) =>
      Some (l_next, update s v (s v + 1)%Z)
  | BTNode TDec (BTNode (TVar v) (BTNode TSemi (BTNode TGoto (BTLeaf (TNum l_next))))) =>
      Some (l_next, update s v (s v - 1)%Z)
  | BTIf (BTLeaf (TVar v)) (BTLeaf TCmpEq) (BTLeaf (TNum 0))
         (BTNode TGoto (BTLeaf (TNum l_true)))
         (BTNode TGoto (BTLeaf (TNum l_false))) =>
      if Z.eqb (s v) 0%Z then Some (l_true, s)
      else Some (l_false, s)
  | BTLeaf THalt => None
  | _ => None
  end.

(** ** Mathematical PBPL machine step *)

Inductive bt_step (bp : btree_program) : config -> config -> Prop :=
  | bts_exec : forall l s t l' s',
      bt_fetch bp l = Some t ->
      eval_tree t s = Some (l', s') ->
      bt_step bp (l, s) (l', s').

(** ** bt_fetch correctness lemmas *)

Lemma bt_fetch_compile_instr_none : forall i instr l,
  l < 2 * i \/ l >= 2 * i + 2 ->
  bt_fetch (compile_instr_btree i instr) l = None.
Proof.
  intros i instr l Hrange.
  assert (Hne_main : l <> 2 * i) by lia.
  assert (Hne_aux  : l <> 2 * i + 1) by lia.
  destruct instr; unfold compile_instr_btree.
  - rewrite bt_fetch_neq by exact Hne_main. reflexivity.
  - rewrite bt_fetch_neq by exact Hne_main.
    rewrite bt_fetch_neq by exact Hne_aux. reflexivity.
  - rewrite bt_fetch_neq by exact Hne_main. reflexivity.
Qed.

Lemma bt_fetch_compile_btree_aux_inc : forall mp j i c next,
  nth_error mp i = Some (MInc c next) ->
  bt_fetch (compile_btree_aux j mp) (2 * (j + i)) =
    Some (BTNode TInc (BTNode (TVar (counter_var c))
           (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next))))))).
Proof.
  induction mp; intros.
  - destruct i; discriminate.
  - destruct i.
    + simpl in H. inversion H. subst.
      change (compile_btree_aux j (MInc c next :: mp)) with
        (compile_instr_btree j (MInc c next) ++ compile_btree_aux (S j) mp).
      replace (j + 0) with j by lia.
      apply bt_fetch_app_l.
      unfold compile_instr_btree. rewrite bt_fetch_eq. reflexivity.
    + change (compile_btree_aux j (a :: mp)) with
        (compile_instr_btree j a ++ compile_btree_aux (S j) mp).
      rewrite bt_fetch_app_r.
      * replace (S j) with (j + 1) by lia.
        specialize (IHmp (j + 1) i c next H).
        replace (j + 1 + i) with (j + S i) in IHmp by lia.
        exact IHmp.
      * apply bt_fetch_compile_instr_none. lia.
Qed.

Lemma bt_fetch_compile_btree_aux_if : forall mp j i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  bt_fetch (compile_btree_aux j mp) (2 * (j + i)) =
    Some (BTIf (BTLeaf (TVar (counter_var c)))
               (BTLeaf TCmpEq) (BTLeaf (TNum 0))
               (BTNode TGoto (BTLeaf (TNum (2*next_z))))
               (BTNode TGoto (BTLeaf (TNum (2*(j+i)+1))))).
Proof.
  induction mp; intros.
  - destruct i; discriminate.
  - destruct i.
    + simpl in H. inversion H. subst.
      change (compile_btree_aux j (MDec c next_nz next_z :: mp)) with
        (compile_instr_btree j (MDec c next_nz next_z) ++ compile_btree_aux (S j) mp).
      replace (j + 0) with j by lia.
      apply bt_fetch_app_l.
      unfold compile_instr_btree. rewrite bt_fetch_eq. reflexivity.
    + change (compile_btree_aux j (a :: mp)) with
        (compile_instr_btree j a ++ compile_btree_aux (S j) mp).
      rewrite bt_fetch_app_r.
      * replace (S j) with (j + 1) by lia.
        specialize (IHmp (j + 1) i c next_nz next_z H).
        replace (j + 1 + i) with (j + S i) in IHmp by lia.
        exact IHmp.
      * apply bt_fetch_compile_instr_none. lia.
Qed.

Lemma bt_fetch_compile_btree_aux_dec : forall mp j i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  bt_fetch (compile_btree_aux j mp) (2 * (j + i) + 1) =
    Some (BTNode TDec (BTNode (TVar (counter_var c))
           (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next_nz))))))).
Proof.
  induction mp; intros.
  - destruct i; discriminate.
  - destruct i.
    + simpl in H. inversion H. subst.
      change (compile_btree_aux j (MDec c next_nz next_z :: mp)) with
        (compile_instr_btree j (MDec c next_nz next_z) ++ compile_btree_aux (S j) mp).
      replace (j + 0) with j by lia.
      apply bt_fetch_app_l.
      unfold compile_instr_btree.
      rewrite bt_fetch_neq by lia.
      rewrite bt_fetch_eq. reflexivity.
    + change (compile_btree_aux j (a :: mp)) with
        (compile_instr_btree j a ++ compile_btree_aux (S j) mp).
      rewrite bt_fetch_app_r.
      * replace (S j) with (j + 1) by lia.
        specialize (IHmp (j + 1) i c next_nz next_z H).
        replace (j + 1 + i) with (j + S i) in IHmp by lia.
        exact IHmp.
      * apply bt_fetch_compile_instr_none. lia.
Qed.

(** Top-level bt_fetch lemmas used by the simulation proof *)

Lemma bt_fetch_compile_btree_inc : forall mp i c next,
  nth_error mp i = Some (MInc c next) ->
  bt_fetch (compile_btree mp) (2 * i) =
    Some (BTNode TInc (BTNode (TVar (counter_var c))
           (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next))))))).
Proof.
  intros. unfold compile_btree.
  replace (2 * i) with (2 * (0 + i)) by lia.
  apply bt_fetch_compile_btree_aux_inc. exact H.
Qed.

Lemma bt_fetch_compile_btree_if : forall mp i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  bt_fetch (compile_btree mp) (2 * i) =
    Some (BTIf (BTLeaf (TVar (counter_var c)))
               (BTLeaf TCmpEq) (BTLeaf (TNum 0))
               (BTNode TGoto (BTLeaf (TNum (2*next_z))))
               (BTNode TGoto (BTLeaf (TNum (2*i+1))))).
Proof.
  intros. unfold compile_btree.
  replace (2 * i) with (2 * (0 + i)) by lia.
  replace (2 * i + 1) with (2 * (0 + i) + 1) by lia.
  eapply bt_fetch_compile_btree_aux_if. exact H.
Qed.

Lemma bt_fetch_compile_btree_dec : forall mp i c next_nz next_z,
  nth_error mp i = Some (MDec c next_nz next_z) ->
  bt_fetch (compile_btree mp) (2 * i + 1) =
    Some (BTNode TDec (BTNode (TVar (counter_var c))
           (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next_nz))))))).
Proof.
  intros. unfold compile_btree.
  replace (2 * i + 1) with (2 * (0 + i) + 1) by lia.
  eapply bt_fetch_compile_btree_aux_dec. exact H.
Qed.

(** ** Forward simulation: one Minsky step --> one or more bt_steps *)

Theorem simulate_bt_step :
  forall (mp : minsky_program) (mc1 mc2 : minsky_config),
    minsky_step mp mc1 mc2 ->
    forall pc1, match_config mc1 pc1 ->
    exists pc2,
      star (bt_step (compile_btree mp)) pc1 pc2 /\
      match_config mc2 pc2.
Proof.
  intros mp mc1 mc2 Hmstep pc1 Hmatch.
  destruct pc1 as [l s].
  inversion Hmstep; subst.

  (* Case 1: INC C1 *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (bt_fetch_compile_btree_inc mp _ _ _ H) as Hfetch.
    exists (2 * next, update s VarA (s VarA + 1)%Z).
    split.
    + apply star_one. econstructor. exact Hfetch. reflexivity.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_eq. rewrite Ha. lia.
      * rewrite update_neq by discriminate. exact Hb.

  (* Case 2: INC C2 *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (bt_fetch_compile_btree_inc mp _ _ _ H) as Hfetch.
    exists (2 * next, update s VarB (s VarB + 1)%Z).
    split.
    + apply star_one. econstructor. exact Hfetch. reflexivity.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_neq by discriminate. exact Ha.
      * rewrite update_eq. rewrite Hb. lia.

  (* Case 3: DEC C1 nonzero - two bt_steps: IF-false then DEC *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (bt_fetch_compile_btree_if mp _ _ _ _ H) as Hfetch_if.
    pose proof (bt_fetch_compile_btree_dec mp _ _ _ _ H) as Hfetch_dec.
    exists (2 * next_nz, update s VarA (s VarA - 1)%Z).
    split.
    + eapply star_step.
      * econstructor. exact Hfetch_if.
        unfold eval_tree, counter_var.
        destruct (Z.eqb_spec (s VarA) 0%Z) as [Heq | Hne].
        -- exfalso. rewrite Ha in Heq. lia.
        -- reflexivity.
      * eapply star_step.
        -- econstructor. exact Hfetch_dec. reflexivity.
        -- apply star_refl.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_eq. rewrite Ha. lia.
      * rewrite update_neq by discriminate. exact Hb.

  (* Case 4: DEC C1 zero - one bt_step: IF-true *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (bt_fetch_compile_btree_if mp _ _ _ _ H) as Hfetch_if.
    exists (2 * next_z, s).
    split.
    + apply star_one. econstructor. exact Hfetch_if.
      unfold eval_tree, counter_var.
      destruct (Z.eqb_spec (s VarA) 0%Z) as [Heq | Hne].
      * reflexivity.
      * exfalso. apply Hne. rewrite Ha. reflexivity.
    + unfold match_config. split; [lia|]. split; assumption.

  (* Case 5: DEC C2 nonzero - two bt_steps: IF-false then DEC *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (bt_fetch_compile_btree_if mp _ _ _ _ H) as Hfetch_if.
    pose proof (bt_fetch_compile_btree_dec mp _ _ _ _ H) as Hfetch_dec.
    exists (2 * next_nz, update s VarB (s VarB - 1)%Z).
    split.
    + eapply star_step.
      * econstructor. exact Hfetch_if.
        unfold eval_tree, counter_var.
        destruct (Z.eqb_spec (s VarB) 0%Z) as [Heq | Hne].
        -- exfalso. rewrite Hb in Heq. lia.
        -- reflexivity.
      * eapply star_step.
        -- econstructor. exact Hfetch_dec. reflexivity.
        -- apply star_refl.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_neq by discriminate. exact Ha.
      * rewrite update_eq. rewrite Hb. lia.

  (* Case 6: DEC C2 zero - one bt_step: IF-true *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (bt_fetch_compile_btree_if mp _ _ _ _ H) as Hfetch_if.
    exists (2 * next_z, s).
    split.
    + apply star_one. econstructor. exact Hfetch_if.
      unfold eval_tree, counter_var.
      destruct (Z.eqb_spec (s VarB) 0%Z) as [Heq | Hne].
      * reflexivity.
      * exfalso. apply Hne. rewrite Hb. reflexivity.
    + unfold match_config. split; [lia|]. split; assumption.
Qed.

(** ** Top-level Turing-completeness theorem for the mathematical PBPL machine *)

Theorem pbpl_machine_tc :
  forall (mp : minsky_program),
    (forall mc1 mc2,
      minsky_step mp mc1 mc2 ->
      forall pc1, match_config mc1 pc1 ->
      exists pc2,
        star (bt_step (compile_btree mp)) pc1 pc2 /\
        match_config mc2 pc2).
Proof.
  intros mp mc1 mc2 Hmstep pc1 Hmatch.
  eapply simulate_bt_step; eassumption.
Qed.

(** ** Well-formedness of compiled btree entries *)

Lemma compile_instr_btree_wf : forall i instr l t,
  In (l, t) (compile_instr_btree i instr) -> wf_tree t.
Proof.
  intros i instr l t Hin.
  destruct instr as [c next | c next_nz next_z |]; simpl in Hin.
  - destruct Hin as [H | []]. injection H; intros; subst. repeat constructor.
  - destruct Hin as [H | [H | []]]; injection H; intros; subst.
    + apply wf_if.
      * apply expr_leaf. destruct c; exact I.
      * apply cmp_leaf. exact I.
      * apply expr_leaf. exact I.
      * repeat constructor.
      * repeat constructor.
    + repeat constructor.
  - destruct Hin as [H | []]. injection H; intros; subst. constructor.
Qed.

Lemma compile_btree_aux_entries_wf : forall mp j l t,
  In (l, t) (compile_btree_aux j mp) -> wf_tree t.
Proof.
  induction mp as [|instr rest IH]; intros j l t Hin.
  - contradiction.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [H | H].
    + eapply compile_instr_btree_wf. exact H.
    + eapply IH. exact H.
Qed.

Lemma compile_btree_entries_wf : forall mp l t,
  In (l, t) (compile_btree mp) -> wf_tree t.
Proof.
  intros mp l t Hin.
  unfold compile_btree in Hin. eapply compile_btree_aux_entries_wf. exact Hin.
Qed.

(** ** Bridge theorem: bt_step <--> step *)

(** bt_fetch success implies list membership *)
Lemma bt_fetch_gives_In : forall bp l t,
  bt_fetch bp l = Some t -> In (l, t) bp.
Proof.
  induction bp as [|[l' t'] rest IH]; intros l t H.
  - discriminate.
  - simpl in H. destruct (Nat.eqb l l') eqn:E.
    + apply Nat.eqb_eq in E. injection H; intros; subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(** fetch success implies list membership *)
Lemma fetch_gives_In : forall P l stmt,
  fetch P l = Some stmt -> In (l, stmt) P.
Proof.
  induction P as [|[l' s'] rest IH]; intros l stmt H.
  - discriminate.
  - simpl in H. destruct (Nat.eqb l l') eqn:E.
    + apply Nat.eqb_eq in E. injection H; intros; subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(** Any entry in compile_btree_aux comes from a specific instruction *)
Lemma compile_btree_aux_In_inv : forall mp j l t,
  In (l, t) (compile_btree_aux j mp) ->
  exists i instr,
    nth_error mp i = Some instr /\
    In (l, t) (compile_instr_btree (j + i) instr).
Proof.
  induction mp as [|instr rest IH]; intros j l t Hin.
  - contradiction.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [H | H].
    + exists 0, instr. rewrite Nat.add_0_r. split; [reflexivity | exact H].
    + destruct (IH (S j) l t H) as [i' [instr' [Hnth Hmem]]].
      exists (S i'), instr'. split.
      * exact Hnth.
      * replace (j + S i') with (S j + i') by lia. exact Hmem.
Qed.

(** Any entry in compile_aux comes from a specific instruction *)
Lemma compile_aux_In_inv : forall mp j l stmt,
  In (l, stmt) (compile_aux j mp) ->
  exists i instr,
    nth_error mp i = Some instr /\
    In (l, stmt) (compile_instr (j + i) instr).
Proof.
  induction mp as [|instr rest IH]; intros j l stmt Hin.
  - contradiction.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [H | H].
    + exists 0, instr. rewrite Nat.add_0_r. split; [reflexivity | exact H].
    + destruct (IH (S j) l stmt H) as [i' [instr' [Hnth Hmem]]].
      exists (S i'), instr'. split.
      * exact Hnth.
      * replace (j + S i') with (S j + i') by lia. exact Hmem.
Qed.

(** Shape characterization for btree entries *)
Lemma compile_instr_btree_In_shapes : forall i instr l t,
  In (l, t) (compile_instr_btree i instr) ->
  match instr with
  | MInc c next =>
      l = 2*i /\
      t = BTNode TInc (BTNode (TVar (counter_var c))
            (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next))))))
  | MDec c next_nz next_z =>
      (l = 2*i /\
       t = BTIf (BTLeaf (TVar (counter_var c))) (BTLeaf TCmpEq) (BTLeaf (TNum 0))
                (BTNode TGoto (BTLeaf (TNum (2*next_z))))
                (BTNode TGoto (BTLeaf (TNum (2*i+1))))) \/
      (l = 2*i+1 /\
       t = BTNode TDec (BTNode (TVar (counter_var c))
              (BTNode TSemi (BTNode TGoto (BTLeaf (TNum (2*next_nz)))))))
  | MHalt => l = 2*i /\ t = BTLeaf THalt
  end.
Proof.
  intros i instr l t Hin.
  destruct instr as [c next | c next_nz next_z |]; simpl in Hin.
  - destruct Hin as [H | []]. injection H; intros; subst. split; reflexivity.
  - destruct Hin as [H | [H | []]].
    + injection H; intros; subst. left. split; reflexivity.
    + injection H; intros; subst. right. split; reflexivity.
  - destruct Hin as [H | []]. injection H; intros; subst. split; reflexivity.
Qed.

(** Shape characterization for flat program entries *)
Lemma compile_instr_In_shapes : forall i instr l stmt,
  In (l, stmt) (compile_instr i instr) ->
  match instr with
  | MInc c next =>
      l = 2*i /\ stmt = SInc (counter_var c) (2*next)
  | MDec c next_nz next_z =>
      (l = 2*i /\
       stmt = SIf (EVar (counter_var c)) CmpEq (ENum 0%Z) (2*next_z) (2*i+1)) \/
      (l = 2*i+1 /\ stmt = SDec (counter_var c) (2*next_nz))
  | MHalt => l = 2*i /\ stmt = SHalt
  end.
Proof.
  intros i instr l stmt Hin.
  destruct instr as [c next | c next_nz next_z |]; simpl in Hin.
  - destruct Hin as [H | []]. injection H; intros; subst. split; reflexivity.
  - destruct Hin as [H | [H | []]].
    + injection H; intros; subst. left. split; reflexivity.
    + injection H; intros; subst. right. split; reflexivity.
  - destruct Hin as [H | []]. injection H; intros; subst. split; reflexivity.
Qed.

(** ** Formal bridge: bt_step <--> step *)

Theorem compile_btree_correct : forall mp l s l' s',
  bt_step (compile_btree mp) (l, s) (l', s') <->
  step (compile mp) (l, s) (l', s').
Proof.
  intros mp l s l' s'. split.

  (** Forward: bt_step --> step *)
  - intro Hbt.
    inversion Hbt as [? ? t ? ? Hfetch Heval]. subst.
    apply bt_fetch_gives_In in Hfetch.
    unfold compile_btree in Hfetch.
    apply compile_btree_aux_In_inv in Hfetch.
    destruct Hfetch as [i [instr [Hnth Hmem]]].
    rewrite Nat.add_0_l in Hmem.
    apply compile_instr_btree_In_shapes in Hmem.
    destruct instr as [c next | c next_nz next_z |].
    + (* MInc *)
      destruct Hmem as [Hl Ht]. subst l t.
      simpl in Heval. injection Heval; intros; subst.
      apply step_inc. apply fetch_compile_inc. exact Hnth.
    + (* MDec *)
      destruct Hmem as [[Hl Ht] | [Hl Ht]].
      * subst l t. unfold eval_tree in Heval.
        destruct (Z.eqb_spec (s (counter_var c)) 0%Z) as [Heq | Hne].
        -- injection Heval; intros; subst.
           eapply step_if_true. eapply fetch_compile_if. exact Hnth. simpl. exact Heq.
        -- injection Heval; intros; subst.
           eapply step_if_false. eapply fetch_compile_if. exact Hnth. simpl. exact Hne.
      * subst l t. simpl in Heval. injection Heval; intros; subst.
        apply step_dec. eapply fetch_compile_dec. exact Hnth.
    + (* MHalt: eval_tree returns None, contradiction *)
      destruct Hmem as [Hl Ht]. subst l t. simpl in Heval. discriminate.

  (** Backward: step --> bt_step.
      Use match goal per case to find the fetch hypothesis regardless of Coq's naming. *)
  - intro Hstep.
    inversion Hstep; subst.
    + (* step_inc *)
      match goal with Hf : fetch _ _ = Some _ |- _ =>
        apply fetch_gives_In in Hf; unfold compile in Hf;
        apply compile_aux_In_inv in Hf;
        destruct Hf as [? [instr [Hnth Hmem]]];
        rewrite Nat.add_0_l in Hmem;
        apply compile_instr_In_shapes in Hmem
      end.
      destruct instr as [c next | c next_nz next_z |].
      * destruct Hmem as [? Hstmt]. injection Hstmt; intros; subst.
        econstructor. apply bt_fetch_compile_btree_inc. exact Hnth. reflexivity.
      * destruct Hmem as [[? Hstmt] | [? Hstmt]]; discriminate.
      * destruct Hmem as [? Hstmt]. discriminate.
    + (* step_dec *)
      match goal with Hf : fetch _ _ = Some _ |- _ =>
        apply fetch_gives_In in Hf; unfold compile in Hf;
        apply compile_aux_In_inv in Hf;
        destruct Hf as [? [instr [Hnth Hmem]]];
        rewrite Nat.add_0_l in Hmem;
        apply compile_instr_In_shapes in Hmem
      end.
      destruct instr as [c next | c next_nz next_z |].
      * destruct Hmem as [? Hstmt]. discriminate.
      * destruct Hmem as [[? Hstmt] | [? Hstmt]].
        -- discriminate.
        -- injection Hstmt; intros; subst.
           econstructor. eapply bt_fetch_compile_btree_dec. exact Hnth. reflexivity.
      * destruct Hmem as [? Hstmt]. discriminate.
    + (* step_if_true: condition holds, result is true-branch label *)
      match goal with Hf : fetch _ _ = Some _ |- _ =>
        apply fetch_gives_In in Hf; unfold compile in Hf;
        apply compile_aux_In_inv in Hf;
        destruct Hf as [? [instr [Hnth Hmem]]];
        rewrite Nat.add_0_l in Hmem;
        apply compile_instr_In_shapes in Hmem
      end.
      destruct instr as [c next | c next_nz next_z |].
      * destruct Hmem as [? ?]. discriminate.
      * destruct Hmem as [[Hl Hstmt] | [Hl Hstmt]].
        -- (* MDec IF entry: injection grounds e1/e2/l', subst also eliminates l *)
           injection Hstmt; intros; subst.
           econstructor; [eapply bt_fetch_compile_btree_if; exact Hnth |].
           unfold eval_tree.
           match goal with He : eval_expr _ _ = eval_expr _ _ |- _ =>
             simpl in He; apply Z.eqb_eq in He; rewrite He
           end.
           reflexivity.
        -- discriminate.
      * destruct Hmem as [Hl Hstmt]. discriminate.
    + (* step_if_false: condition fails, result is false-branch label *)
      match goal with Hf : fetch _ _ = Some _ |- _ =>
        apply fetch_gives_In in Hf; unfold compile in Hf;
        apply compile_aux_In_inv in Hf;
        destruct Hf as [? [instr [Hnth Hmem]]];
        rewrite Nat.add_0_l in Hmem;
        apply compile_instr_In_shapes in Hmem
      end.
      destruct instr as [c next | c next_nz next_z |].
      * destruct Hmem as [Hl Hstmt]. discriminate.
      * destruct Hmem as [[Hl Hstmt] | [Hl Hstmt]].
        -- (* MDec IF entry: injection grounds e1/e2/l', subst also eliminates l *)
           injection Hstmt; intros; subst.
           econstructor; [eapply bt_fetch_compile_btree_if; exact Hnth |].
           unfold eval_tree.
           match goal with He : eval_expr _ _ <> eval_expr _ _ |- _ =>
             simpl in He; apply Z.eqb_neq in He; rewrite He
           end.
           reflexivity.
        -- discriminate.
      * destruct Hmem as [Hl Hstmt]. discriminate.
    + (* step_goto: impossible - no SGoto in compiled programs *)
      match goal with Hf : fetch _ _ = Some _ |- _ =>
        apply fetch_gives_In in Hf; unfold compile in Hf;
        apply compile_aux_In_inv in Hf;
        destruct Hf as [? [instr [Hnth Hmem]]];
        rewrite Nat.add_0_l in Hmem;
        apply compile_instr_In_shapes in Hmem
      end.
      destruct instr as [c next | c next_nz next_z |].
      * destruct Hmem as [? Hstmt]. discriminate.
      * destruct Hmem as [[? Hstmt] | [? Hstmt]]; discriminate.
      * destruct Hmem as [? Hstmt]. discriminate.
Qed.

(** ** BrickTree <--> physical token sequence consistency

    [eval_tokens] is the ground-truth physical model: it evaluates the flat
    token list that a daisy-chained brick row produces, matching exactly the
    four instruction shapes the physical hardware supports.

    [eval_tree_tokens_agree] proves that the mathematical tree model and the
    physical token model agree on every tree that the compiler produces —
    closing the gap the reviewer identified between "PBPL Turing-completeness"
    and "physical bricks Turing-completeness".

    (The theorem cannot be stated for ALL brick_trees because [flatten] is not
    injective: a [BTNode TIf child] can produce the same token list as a
    [BTIf], yet [eval_tree] returns [None] on the former while [eval_tokens]
    would return [Some].  Restricting to compiled trees avoids this.) *)

Definition eval_tokens (toks : list token) (s : store) : option (label * store) :=
  match toks with
  | [TInc; TVar v; TSemi; TGoto; TNum l] =>
      Some (l, update s v (s v + 1)%Z)
  | [TDec; TVar v; TSemi; TGoto; TNum l] =>
      Some (l, update s v (s v - 1)%Z)
  | [TIf; TVar v; TCmpEq; TNum 0; TSemi;
     TGoto; TNum lt; TIfSep;
     TGoto; TNum lf; TIfSep] =>
      if Z.eqb (s v) 0%Z then Some (lt, s) else Some (lf, s)
  | [THalt] => None
  | _ => None
  end.

(** For every instruction tree produced by [compile_instr_btree],
    [eval_tree] and [eval_tokens . flatten] agree. *)
Lemma eval_tree_tokens_agree : forall i instr s l t,
  In (l, t) (compile_instr_btree i instr) ->
  eval_tree t s = eval_tokens (flatten t) s.
Proof.
  intros i instr s l t Hin.
  destruct instr as [c next | c next_nz next_z |]; simpl in Hin.
  - destruct Hin as [H | []]. injection H; intros; subst t. reflexivity.
  - destruct Hin as [H | [H | []]].
    + injection H; intros; subst t. reflexivity.
    + injection H; intros; subst t. reflexivity.
  - destruct Hin as [H | []]. injection H; intros; subst t. reflexivity.
Qed.

(** Lift to the full compiled program. *)
Corollary compile_btree_tokens_agree : forall mp l t s,
  In (l, t) (compile_btree mp) ->
  eval_tree t s = eval_tokens (flatten t) s.
Proof.
  intros mp l t s Hin.
  unfold compile_btree in Hin.
  apply compile_btree_aux_In_inv in Hin.
  destruct Hin as [i [instr [Hnth Hmem]]].
  rewrite Nat.add_0_l in Hmem.
  eapply eval_tree_tokens_agree. exact Hmem.
Qed.
