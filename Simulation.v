(** * Simulation: Forward simulation proof + Turing-completeness *)

Require Import ZArith List Arith Lia.
Require Import PBPL.Util PBPL.BrickTree PBPL.PBPL PBPL.Minsky PBPL.Compile.
Import ListNotations.
Open Scope nat_scope.

(** ** Simulation relation *)

Definition match_config (mc : minsky_config) (pc : config) : Prop :=
  let '(i, c1, c2) := mc in
  let '(l, s) := pc in
  l = 2 * i /\
  s VarA = Z.of_nat c1 /\
  s VarB = Z.of_nat c2.

(** ** Forward simulation: one Minsky step → one or more PBPL steps *)

Theorem simulate_step :
  forall (mp : minsky_program) (mc1 mc2 : minsky_config),
    minsky_step mp mc1 mc2 ->
    forall pc1, match_config mc1 pc1 ->
    exists pc2,
      star (step (compile mp)) pc1 pc2 /\
      match_config mc2 pc2.
Proof.
  intros mp mc1 mc2 Hmstep pc1 Hmatch.
  destruct pc1 as [l s].
  inversion Hmstep; subst.

  (* Case 1: INC C1 *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (fetch_compile_inc mp _ _ _ H) as Hfetch.
    simpl in Hfetch.
    exists (2 * next, update s VarA (s VarA + 1)%Z).
    split.
    + apply star_one. econstructor. exact Hfetch.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_eq. rewrite Ha. lia.
      * rewrite update_neq by discriminate. exact Hb.

  (* Case 2: INC C2 *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (fetch_compile_inc mp _ _ _ H) as Hfetch.
    simpl in Hfetch.
    exists (2 * next, update s VarB (s VarB + 1)%Z).
    split.
    + apply star_one. econstructor. exact Hfetch.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_neq by discriminate. exact Ha.
      * rewrite update_eq. rewrite Hb. lia.

  (* Case 3: DEC C1 nonzero *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (fetch_compile_if mp _ _ _ _ H) as Hfetch_if.
    pose proof (fetch_compile_dec mp _ _ _ _ H) as Hfetch_dec.
    simpl in Hfetch_if. simpl in Hfetch_dec.
    exists (2 * next_nz, update s VarA (s VarA - 1)%Z).
    split.
    + eapply star_step.
      * eapply step_if_false.
        -- exact Hfetch_if.
        -- simpl. rewrite Ha. lia.
      * eapply star_step.
        -- eapply step_dec. exact Hfetch_dec.
        -- apply star_refl.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_eq. rewrite Ha. lia.
      * rewrite update_neq by discriminate. exact Hb.

  (* Case 4: DEC C1 zero *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (fetch_compile_if mp _ _ _ _ H) as Hfetch_if.
    simpl in Hfetch_if.
    exists (2 * next_z, s).
    split.
    + eapply star_step.
      * eapply step_if_true.
        -- exact Hfetch_if.
        -- simpl. rewrite Ha. reflexivity.
      * apply star_refl.
    + unfold match_config. split; [lia|]. split; assumption.

  (* Case 5: DEC C2 nonzero *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (fetch_compile_if mp _ _ _ _ H) as Hfetch_if.
    pose proof (fetch_compile_dec mp _ _ _ _ H) as Hfetch_dec.
    simpl in Hfetch_if. simpl in Hfetch_dec.
    exists (2 * next_nz, update s VarB (s VarB - 1)%Z).
    split.
    + eapply star_step.
      * eapply step_if_false.
        -- exact Hfetch_if.
        -- simpl. rewrite Hb. lia.
      * eapply star_step.
        -- eapply step_dec. exact Hfetch_dec.
        -- apply star_refl.
    + unfold match_config. split; [lia|]. split.
      * rewrite update_neq by discriminate. exact Ha.
      * rewrite update_eq. rewrite Hb. lia.

  (* Case 6: DEC C2 zero *)
  - destruct Hmatch as [Hl [Ha Hb]]. subst l.
    pose proof (fetch_compile_if mp _ _ _ _ H) as Hfetch_if.
    simpl in Hfetch_if.
    exists (2 * next_z, s).
    split.
    + eapply star_step.
      * eapply step_if_true.
        -- exact Hfetch_if.
        -- simpl. rewrite Hb. reflexivity.
      * apply star_refl.
    + unfold match_config. split; [lia|]. split; assumption.
Qed.

(** ** Multi-step simulation *)

Theorem simulate_star :
  forall (mp : minsky_program) (mc1 mc2 : minsky_config),
    star (minsky_step mp) mc1 mc2 ->
    forall pc1, match_config mc1 pc1 ->
    exists pc2,
      star (step (compile mp)) pc1 pc2 /\
      match_config mc2 pc2.
Proof.
  intros mp mc1 mc2 Hstar.
  induction Hstar; intros.
  - exists pc1. split. constructor. assumption.
  - destruct (simulate_step mp x y H pc1 H0) as [pc_mid [Hsteps Hmid]].
    destruct (IHHstar pc_mid Hmid) as [pc2 [Hsteps2 Hfinal]].
    exists pc2. split.
    + eapply star_trans; eassumption.
    + exact Hfinal.
Qed.

(** ** Top-level Turing-completeness theorem *)

Theorem pbpl_turing_complete :
  forall (mp : minsky_program),
    wf_tree (compile_tree mp) /\
    (forall mc1 mc2,
      minsky_step mp mc1 mc2 ->
      forall pc1, match_config mc1 pc1 ->
      exists pc2,
        star (step (compile mp)) pc1 pc2 /\
        match_config mc2 pc2).
Proof.
  intros. split.
  - apply compile_wf.
  - intros. eapply simulate_step; eassumption.
Qed.
