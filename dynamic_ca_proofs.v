Require Import Reals.
Require Import Rpower.
Require Import Rtrigo.
Require Import List.
Import ListNotations.
Open Scope R_scope.

(* Type definitions *)
Record Interaction := mkInteraction {
  probability : R;  (* Attack probability p ∈ [0,1] *)
  effectiveness : R;  (* Defense effectiveness E ∈ [0,1] *)
  timestamp : R;  (* Time of interaction *)
  decay_time : R  (* Calculated decay period *)
}.

(* Parameters *)
Parameter k1 : R.  (* Linear scaling factor *)
Parameter k2 : R.  (* Exponential scaling factor *)
Parameter CA0 : R.  (* Initial CA value *)
Parameter T_base : R.  (* Base decay period (365 days) *)
Parameter alpha : R.  (* Extension scaling factor *)
Parameter beta : R.  (* Punishment severity exponent *)
Parameter gamma : R.  (* Reset factor *)
Parameter p_threshold : R.  (* Threshold for triggering resets *)

(* Axioms for parameters *)
Axiom k1_bounds : 0.5 <= k1 <= 2.
Axiom k2_bounds : 1.5 <= k2 <= 2.5.
Axiom CA0_positive : CA0 > 0.
Axiom T_base_value : T_base = 365.
Axiom alpha_bounds : 0.5 <= alpha <= 2.
Axiom beta_bounds : 2 <= beta <= 3.
Axiom gamma_bounds : 0 < gamma <= 1.
Axiom p_threshold_bounds : 0 < p_threshold <= 1.

(* Growth function: g(p, E) = 1 + k₁ × p × (2-E)^k₂ *)
Definition growth_function (p E : R) : R :=
  1 + k1 * p * Rpower (2 - E) k2.

(* Punishment extension function: f(p) = α × p^β × T_base *)
Definition punishment_extension (p : R) : R :=
  alpha * Rpower p beta * T_base.

(* Decay timer function: T_decay(i) = T_base + f(p_i) *)
Definition decay_timer (p : R) : R :=
  T_base + punishment_extension p.

(* Check if interaction is still active *)
Definition is_active (i : Interaction) (current_time : R) : bool :=
  Rle_dec (current_time - timestamp i) (decay_time i).

(* Filter active interactions *)
Definition active_interactions (interactions : list Interaction) (current_time : R) : list Interaction :=
  filter (fun i => is_active i current_time) interactions.

(* Calculate product of growth functions for active interactions *)
Fixpoint product_growth (interactions : list Interaction) : R :=
  match interactions with
  | [] => 1
  | i :: rest => growth_function (probability i) (effectiveness i) * product_growth rest
  end.

(* Main CA formula: CA(t) = CA₀ × exp(∏ᵢ∈active g(pᵢ, Eᵢ)) *)
Definition CA_value (interactions : list Interaction) (current_time : R) : R :=
  CA0 * exp (product_growth (active_interactions interactions current_time)).

(* Timer reset mechanism *)
Definition reset_timer (old_remaining : R) (p_new : R) : R :=
  Rmax old_remaining (gamma * punishment_extension p_new).

(* Lemmas and Theorems *)

(* Lemma 1: Probability and effectiveness bounds preserve validity *)
Lemma valid_bounds : forall p E,
  0 <= p <= 1 -> 0 <= E <= 1 -> 0 < 2 - E <= 2.
Proof.
  intros p E Hp HE.
  split.
  - apply Rlt_0_minus. lra.
  - lra.
Qed.

(* Lemma 2: Growth function is always greater than 1 *)
Lemma growth_function_gt_1 : forall p E,
  0 <= p <= 1 -> 0 <= E <= 1 -> growth_function p E >= 1.
Proof.
  intros p E Hp HE.
  unfold growth_function.
  assert (H1: 0 <= k1 * p * Rpower (2 - E) k2).
  {
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      + left. apply Rlt_le_trans with 0.5; [lra | apply k1_bounds].
      + apply Hp.
    - apply Rlt_le. apply exp_pos.
  }
  lra.
Qed.

(* Lemma 3: CA value is always positive *)
Lemma CA_value_positive : forall interactions t,
  (forall i, In i interactions -> 0 <= probability i <= 1 /\ 0 <= effectiveness i <= 1) ->
  CA_value interactions t > 0.
Proof.
  intros interactions t H.
  unfold CA_value.
  apply Rmult_gt_0_compat.
  - exact CA0_positive.
  - apply exp_pos.
Qed.

(* Lemma 4: Higher attack probability increases growth *)
Lemma higher_p_higher_growth : forall p1 p2 E,
  0 <= p1 < p2 -> p2 <= 1 -> 0 <= E <= 1 ->
  growth_function p1 E < growth_function p2 E.
Proof.
  intros p1 p2 E Hp12 Hp2 HE.
  unfold growth_function.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_r.
  - apply Rlt_0_le_trans with (Rpower 0.5 k2).
    + apply exp_pos.
    + apply Rle_pow.
      * lra.
      * apply valid_bounds; assumption.
      * apply k2_bounds.
  - apply Rmult_lt_compat_l.
    + apply Rlt_le_trans with 0.5; [lra | apply k1_bounds].
    + exact Hp12.
Qed.

(* Lemma 5: Weaker defense (lower E) increases growth *)
Lemma weaker_defense_higher_growth : forall p E1 E2,
  0 < p <= 1 -> 0 <= E1 < E2 -> E2 <= 1 ->
  growth_function p E2 < growth_function p E1.
Proof.
  intros p E1 E2 Hp HE12 HE2.
  unfold growth_function.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_l.
  - apply Rmult_lt_0_compat.
    + apply Rlt_le_trans with 0.5; [lra | apply k1_bounds].
    + exact Hp.
  - apply Rlt_pow.
    + split.
      * apply valid_bounds; [apply Hp | split; [apply HE12 | apply Rlt_le; apply HE12]].
      * apply valid_bounds; [apply Hp | split; [lra | exact HE2]].
    + lra.
    + apply Rlt_le_trans with 1.5; [lra | apply k2_bounds].
Qed.

(* Lemma 6: Punishment extension increases with probability *)
Lemma punishment_increases_with_p : forall p1 p2,
  0 <= p1 < p2 -> p2 <= 1 ->
  punishment_extension p1 < punishment_extension p2.
Proof.
  intros p1 p2 Hp12 Hp2.
  unfold punishment_extension.
  apply Rmult_lt_compat_r.
  - rewrite T_base_value. lra.
  - apply Rmult_lt_compat_l.
    + apply Rlt_le_trans with 0.5; [lra | apply alpha_bounds].
    + apply Rlt_pow.
      * exact Hp12.
      * apply Rle_trans with 2; [lra | apply beta_bounds].
Qed.

(* Theorem 1: Decay timer increases with attack probability *)
Theorem decay_timer_monotonic : forall p1 p2,
  0 <= p1 < p2 -> p2 <= 1 ->
  decay_timer p1 < decay_timer p2.
Proof.
  intros p1 p2 Hp12 Hp2.
  unfold decay_timer.
  apply Rplus_lt_compat_l.
  apply punishment_increases_with_p; assumption.
Qed.

(* Theorem 2: Timer reset preserves or increases remaining time *)
Theorem timer_reset_preserves_or_increases : forall old_remaining p_new,
  0 <= p_new <= 1 -> p_new > p_threshold ->
  old_remaining <= reset_timer old_remaining p_new.
Proof.
  intros old_remaining p_new Hp_bounds Hp_threshold.
  unfold reset_timer.
  apply Rmax_l.
Qed.

(* Theorem 3: Clean users have minimal punishment *)
Theorem clean_user_minimal_punishment : forall p,
  0 <= p <= 0.2 ->
  decay_timer p <= T_base + 0.2 * alpha * T_base.
Proof.
  intros p Hp.
  unfold decay_timer, punishment_extension.
  assert (Rpower p beta <= Rpower 0.2 beta).
  {
    apply Rle_pow.
    - split; [apply Hp | apply Hp].
    - split; [lra | lra].
    - apply beta_bounds.
  }
  apply Rplus_le_compat_l.
  apply Rmult_le_compat.
  - apply Rmult_le_pos.
    + apply Rlt_le. apply Rlt_le_trans with 0.5; [lra | apply alpha_bounds].
    + apply Rlt_le. apply exp_pos.
  - apply Rlt_le. rewrite T_base_value. lra.
  - apply Rmult_le_compat_l.
    + apply Rlt_le. apply Rlt_le_trans with 0.5; [lra | apply alpha_bounds].
    + exact H.
  - apply Rle_refl.
Qed.

(* Theorem 4: Suspicious users have significant punishment *)
Theorem suspicious_user_significant_punishment : forall p,
  0.8 <= p <= 1 ->
  decay_timer p >= T_base + 0.8^2 * alpha * T_base.
Proof.
  intros p Hp.
  unfold decay_timer, punishment_extension.
  assert (Rpower p beta >= Rpower 0.8 beta).
  {
    apply Rle_pow.
    - split; [lra | apply Hp].
    - split; [apply Hp | exact (proj2 Hp)].
    - apply beta_bounds.
  }
  apply Rplus_le_compat_l.
  assert (beta >= 2) by apply beta_bounds.
  assert (Rpower 0.8 beta >= Rpower 0.8 2).
  {
    apply Rle_pow.
    - split; lra.
    - split; lra.
    - exact H0.
  }
  apply Rle_trans with (alpha * Rpower 0.8 2 * T_base).
  - unfold Rpower. rewrite Rmult_comm. 
    apply Rmult_le_compat_r.
    + rewrite T_base_value. lra.
    + apply Rmult_le_compat_l.
      * apply Rlt_le. apply Rlt_le_trans with 0.5; [lra | apply alpha_bounds].
      * simpl. lra.
  - apply Rmult_le_compat.
    + apply Rmult_le_pos.
      * apply Rlt_le. apply Rlt_le_trans with 0.5; [lra | apply alpha_bounds].
      * apply Rlt_le. apply exp_pos.
    + apply Rlt_le. rewrite T_base_value. lra.
    + apply Rmult_le_compat_l.
      * apply Rlt_le. apply Rlt_le_trans with 0.5; [lra | apply alpha_bounds].
      * apply Rle_trans with (Rpower 0.8 beta); assumption.
    + apply Rle_refl.
Qed.