Require Import Reals.
Require Import Rpower.
Require Import Reals.Ranalysis.
Require Import Reals.Rdefinitions.
Require Import QArith.
Require Import QArith.Qreals.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Reals.Rbasic_fun.
Require Import List.
Require Import Psatz.
Import Coq.Reals.Rbasic_fun.
Import Coq.QArith.Qreals.
Import ListNotations.
Open Scope Q_scope.
Open Scope R_scope.

(** ** Core Formula:
    CA(t) = min(CA_max(t), CA₀ × exp(∏ᵢ∈active g(pᵢ, Eᵢ)) × Π_nash(G, S, M))
    
    Where:
    - CA_max(t) = min(System_Score(t), Economic_Score(u,t), Temporal_Score(u,t), Regulatory_Score)
    - g(p, E) = 1 + k₁ × p × (2-E)^k₂
    - T_decay(i) = T_base + α × p^β × T_base
    - Π_nash = w₁·π_eq + w₂·π_comp + w₃·π_rep + w₄·π_bayes + w₅·π_signal
*)

(* Custom bounded type for probabilities and effectiveness *)
Record BoundedQ := mkBounded {
  value : Q;
  bounds : (0 <= value <= 1)%Q
}.

(* Type definitions *)
Record Interaction := mkInteraction {
  probability : BoundedQ;     (* Attack probability p ∈ [0,1] *)
  effectiveness : BoundedQ;   (* Defense effectiveness E ∈ [0,1] *)
  timestamp : R;              (* Time of interaction *)
  decay_time : R              (* Calculated decay period *)
}.

(* Parameters - use Q for bounded values, R for unbounded *)
Parameter k1 : Q.           (* Linear scaling factor *)
Parameter k2 : Q.           (* Exponential scaling factor *)
Parameter CA0 : Q.          (* Initial CA value *)
Parameter T_base : N.       (* Base decay period (365 days) *)
Parameter alpha : Q.        (* Extension scaling factor *)
Parameter beta : Q.         (* Punishment severity exponent *)
Parameter gamma : Q.        (* Reset factor *)
Parameter p_threshold : BoundedQ.  (* Threshold for triggering resets *)

(* Axioms for parameters *)
Axiom k1_bounds : (Q2R(1#2)) <= Q2R k1 <= (Q2R 2).
Axiom k2_bounds : (Q2R(3#2)) <= Q2R k2 <= (Q2R (5#2)).
Axiom CA0_positive : (Q2R 0) < Q2R CA0.
Axiom T_base_value : T_base = 365%N.
Axiom alpha_bounds : (Q2R (1#2)) <= Q2R alpha <= (Q2R 2).
Axiom beta_bounds : (Q2R 2) <= Q2R beta <= (Q2R 3).
Axiom gamma_bounds : (Q2R 0) < Q2R gamma <= (Q2R 1).
Axiom Rpower_0_pos : forall y : R, (0 < y)%R -> Rpower 0 y = 0%R.

(* Q2R conversion axioms *)
Axiom Q2R_0 : Q2R 0 = 0%R.
Axiom Q2R_1 : Q2R 1 = 1%R.

Axiom Rpower_lt_nonneg : forall x y r : R,
  (0 <= x)%R -> (x < y)%R -> (0 < r)%R -> (Rpower x r < Rpower y r)%R.

Axiom Rpower_le_nonneg : forall x y r : R,
  (0 <= x)%R -> (x <= y)%R -> (0 <= r)%R -> (Rpower x r <= Rpower y r)%R.
  
  
Axiom Rle_Rpower_base_lt_1 : forall e n m : R,
  0 < e -> e < 1 -> n <= m -> Rpower e m <= Rpower e n.
(* Basic Q inequalities *)
Lemma Qle_0_1 : (0 <= 1)%Q.
Proof. lra. Qed.

Lemma Qle_0_half : (0 <= 1#2)%Q.  
Proof. lra. Qed.

Lemma Qle_half_1 : (1#2 <= 1)%Q.
Proof. lra. Qed.

(* Helper lemma for positive Q2R *)
Lemma Q2R_pos : forall q : Q, (0 < q)%Q -> (0 < Q2R q)%R.
Proof.
  intros q Hq.
  rewrite <- Q2R_0.
  apply Qreals.Qlt_Rlt.
  exact Hq.
Qed.

(* Helper lemma for Q2R inequality *)
Lemma Q2R_lt : forall p q : Q, (p < q)%Q -> (Q2R p < Q2R q)%R.
Proof.
  intros. apply Qreals.Qlt_Rlt. assumption.
Qed.

(* Conversion function - use the standard library Q2R *)
Definition bounded_to_R (b : BoundedQ) : R := Q2R (value b).

(* Growth function: g(p, E) = 1 + k₁ × p × (2-E)^k₂ *)
Definition growth_function (p E : BoundedQ) : R :=
  1 + Q2R k1 * bounded_to_R p * Rpower (2 - bounded_to_R E) (Q2R k2).

(* Punishment extension function: f(p) = α × p^β × T_base *)
Definition punishment_extension (p : BoundedQ) : R :=
  Q2R alpha * Rpower (bounded_to_R p) (Q2R beta) * INR (N.to_nat T_base).

(* Decay timer function: T_decay(i) = T_base + f(p_i) *)
Definition decay_timer (p : BoundedQ) : R :=
  INR (N.to_nat T_base) + punishment_extension p.

(* Check if interaction is still active *)
Definition is_active (i : Interaction) (current_time : R) : bool :=
  if Rle_dec (current_time - timestamp i) (decay_time i) then true else false.

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
  Q2R CA0 * exp (product_growth (active_interactions interactions current_time)).

(* Timer reset mechanism *)
Definition reset_timer (old_remaining : R) (p_new : BoundedQ) : R :=
  Rmax old_remaining (Q2R gamma * punishment_extension p_new).

(* Helper lemmas for bounded values *)
Local Open Scope R_scope.
Lemma bounded_to_R_bounds : forall b : BoundedQ,
  (0:R) <= bounded_to_R b <= (1:R).
Proof.
  intros b.
  unfold bounded_to_R.
  destruct b as [v [H1 H2]].
  simpl.
  split.
  - rewrite <- Q2R_0. apply Qreals.Qle_Rle. exact H1.
  - rewrite <- Q2R_1. apply Qreals.Qle_Rle. exact H2.
Qed.

Lemma Q2R_eq : forall q1 q2 : Q, q1 = q2 -> Q2R q1 = Q2R q2.
Proof. intros. f_equal. assumption. Qed.

(* Lemma 1: Probability and effectiveness bounds preserve validity *)
Lemma valid_bounds : forall p E : BoundedQ,
  0 < 2 - bounded_to_R E <= 2.
Proof.
  intros p E.
  destruct (bounded_to_R_bounds E) as [HE1 HE2].
  split; lra.
Qed.

(* Lemma 2: Growth function is always greater than 1 *)
Lemma growth_function_gt_1 : forall p E : BoundedQ,
  growth_function p E >= 1.
Proof.
  intros p E.
  unfold growth_function.
  assert (H1: 0 <= Q2R k1 * bounded_to_R p * Rpower (2 - bounded_to_R E) (Q2R k2)).
  {
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      + left.
        (* The goal here is: 0 < Q2R k1 *)
        apply Rlt_le_trans with (Q2R (1#2)).
        * unfold Q2R. simpl. lra.
        * (* Now, the problem. (proj1 k1_bounds) gives (Q2R (1#2) <= Q2R k1). *)
          (* No need for Qle_Rle here, as k1_bounds directly gives an R inequality *)
          apply (proj1 k1_bounds).
      + apply (proj1 (bounded_to_R_bounds p)).
    - apply Rlt_le. apply exp_pos.
  }
  lra.
Qed.

(* Lemma 3: CA value is always positive *)
Lemma CA_value_positive : forall interactions t,
  CA_value interactions t > 0.
Proof.
  intros interactions t.
  unfold CA_value.
  apply Rmult_gt_0_compat.
  apply Rlt_gt.
  rewrite <- Q2R_0.
  exact CA0_positive.
  - apply exp_pos.
Qed.

(* Constructor for bounded values with proof obligation *)
Definition mkBoundedQ (q : Q) (H : (0 <= q <= 1)%Q) : BoundedQ :=
  mkBounded q H.

(* Example usage: *)
Definition zero_prob : BoundedQ := 
  mkBoundedQ 0 (conj (Qle_refl 0) Qle_0_1).

Definition half_prob : BoundedQ :=
  mkBoundedQ (1#2) (conj Qle_0_half Qle_half_1).

(* Lemma 4: Higher attack probability increases growth *)
Lemma higher_p_higher_growth : forall p1 p2 E : BoundedQ,
  (value p1 < value p2)%Q ->
  growth_function p1 E < growth_function p2 E.
Proof.
  intros p1 p2 E Hp_lt.
  unfold growth_function.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_r.
  - apply exp_pos.
  - apply Rmult_lt_compat_l.
    + apply Rlt_le_trans with (Q2R (1#2)).
      * unfold Q2R. simpl. lra.
      * (* FIX HERE: Remove Qle_Rle. k1_bounds already provides an R inequality. *)
        apply (proj1 k1_bounds).
    + unfold bounded_to_R. simpl.
      apply Qlt_Rlt. exact Hp_lt.
Qed.

(* Lemma 5: Weaker defense (lower E) increases growth *)
Lemma weaker_defense_higher_growth : forall p E1 E2 : BoundedQ,
  (0 < value p)%Q ->
  (value E1 < value E2)%Q ->
  growth_function p E2 < growth_function p E1.
Proof.
  intros p E1 E2 Hp_pos HE_lt.
  unfold growth_function.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_l.
  - apply Rmult_lt_0_compat.
    + apply Rlt_le_trans with (Q2R (1#2)).
      * unfold Q2R. simpl. lra.
      * (* FIX HERE: Remove Qle_Rle *)
        apply (proj1 k1_bounds).
    + unfold bounded_to_R. simpl.
      apply Q2R_pos. exact Hp_pos.
  - apply Rlt_Rpower_l.
    + apply Rlt_le_trans with (Q2R (3#2)).
      * unfold Q2R. simpl. lra.
      * (* FIX HERE: Remove Qle_Rle *)
        apply (proj1 k2_bounds).
    + split.
      * destruct (bounded_to_R_bounds E2). lra.
      * unfold bounded_to_R. simpl.
        assert (Q2R (value E1) < Q2R (value E2)) by (apply Q2R_lt; exact HE_lt).
        lra.
Qed.

(* Theorem 1: Decay timer increases with attack probability *)
Theorem decay_timer_monotonic : forall p1 p2 : BoundedQ,
  (value p1 < value p2)%Q ->
  decay_timer p1 < decay_timer p2.
Proof.
  intros p1 p2 Hp_lt.
  unfold decay_timer, punishment_extension.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_r.
  - apply lt_0_INR.
    rewrite T_base_value.
    unfold N.to_nat. simpl. lia.
  - apply Rmult_lt_compat_l.
    + apply Rlt_le_trans with (Q2R (1#2)).
      * unfold Q2R. simpl. lra.
      * apply (proj1 alpha_bounds).
    + apply Rpower_lt_nonneg.
      * apply (proj1 (bounded_to_R_bounds p1)).
      * unfold bounded_to_R. simpl. apply Qlt_Rlt. exact Hp_lt.
      * apply Rlt_le_trans with (Q2R 2). 
        -- unfold Q2R. simpl. lra.
        -- apply (proj1 beta_bounds).
Qed.



(* Theorem 2: Timer reset preserves or increases remaining time *)
Theorem timer_reset_preserves_or_increases : forall old_remaining p_new,
  (value p_threshold < value p_new)%Q ->
  old_remaining <= reset_timer old_remaining p_new.
Proof.
  intros old_remaining p_new Hp_threshold.
  unfold reset_timer.
  apply Rmax_l.
Qed.

(* Helper to create bounded values for specific probabilities *)
Definition make_prob_02 : BoundedQ.
  refine (mkBoundedQ (2#10) _).
  split; compute; discriminate.
Defined.

Definition make_prob_08 : BoundedQ.
  refine (mkBoundedQ (8#10) _).
  split; compute; discriminate.
Defined.

Lemma Rpower_le_exp_le : forall (x y : R),
  (0 < x)%R -> (x <= 1)%R -> (1 <= y)%R -> (Rpower x y <= x)%R.
Proof.
  intros x y Hx0 Hx1 Hy1.
  
  (* Prove ln x <= 0 *)
  assert (Hln_x_le_0 : ln x <= 0). {
    (* Check if x = 1 or x < 1 *)
    destruct (Req_dec x 1) as [Hx_eq_1 | Hx_ne_1].
    - (* Case: x = 1 *)
      rewrite Hx_eq_1.
      rewrite ln_1.  (* Assuming ln_1 exists - check with: Search ln 1. *)
      lra.
    - (* Case: x < 1 (since x <= 1 and x ≠ 1) *)
      assert (Hx_lt_1 : x < 1).
      {
        lra. (* x <= 1 and x ≠ 1 implies x < 1 *)
      }
      rewrite <- ln_1.  (* ln 1 = 0 *)
      apply Rlt_le.
      apply ln_increasing.  (* This is available from your search *)
      + exact Hx0.      (* 0 < x *)
      + exact Hx_lt_1.  (* x < 1 *)
  }
  
  (* Now prove y * ln x <= ln x *)
  assert (H_mult_le : y * ln x <= ln x). {
    rewrite Rmult_comm.
    rewrite <- (Rmult_1_r (ln x)) at 2.
    apply Rmult_le_compat_neg_l.
    - exact Hln_x_le_0.
    - exact Hy1.
  }

  
(* Final step: prove Rpower x y <= x *)
unfold Rpower.
(* Goal: exp (y * ln x) <= x *)

(* First, let's establish that x = exp (ln x) *)
assert (H_x_eq : x = exp (ln x)).
{ 
  symmetry. 
  apply exp_ln. 
  exact Hx0. 
}

(* Now rewrite only on the right side *)
rewrite H_x_eq.
(* Goal should now be: exp (y * ln x) <= exp (ln x) *)

destruct (Rlt_dec (y * ln x) (ln x)) as [H_lt | H_not_lt].
- (* Case: y * ln x < ln x *)
   assert (H_simp : ln (exp (ln x)) = ln x).
  { apply ln_exp. }
  rewrite H_simp.
  Show.
  apply Rlt_le.
  apply exp_increasing.
  exact H_lt.
- (* Case: not (y * ln x < ln x) *)
  assert (H_eq : y * ln x = ln x).
  { 
    apply Rle_antisym.
    + exact H_mult_le.
    + apply Rnot_lt_le. exact H_not_lt.
  }
 assert (H_simp : ln (exp (ln x)) = ln x).
  { apply ln_exp. }
  rewrite H_simp.
  (* Now rewrite with H_eq *)
  rewrite H_eq.
  apply Rle_refl.
Qed.

Lemma beta_positive : (0 < beta)%Q.
Proof.
  apply Qlt_le_trans with (2)%Q.
  - reflexivity. (* 0 < 2 *)
  - apply Rle_Qle.
    apply (proj1 beta_bounds). (* 2 <= beta *)
Qed.

(* Theorem 3: Clean users have minimal punishment *)
Theorem clean_user_minimal_punishment : forall p : BoundedQ,
  (value p <= (2#10))%Q ->
  decay_timer p <= INR (N.to_nat T_base) + Q2R (2#10) * Q2R alpha * INR (N.to_nat T_base).
Proof.
  intros p Hp.
  unfold decay_timer, punishment_extension.
  (* Goal: INR (N.to_nat T_base) + Q2R alpha * Rpower (bounded_to_R p) (Q2R beta) * INR (N.to_nat T_base) <= INR (N.to_nat T_base) + Q2R (2#10) * Q2R alpha * INR (N.to_nat T_base) *)
  apply Rplus_le_compat_l.
  (* Goal: Q2R alpha * Rpower (bounded_to_R p) (Q2R beta) * INR (N.to_nat T_base) <= Q2R (2#10) * Q2R alpha * INR (N.to_nat T_base) *)

  (* First, prove the inequality for the Rpower term: bounded_to_R p <= Q2R (2#10) *)
  assert (H_val_le_02 : bounded_to_R p <= Q2R (2#10)).
  { unfold bounded_to_R. apply Qle_Rle. exact Hp. }

  (* Next, prove Rpower (bounded_to_R p) (Q2R beta) <= Rpower (Q2R (2#10)) (Q2R beta) *)
  assert (H_power_le : Rpower (bounded_to_R p) (Q2R beta) <= Rpower (Q2R (2#10)) (Q2R beta)).
  {
    apply Rpower_le_nonneg.
    - apply (proj1 (bounded_to_R_bounds p)). (* 0 <= bounded_to_R p *)
    - exact H_val_le_02. (* bounded_to_R p <= Q2R (2#10) *)
    - apply Rlt_le. apply Q2R_pos.
      exact beta_positive. (* 0 < beta (since beta >= 2) *)
  }

  (* Second, prove the key property: Rpower (Q2R (2#10)) (Q2R beta) <= Q2R (2#10) *)
  assert (H_beta_property : Rpower (Q2R (2#10)) (Q2R beta) <= Q2R (2#10)).
  {
    apply Rpower_le_exp_le.
    - unfold Q2R. simpl. lra. (* 0 < 0.2 *)
    - unfold Q2R. simpl. lra. (* 0.2 <= 1 *)
    - (* Need to prove: 1 <= Q2R beta *)
      apply Rle_trans with (Q2R 2).
      + (* First prove: 1 <= Q2R 2 *)
        rewrite <- Q2R_1.  (* Convert 1 to Q2R 1 *)
        apply Qle_Rle.
        lra.  (* Use lra instead of reflexivity for 1 <= 2 in Q *)
      + (* Then prove: Q2R 2 <= Q2R beta *)
        apply Qle_Rle.
        apply Rle_Qle.
        exact (proj1 beta_bounds).  (* 2 <= beta *)
  }

  (* Now combine H_power_le and H_beta_property using Rle_trans *)
  assert (H_combined_power : Rpower (bounded_to_R p) (Q2R beta) <= Q2R (2#10)).
  { apply Rle_trans with (Rpower (Q2R (2#10)) (Q2R beta)).
    - exact H_power_le.
    - exact H_beta_property.
  }

  (* THIS IS THE FINAL BLOCK TO PROVE THE MAIN GOAL *)
  apply Rmult_le_compat_r. (* Apply with INR (N.to_nat T_base) as the common multiplier *)
  - (* Proof that INR (N.to_nat T_base) >= 0 *)
    apply Rlt_le.
    apply lt_0_INR. (* N.to_nat T_base must be > 0 *)
    rewrite T_base_value. (* Replace N.to_nat T_base with 200 *)
    simpl. (* Simplify 200 > 0 *)
    lia.
  - (* Goal after Rmult_le_compat_r:
       Q2R alpha * Rpower (bounded_to_R p) (Q2R beta) <= 0.2 * Q2R alpha
    *)
    (* At this point, we need to show: (Q2R alpha) * (Rpower ...) <= (0.2) * (Q2R alpha)
       We have:
       H_combined_power : Rpower (bounded_to_R p) (Q2R beta) <= 0.2
       And we know from alpha_bounds that Q2R alpha is positive.
    *)

    (* Provide the necessary hypotheses to lra *)
    assert (H_alpha_pos : (0 < Q2R alpha)%R).
    {
      apply Q2R_pos. (* This reduces the goal to (0 < alpha)%Q. Now we are in Q_scope for alpha. *)
      
      (* Bring the lower bound of alpha into the context *)
      destruct alpha_bounds as [H_alpha_lower_bound H_alpha_upper_bound].
      apply Qlt_le_trans with (1#2)%Q.
      unfold Qlt. simpl. reflexivity.
      (* Now you have H_alpha_lower_bound : (1#2 <= alpha)%Q in your hypotheses *)
      
      (* At this point, the goal is (0 < alpha)%Q.
         We know 0 < 1#2 and 1#2 <= alpha.
         lra can easily deduce 0 < alpha from these. *)
      apply Rle_Qle.
      exact H_alpha_lower_bound.
    }
    rewrite (Rmult_comm (Q2R (2#10)) (Q2R alpha)).
    apply Rmult_le_compat_l.
    apply Rlt_le.
    exact H_alpha_pos.
    exact H_combined_power.
  Qed.

(* Theorem 4: Suspicious users have more punishment than clean users *)
Theorem suspicious_user_more_punishment : forall p1 p2 : BoundedQ,
  (value p1 <= (2#10))%Q ->
  ((8#10) <= value p2)%Q ->
  decay_timer p1 < decay_timer p2.
Proof.
  intros p1 p2 Hp1 Hp2.
  (* We'll show that decay_timer is monotonic in probability *)
  (* Since value p1 <= 0.2 < 0.8 <= value p2, we have value p1 < value p2 *)
  assert (H_lt : (value p1 < value p2)%Q).
  {
    apply Qle_lt_trans with (2#10).
    - exact Hp1.
    - apply Qlt_le_trans with (8#10).
      + reflexivity. (* 0.2 < 0.8 *)
      + exact Hp2.
  }
  (* Now use the monotonicity theorem *)
  apply decay_timer_monotonic.
  exact H_lt.
Qed.
