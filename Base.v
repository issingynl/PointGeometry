Require Export Reals.
Open Scope R_scope.

Lemma Rmult_1_r' : forall r, 1 * r = r.
Proof.
  intros; ring.
Qed.

Lemma Rmult_2_r : forall r, 2 * r = r + r.
Proof.
  intros; ring.
Qed.

Lemma Rmult_3_r : forall r, 3 * r = r + r + r.
Proof.
  intros; ring.
Qed.

Lemma Rmult_opp_r : forall r, -1 * r = - r.
Proof.
  intros; ring.
Qed.

Lemma rplus_minus_tran : forall r r1, r + (- r1) = r - r1.
Proof.
  intros; ring.
Qed.

Lemma rplus_minus_tran' : forall r r1, -r + r1 = r1 - r.
Proof.
  intros; ring.
Qed.

Lemma Rplus_minus' : forall r1 r2 r3, r1 = r2 + r3 -> r3 = r1 - r2.
Proof.
  intros; symmetry; rewrite H.
  assert (r2 + r3 - r2 = r2 + (r3 - r2) ). { ring. } rewrite H0; apply Rplus_minus.
Qed.

Lemma Rplus_0_l : forall r, 0 + r = r.
Proof.
  intros; ring.
Qed.

Lemma pm_assoc : forall r1 r2 r3, r1 + (r2 - r3) = r1 + r2 - r3.
Proof.
  intros; ring.
Qed.

Lemma pm_assoc' : forall r1 r2 r3, r1 + r2 - r3 = r1 + (r2 - r3).
Proof.
  intros; ring.
Qed.

Lemma pm_change : forall r1 r2 r3, r1 + r2 - r3 - r3 - r3 = r1 - r3 + (r2 - r3) + - r3.
Proof.
  intros. ring.
Qed.

Lemma Rminus_r_0 : forall r r1, r - r1 = r -> r1 = 0.
Proof.
  intros. symmetry in H. apply Rplus_minus' in H. rewrite Rminus_eq_0 in H. 
  apply Ropp_eq_0_compat in H. rewrite Ropp_involutive in H. subst; auto.
Qed.

Lemma Rdiv_simpl_l : forall r1 r2, r1 <> 0 -> r2 / r1 * r1 = r2.
Proof.
  intros. unfold Rdiv. rewrite Rmult_assoc. rewrite (Rmult_comm (/ r1)).
  rewrite <- Rinv_r_sym; auto. apply Rmult_1_r.
Qed.

Lemma Rmult_assoc' : forall r1 r2 r3, r1 * (r2 * r3) = r1 * r2 * r3.
Proof.
  intros; ring.
Qed.

Lemma Rmult_comm' : forall r1 r2 r3, r1 * r2 * r3 = r1 * r3 * r2.
Proof.
  intros; ring.
Qed. 

Lemma Rmult_minus_distr_r : forall r1 r2 r3, r1 * (r2 - r3) = r1 * r2 - r1 * r3.
Proof.
  intros; ring.
Qed.

Lemma Rmult_minus_distr_r' : forall r1 r2 r3, (r2 - r3) * r1 = r1 * r2 - r1 * r3.
Proof.
  intros; ring.
Qed.

Lemma Rmult_mix_distr : forall r r1 r2 r3, r * (r1 + r2 - r3) = r * r1 + r * r2 - r * r3.
Proof.
  intros; ring.
Qed.

Lemma test0 :forall r1 r2 r3, r3 - (r2 - r1) = r3 + r1 - r2.
Proof.
  intros. ring.
Qed.

Lemma test : forall r1 r2 r3, r1 - r2 + r3 = 0 -> r3 = r2 - r1.
Proof.
  intros. apply Rminus_diag_uniq . rewrite test0. rewrite pm_assoc'. rewrite Rplus_comm; auto.
Qed.

Lemma test1 : forall r1 r2 r3 r4, r1 + r2 = r3 -> r1 + r2 - r4 = r3 - r4.
Proof.
  intros. rewrite H; auto.
Qed.

Lemma test2 : forall r1 r2 r3, r1 - (r2 + r3) = r1 - r2 - r3.
Proof.
  intros; ring.
Qed.

Lemma test2' : forall r1 r2 r3, r1 - r2 - r3 = r1 - (r2 + r3).
Proof.
  intros; ring.
Qed.

Lemma test3' : forall r1 r2 r3, r1 - (r2 - r3) = r1 - r2 + r3.
Proof.
  intros; ring.
Qed.

Lemma test3 : forall r1 r2 r3, r1 - r2 = r3 -> r1 - r3 = r2.
Proof.
  intros. symmetry in H. rewrite H. rewrite test3'. rewrite Rminus_eq_0. 
  apply Rplus_ne.
Qed.

Lemma test4 : forall r1 r2, r1 - - r2 = r1 + r2.
Proof.
  intros; ring.
Qed.

Lemma test5 : forall r r1, r + - (r - r1) = r1.
Proof.
  intros; ring.
Qed.

Lemma tt : forall r, - r - r = - (r + r).
Proof.
  intros. ring.
Qed. 

Lemma tt' : forall r r1, - r - r1 = - (r + r1). 
Proof.
  intros; ring.
Qed.

Lemma minus_eq : forall r r1, r - r1 + r1 = r.
Proof.
  intros; ring.
Qed.

Lemma minus_eq1 : forall r r1, - (r - r1) = r1 - r.
Proof.
  intros; ring.
Qed.

Lemma div_distr : forall r r1 r2, r2<>0 -> (r - r1) / r2 = r/r2 - r1/r2.
Proof.
  intros. unfold Rdiv. ring.
Qed.

Lemma minus_same : forall a b c, a=b <-> a - c = b -c.
Proof.
  intros. split.
  - intro. rewrite H; auto. - intro. apply (Rplus_eq_reg_l (-c) a b).
    rewrite Rplus_comm. rewrite (Rplus_comm (-c) b). auto. 
Qed.

Lemma div_same : forall a b c, a = b -> a/c = b/c.
Proof.
  intros. rewrite H; auto.
Qed.

Lemma Rmult_4 : forall a b c d, a * b * c * d = a *(b * c) *d.
Proof.
  intros; ring.
Qed.

Lemma div_all : forall a b c d,(a + b - c)*/d = a */d + b*/d - c*/d.
Proof.
  intros. ring.
Qed.

(* Lemma Rmult_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 * r = r2 * r.

Lemma Rmult_eq_reg_l : forall r r1 r2, r * r1 = r * r2 -> r <> 0 -> r1 = r2. *)

Lemma Rmult_plus_distr_l' : forall a b c,(a+b)*c = a*c+b*c.
Proof.
  intros; ring.
Qed.

