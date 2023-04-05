Require Export A_1.
Require Import Base.
Open Scope R_scope.

(* 例1 求证：三角形ABC的三条中线AM、BN、CP共点． *)
Lemma ex1_1 : 1 + 2 <> 0.
Proof.
  pose proof Rlt_0_1. pose proof H. apply Rplus_lt_0_compat with (r1:=1) in H.
  assert(1 + 1 = 2). { ring. } rewrite H1 in H.
  assert(0 < 1 + 2). { apply Rplus_lt_0_compat; auto. }
  apply Rlt_not_eq in H2;auto. auto.
Qed.

Example example_1' : forall B C G M N P, Triangle O B C 
  -> Inter_p B N C P G /\ Midpoint M B C /\ Midpoint N O C /\ Midpoint P O B 
  -> col G O M.
Proof.
  intros. destruct H0 as [H0 [H1 [H2 H3]]]. apply Midpoint_p in H2. apply Midpoint_p in H3.
  apply locate_P_2 in H1. 
  assert (B +.C = 2 *.P +.C). { rewrite H3; auto. }
  assert (B +.C = B +.2 *.N). { rewrite H2; auto. }
  unfold Inter_p in H0. rewrite H5 in H4.
  assert( 1 *.B +.2 *.N = ((1 + 2) *.G)). { apply H0 with (r := 1) (s := 2).
  repeat rewrite pmult_1_p. rewrite (pplus_comm C). 
  repeat split;auto. apply ex1_1. } 
  rewrite pmult_1_p in H6. replace (1 + 2) with 3 in H6; try ring.
  rewrite <- H5,H1 in H6. 
  unfold col. left. exists (2/3). induction G, M; unfold vector', point_minus, point_mult, O.
  repeat (rewrite Rminus_0_r). unfold point_mult in H6. injection H6 as H7 H8.
  unfold Rdiv. 
  repeat (rewrite Rmult_assoc); repeat (rewrite (Rmult_comm (/ (3)))); repeat (rewrite Rmult_assoc').
  rewrite H7, H8. repeat (rewrite Rinv_r_simpl_m). split; auto.
  - apply Rmult_integral_contrapositive_currified; auto.
    apply Rinv_neq_0_compat; auto.
  - auto. - auto.
Qed.

(* 例2 平行四边形ABCD的边AB中点为M，连DM交对角线AC于P．求证：AC=3AP． *)
Example example_2 : forall B C D M P,Parallelogram B O C D /\ Midpoint M O B /\ 
  Inter_p D M O C P -> vector' O C = 3 *.vector' O P.
Proof.
  intros. destruct H as [H[H0 H1]]. unfold vector'. repeat rewrite pminus_O.
  apply Midpoint_p in H0. unfold Parallelogram in H. 
  unfold Inter_p in H1. destruct H; unfold vector' in H. rewrite pminus_O in H.
  assert(B +.D = C -.D +.D). { rewrite H;auto. } 
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H3.
  assert (1 *.D +.2 *.M = (1 + 2) *.P). 
  { apply H1 with (r := 2)(s := 1). repeat rewrite pmult_1_p.
    rewrite pmult_0_l,pplus_O_p. rewrite H0,pplus_comm in H3.
    repeat split; try ring. apply H3. apply ex1_1. }
   rewrite pmult_1_p in H4. replace (1 + 2) with 3 in H4; try ring.
  rewrite <- H0,pplus_comm,H3 in H4. apply H4.
Qed.

(* 例3 已知AC=3AP，3AB=5AQ，求PD/BD,QD/CD,PQ/RQ,BR/CR。 *)
Lemma ex3_1 : 1 + 5 <> 0.
Proof.
  pose proof Rlt_0_1. pose proof H. apply Rplus_lt_0_compat with (r1:=1) in H.
  assert(1 + 1 = 2). { ring. } rewrite H1 in H.
  assert(0 < 1 + 2). { apply Rplus_lt_0_compat; auto. }
  assert(5 = 2 + 1 + 2). { ring. } rewrite H3.
  assert(1 + (2 + 1 + 2) = 1 + 2 + (1 + 2)). { ring. }
  assert(0 < 1 + (2 + 1 + 2)). { rewrite H4. apply Rplus_lt_0_compat. 
  apply H2. apply H2. } apply Rlt_not_eq in H5;auto. auto.
Qed. 

Lemma ex3_2 : 3 + -1 <> 0.
Proof.
  assert(3 + -1 = 2). { ring. } rewrite H.
  pose proof Rlt_0_1. pose proof H. apply Rplus_lt_0_compat with (r1:=1) in H0.
  assert(1 + 1 = 2). { ring. } rewrite H2 in H0.
  apply Rlt_not_eq in H0;auto. auto.
Qed.

Lemma ex3_2' : 2 <> 0.
Proof.
  replace 2 with (3 + -1); try ring. apply ex3_2.
Qed.


Lemma ex3_3 : forall A B C D a,a <> 0 -> a *.vector' A B = a *.vector' C D
  -> vector' A B = vector' C D.
Proof.
  intros. induction A,B,C,D;unfold vector',point_mult,point_minus in * .
  inversion H0. f_equal; eapply Rmult_eq_reg_l;eauto. 
Qed.

Lemma ex3_4 : forall A B C D a b,a *.vector' A B = b *.vector' C D
  -> a *.vector' B A = b *.vector' D C.
Proof.
  intros. induction A,B,C,D; unfold vector',point_mult,point_minus in * .
  inversion H. f_equal. rewrite <- Ropp_minus_distr in H1. 
  rewrite <- (Ropp_minus_distr r3) in H1. 
  repeat rewrite Ropp_mult_distr_r_reverse in H1.
  apply Ropp_eq_compat in H1. repeat rewrite Ropp_involutive in H1. auto.
  rewrite <- Ropp_minus_distr in H2. 
  rewrite <- (Ropp_minus_distr r4) in H2. 
  repeat rewrite Ropp_mult_distr_r_reverse in H2.
  apply Ropp_eq_compat in H2. repeat rewrite Ropp_involutive in H2.
  auto.
Qed.

Lemma ex3_5 : forall A B a, -a *.vector' A B = a *.vector' B A.
Proof.
  intros. unfold vector'. rewrite pmult_minus_opp'. auto.
Qed.

Lemma ex3_5' : forall A B, -1 *.vector' A B = vector' B A.
Proof.
  intros. unfold vector'. rewrite pmult_minus_opp. auto.
Qed.

Example example_3 : forall B C D P Q T, 
  C = 3 *.P /\ 5 *.Q = 3 *.B -> Inter_p C Q P B D -> Inter_p B C Q P T
  -> vector' P D = vector' D B /\ 5 *.vector' Q D = vector' D C
  /\ 3 *.vector' B T = vector' C T /\ 3 *.vector' P Q = 2 *.vector' Q T.
Proof.
  intros. destruct H. unfold Inter_p in H0, H1.
  assert(C +.5 *.Q = 3 *.P +.3 *.B).
  { rewrite H,H2;auto. }
  assert (1 *.C +.5 *.Q = (1 + 5) *.D).
  { apply H0 with (r := 3)(s := 3). rewrite pmult_1_p.
    repeat split; try ring. apply H3. apply ex3_1. }
  rewrite pmult_1_p in H4; replace (1 + 5) with 6 in H4; try ring.  
  assert (3 *.P +.3 *.B = 6 *.D). { rewrite <- H3;apply H4. }
  assert(C +.5 *.Q -.3 *.P = 3 *.B +.3 *.P -.3 *.P).
  { rewrite (pplus_comm (3 *.P)) in H3. rewrite H3;auto. }
  symmetry in H6. rewrite pplus_minus_assoc,pminus_eq_O,pplus_O_p' in H6.
  assert(3 *.B -.C = 5 *.Q -.3 *.P +.C -.C).
  { rewrite H6. rewrite pplus_comm. 
    induction C,Q,P;unfold point_plus,point_minus,point_mult.
    f_equal;ring. } 
  rewrite pplus_minus_assoc,pminus_eq_O,pplus_O_p' in H7.
  assert(3 *.B +.(-1)*.C = (3 + (-1))*.T).
  { apply H1 with (r := 5)(s := -3). 
    rewrite pmult_opp_p,pplus_minus_tran.
    assert(5 *.Q +.- 3 *.P = 5 *.Q -.3 *.P). 
    { induction Q,P;unfold point_plus,point_minus,point_mult. 
      f_equal; ring. } rewrite H8.
      repeat split; try ring. apply H7. apply ex3_2. }
  replace (3 + -1) with 2 in H8; try ring. 
  repeat split.
  - assert(6 *.D = (3 + 3) *.D).
    { replace (3 + 3) with 6;auto. ring. } rewrite H9 in H5.
    apply linear_com1' in H5. apply ex3_3 in H5;auto. 
  - assert(6 *.D = (1 + 5) *.D).
    { replace (1 + 5) with 6;auto. ring. } rewrite H9 in H4.
    rewrite <- (pmult_1_p C) in H4.
    apply linear_com1' in H4. apply ex3_4 in H4. 
    rewrite pmult_1_p in H4. auto.
  - assert(2 *.T = (3 + -1)*.T). 
    {replace (3 + -1) with 2;auto. ring. } rewrite H9 in H8.
    apply linear_com1' in H8. rewrite ex3_5' in H8;auto.
  - rewrite pmult_opp_p,pplus_minus_tran in H8. rewrite H7 in H8.
    assert(2 *.T = (5 + -3)*.T).
    {replace (5 + -3) with 2;auto. ring. } rewrite H9 in H8.
    assert(5 *.Q +.- 3 *.P = 5 *.Q -.3 *.P). 
    { induction Q,P;unfold point_plus,point_minus,point_mult. 
      f_equal; ring. } rewrite <- H10 in H8. apply linear_com1 in H8.
    unfold vector'. repeat rewrite pmult_minus_distr_l.
    symmetry in H8. rewrite <- pmult_minus_opp' in H8.
    replace (-(-3)) with 3 in H8;try ring.
    repeat rewrite pmult_minus_distr_l in H8. symmetry in H8.
    assert(5 *.Q -.5 *.T +.5 *.T = 3 *.P -.3 *.T +.5 *.T).
    { rewrite H8;auto. }
    rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H11.
      assert(3 *.P -.3 *.T +.5 *.T = 3 *.P +.2 *.T).
      { induction P,T; unfold point_mult,point_minus,point_plus. 
        f_equal;ring. } rewrite H12 in H11.
    rewrite pplus_comm in H11.
    assert(5 *.Q -.3 *.P = 2 *.T +.3 *.P -.3 *.P).
    { rewrite H11;auto. } 
    rewrite pplus_minus_assoc,pminus_eq_O,pplus_O_p' in H13.
    assert(5 *.Q -.2 *.Q -.3 *.P = 2 *.T -.2 *.Q).
    { rewrite <- H13. induction Q,P;unfold point_mult,point_minus.
      f_equal;ring. }
    assert(5 *.Q -.2 *.Q = 3 *.Q).
    { rewrite <- pmult_minus_distr'. replace (5 - 2) with 3; try ring;auto. }
    rewrite H15 in H14. apply H14.
Qed.
    
(* 例4 三角形ABC的三条高线AD、BE、CF共点． *)
Lemma e4 : forall A B C D, A ·.B - C ·.D = 0 -> A ·.B = C ·.D.
Proof.
  intros. induction A, B, C; unfold point_magn in H; unfold point_magn.
  apply Rminus_diag_uniq in H; auto.
Qed.

Example example_4 : forall A B C D E F,Triangle A B C /\ Perp A D B C /\ Perp B E A C /\ 
  Perp C F A B /\ Inter_p A D B E O /\ Perp A O B C /\ Perp B O A C -> Perp C O A B.
Proof.
  intros. destruct H as [H0[H1[H2[H3[H4[H5 H6]]]]]].
  unfold Perp in H5, H6; unfold Perp. rewrite pminus_O in H5, H6; rewrite pminus_O.
  rewrite Pmagn_minus_distr in H5, H6. rewrite Pmagn_comm in H6.
  apply e4 in H5. apply e4 in H6.
  rewrite Pmagn_minus_distr. rewrite Pmagn_comm; rewrite (Pmagn_comm (C)).
  symmetry in H5, H6. rewrite H5, H6.
  induction A, B. unfold point_magn; ring. 
Qed.

(* 例5 已知▲ABC三边a、b、c，求中线AD和分角线AE。 *)

Lemma e5_1 : forall A B, point_sqr(A +.B) = point_sqr A + point_sqr B + 2 * (A ·.B).
Proof.
  intros. unfold point_sqr, point_magn, point_plus; induction A, B; ring.
Qed. 

Lemma e5_2 : forall λ A, point_sqr(λ *.A) = Rsqr λ * point_sqr A.
Proof.
  intros. induction A; unfold point_sqr, point_mult, point_magn, Rsqr; ring.
Qed.
Lemma e5_3 : forall A B, A = B -> point_sqr A = point_sqr B.
Proof. 
  intros. unfold point_sqr; rewrite H; auto.
Qed.

Lemma e5_4''' : forall A B, point_sqr(A +.B) - point_sqr(A -.B) = 4 * (A ·.B).
Proof. 
  intros. induction A, B; unfold point_sqr, point_plus, point_minus, point_magn; ring.
Qed.

Lemma e5_4 : forall A B, 2 * (A ·.B) = (point_sqr(A +.B) - point_sqr(A -.B))/2.
Proof.
  intros. rewrite e5_4'''. induction A, B; unfold Rdiv, point_magn. replace 4 with (2*2); auto.
  rewrite (Rmult_assoc (2)). rewrite Rinv_r_simpl_m. auto. auto.
Qed.

Example example_5_1 : forall B C D a b c, Triangle O B C /\ gap_sqr B O = Rsqr c /\ 
  gap_sqr C O = Rsqr b  /\ gap_sqr B C = Rsqr a /\ Midpoint D B C 
  -> gap_sqr D O = ((Rsqr c + Rsqr b)-Rsqr a/2)/2.
Proof.
  intros. destruct H as [H[H0[H1[H2 H3]]]]. apply locate_P_2 in H3.
  assert (point_sqr(B +.C) = point_sqr(2 *.D)). { apply e5_3 in H3; auto. }
  rewrite e5_1, e5_2 in H4. rewrite gap_sqr_O in H0, H1. rewrite H0, H1 in H4.
  unfold gap_sqr in H2. rewrite e5_4 in H4. rewrite H2, H3, e5_2 in H4.
  rewrite gap_sqr_O. induction D; unfold point_sqr, point_magn. 
  unfold point_sqr, point_magn in H4. rewrite div_distr in H4. unfold Rsqr, Rdiv in H4.
  assert(2 * 2 * (r * r + r0 * r0) * / 2 = 2 * (r * r + r0 * r0)).
  { rewrite (Rmult_assoc (2)). rewrite Rinv_r_simpl_m. auto. auto. }
  rewrite H5 in H4. 
  assert((2*2*(r * r + r0 * r0)) =(2 * (r * r + r0 * r0) + 2 * (r * r + r0 * r0)) ).
  { ring. } rewrite H6 in H4. 
  assert(c * c + b * b + (2 * (r * r + r0 * r0) - a * a * / 2) - 2 * (r * r + r0 * r0)=
     2 * (r * r + r0 * r0) + 2 * (r * r + r0 * r0) - 2 * (r * r + r0 * r0)).
  { apply minus_same. apply H4.  }
  assert(c * c + b * b + (2 * (r * r + r0 * r0) - a * a * / 2) -
     2 * (r * r + r0 * r0) = c * c + b * b - a * a * / 2). { ring. }
  assert(2 * (r * r + r0 * r0) + 2 * (r * r + r0 * r0) - 2 * (r * r + r0 * r0) =
     2 * (r * r + r0 * r0)). { ring. } rewrite H8, H9 in H7.
  assert((c * c + b * b - a * a * / 2)/2 = (2 * (r * r + r0 * r0))/2).
  { apply div_same. apply H7. } symmetry in H10. unfold Rdiv in H10.
  rewrite Rinv_r_simpl_m in H10. rewrite H10. unfold Rsqr, Rdiv. ring. 
  auto. auto.
Qed.

Lemma e5_5 : forall B C E, gap C O *.B +.gap B O *.C = (gap B O + gap C O) *.E
  -> point_sqr(gap C O *.B +.gap B O *.C) = point_sqr((gap B O + gap C O) *.E).
Proof.
  intros. rewrite H; auto.
Qed.

Lemma e5_5' : forall B C, point_sqr(gap C O *.B +.gap B O *.C) = 
  Rsqr(gap C O) * point_sqr B + Rsqr(gap B O) * point_sqr C 
  + 2*(gap B O)*(gap C O) *(B ·.C).
Proof.
  intros. rewrite e5_1. repeat rewrite gap_O. unfold point_sqr, gap, Rsqr.
  induction B, C; unfold point_mult, point_magn; ring.
Qed.

Lemma e5_5'' : forall B C E, point_sqr((gap B O + gap C O) *.E) = 
  Rsqr(gap B O + gap C O) * point_sqr E.
Proof.
  intros. rewrite e5_2; auto.
Qed.

Example example_5_2 : forall B C D E a b c, Triangle O B C /\ gap B O = c /\ 
  gap C O = b  /\ gap B C = a /\ Midpoint D B C /\ Angle_div E O B C 
  /\ gap_sqr D O = (b² + c² - a² / 2) / 2 /\ (c + b) <> 0
  -> gap_sqr E O = (2 * Rsqr b * Rsqr c + b * c * (Rsqr b + Rsqr c - Rsqr a))/Rsqr (c + b).
Proof.
  intros. destruct H as [H[H0[H1[H2 [H3 [H4 [H5 H6]]]]]]]. unfold Angle_div in H4.
  assert(point_sqr(gap C O *.B +.gap B O *.C) = point_sqr((gap B O + gap C O) *.E)).
  { apply e5_5, H4. } rewrite e5_5', e5_5'' in H7. rewrite H0, H1 in H7.
  assert(Rsqr(gap B O) = point_sqr B). { apply gap_to_sqr_O. }
  assert(Rsqr(gap C O) = point_sqr C). { apply gap_to_sqr_O. }
  rewrite H0 in H8. rewrite H1 in H9. symmetry in H8, H9.
  rewrite H8, H9 in H7.
  assert(b² * c² + c² * b² = 2 * b² * c²).
  { unfold Rsqr. ring. }
  assert(2 * c * b *(B ·.C) = b * c * (2 * (B ·.C))).
  { induction B, C; unfold point_magn. ring. } rewrite H10, H11 in H7.
  rewrite e5_4 in H7. apply locate_P_2 in H3. rewrite H3 in H7.
  rewrite gap_sqr_O in H5. rewrite e5_2 in H7.
  assert(gap_sqr B C = a²).
  { symmetry in H2. rewrite H2. rewrite gap_to_sqr. auto. }
  unfold gap_sqr in H12. rewrite H5, H12 in H7.
  assert(((2² * ((b² + c² - a² / 2) / 2) - a²) / 2) = b² + c² - a²).
  { unfold Rsqr, Rdiv. rewrite Rmult_assoc'. rewrite (Rmult_assoc (2)). 
    rewrite Rinv_r_simpl_m. rewrite Rmult_mix_distr. repeat rewrite Rmult_assoc'.
    rewrite Rmult_4, Rinv_r_simpl_m. 
    assert(2 * b * b + 2 * c * c - a * a - a * a = 2 * b * b + 2 * c * c - 2 * a * a).
    { ring. } rewrite H13. rewrite div_all. repeat rewrite Rmult_4, Rinv_r_simpl_m.
    auto. auto. auto. auto. auto. auto. }
  rewrite H13 in H7. rewrite gap_sqr_O.
  assert((2 * b² * c² + b * c * (b² + c² - a²))/(c + b)²= (c + b)² * point_sqr E/(c + b)²).
  { apply div_same. apply H7. } rewrite H14.
  induction E; unfold point_sqr, point_magn. 
  unfold Rdiv. rewrite Rinv_r_simpl_m. auto. apply sqr_0, H6.
Qed.
  
Lemma oc_1 : forall A B C, orthocenter O A B C -> A ·.(B -.C) = B ·.(A -.C) 
  /\ B ·.(A -.C) = C ·.(A -.B) /\ B ·.(A -.C) = 0.
Proof.
  intros. unfold orthocenter in H. unfold vector' in H. repeat rewrite pminus_O in H.
  destruct H. assert(A ·.B = C ·.A). { rewrite H, H0; auto. } 
  assert(C ·.A = A ·.C). { rewrite Pmagn_comm. auto. }
  assert(A ·.B = B ·.A). { rewrite Pmagn_comm. auto. } 
  assert(C ·.B = B ·.C). { rewrite Pmagn_comm. auto. }
  repeat split; repeat rewrite Pmagn_minus_distr.
  - symmetry in H2, H3. rewrite H, H2, H3. 
    symmetry in H0. rewrite H0, H. repeat rewrite Pmagn_minus_0; auto.
  - symmetry in H3, H0. rewrite H3, H, H0, H4. repeat rewrite Pmagn_minus_0; auto.
  - symmetry in H3. rewrite H3, H; rewrite Pmagn_minus_0; auto.
Qed.

(* 例7 ABCD为平行四边形，E为其对角线交点，P为任意一点．已知向量PA、PB、PC，求向量PD、PE． *)
Lemma E7_1 : forall A C D P,
  P /p A +.(P /p C) = P /p D -.P -> P /p D = P /p A +.(P /p C) -.(P /p O).
Proof.
  intros. 
  induction A, C, D, P; unfold point_Oprod, point_plus, point_minus in H; unfold point_Oprod, point_plus, point_minus, O.
  injection H as H0 H.
  repeat (rewrite Rminus_0_l, test4).
  assert (r3 - r5 = r - r5 + (r1 - r5) + r5). { rewrite H0; ring. }
  assert (r4 - r6 = r0 - r6 + (r2 - r6) + r6). { rewrite H; ring. }
  rewrite H1, H2; auto.
Qed.

Lemma E7_2 :forall A C E P,
  P /p A +.(P /p C) = 2 *.(P /p E) -> P /p E = 1 / 2 *.(P /p A +.(P /p C)).
Proof.
  intros.
  induction A, C, E, P; unfold point_Oprod, point_plus, point_minus, point_mult in H; 
  unfold point_Oprod, point_plus, point_minus, point_mult.
  injection H as H0 H.
  assert (r3 - r5 = 1 / 2 * (r - r5 + (r1 - r5))). { rewrite H0. unfold Rdiv. rewrite Rmult_assoc'. 
         rewrite Rmult_1_l. rewrite Rinv_l. ring. auto. }
  assert (r4 - r6 = 1 / 2 * (r0 - r6 + (r2 - r6))). { rewrite H. unfold Rdiv. rewrite Rmult_assoc'. 
         rewrite Rmult_1_l. rewrite Rinv_l. ring. auto. }
  rewrite H1, H2; auto.
Qed.

Example example_7 : forall A C D E P, Parallelogram A O C D /\ Plg E A O C D 
  -> P /pD = P /pA +.(P /pC) -.(P /pO) /\ P /pE = 1/2 *.(P /pA +.(P /pC)).
Proof.
  intros. destruct H. unfold Parallelogram in H; unfold Plg in H0.
  destruct H0. destruct H1. apply locate_P_2 in H1; apply locate_P_2 in H2. rewrite pplus_O_p in H2.
  assert (A +.C = D). { rewrite H2; auto. }
  assert (A +.C = D +.O). { rewrite H2. rewrite pplus_O_p'; auto. }
  pose proof (Oprod_plus_distr A C E P 1 1).
  pose proof (Oprod_plus_distr_ex' A C D P 1 1 1).
  split.
  - assert (1 + 1 - 1 = 1). { ring. } rewrite H7 in H6. repeat (rewrite pmult_1_p in H6).
    apply E7_1; auto.
  - assert (1 + 1 = 2). { ring. } rewrite H7 in H5. repeat (rewrite pmult_1_p in H5).
    apply E7_2; auto.
Qed.

(* 例8 ▲ABC的三边上分别取点P、Q、R使BP=PC，CQ=2QA，AR=3RB．三线AP、BQ、CR构成▲LMN，如图所示，求△LMN的面积． *)
Lemma e8_1 : forall A B C (u v : R), A +.B = u *.C -> v *.(A +.B) = (v*u) *.C.
Proof.
  intros. induction A, B, C; unfold point_plus, point_mult. 
  unfold point_plus, point_mult in H. injection H as H0 H1.
  rewrite H0, H1. repeat rewrite Rmult_assoc; auto.
Qed.

Lemma e8_2 : 2 + 2 <> 0.
Proof.

Admitted.

Lemma e8_3 : 1 + 6 <> 0.
Proof.

Admitted.

Lemma e8_4 : 1 + 8 <> 0.
Proof.

Admitted.


Example example_8 : forall B C P Q S L M N, Triangle O B C /\ Midpoint P B C /\ 
  C = 3 *.Q /\ 3 *.B = 4 *.S /\ Inter_p O P B Q N /\ Inter_p O P S C M
  /\ Inter_p C S Q B L
  -> 252 * point_3prod L M N = 25 * point_3prod O B C.
Proof.
  intros. destruct H as [H[H1[H2 [H3[H4 [H5 H6]]]]]]. apply locate_P_2 in H1.
  unfold Inter_p in * .
  assert(B +.3 *.Q = 2 *.O +.2 *.P). 
  { rewrite pmult_0_l,pplus_O_p. rewrite H2 in H1. apply H1. }
  assert(B +.3 *.Q = 4 *.N).
  { rewrite H0. replace 4 with (2 + 2); try ring.
    apply H4 with (r := 1)(s := 3). rewrite <- (pmult_1_p B) in H0.
    rewrite <- H0. repeat split;auto; try ring. apply e8_2. }
  assert(3 *.B +.3 *.C = 6 *.P). 
  { apply e8_1 with (v := 3) in H1. rewrite pmult_plus_distr_l in H1. 
    assert (3 * 2 = 6). { ring. } rewrite H8 in H1. apply H1. }
  assert(4 *.S +.3 *.C = 1 *.O +.6 *.P). 
  { rewrite H3 in H8. rewrite pmult_0_l,pplus_O_p. apply H8. }
  assert(1 *.O +.6 *.P = (1 + 6) *.M). 
  { apply H5 with (r := 4)(s := 3). rewrite H9. 
    repeat split; try ring;auto. apply e8_3. }
  assert(4 *.S +.3 *.C = 7 *.M).
  { rewrite <- H9 in H10. replace (1 + 6) with 7 in H10; try ring. auto. } 
  assert(6 *.B = 8 *.S). 
  { replace 6 with(2 * 3). replace 8 with(2 * 4). 
  assert(2 * 3 *.B = 2 *.(3 *.B)). 
  { induction B; unfold point_mult. repeat rewrite Rmult_assoc. auto. } 
  rewrite H12, H3. induction S; unfold point_mult. repeat rewrite Rmult_assoc; auto.
  ring. ring. }
  assert(C +.8 *.S = 3 *.Q +.6 *.B). { rewrite H2, H12. auto. } 
  assert(1 *.C +.8 *.S = (1 + 8) *.L). 
  { apply H6 with (r := 3)(s := 6). rewrite pmult_1_p.  
    repeat split;try ring;auto. apply e8_4. }
  assert(3 *.Q +.6 *.B = 9 *.L). 
  { rewrite pmult_1_p in H14. replace (1 + 8) with 9 in H14.
    rewrite <- H14, H13;auto. ring. }
  assert(9 *.L = 2 *.O +.6 *.B +.C).
  { rewrite <- H2 in H15. rewrite <- H15. 
    rewrite pmult_0_l, pplus_O_p, pplus_comm. auto. }
  assert(7 *.M = O +.3 *.B +.3 *.C).
  { rewrite <- H11, H3, pplus_O_p. auto. }
  assert(4 *.N = 2 *.O +.B +.C).
  { rewrite <- H7, H2. rewrite pmult_0_l, pplus_O_p. auto. }
  rewrite pmult_1_p in H10;replace(1 + 6) with 7 in H10;try ring.
  rewrite pmult_1_p in H14;replace(1 + 8) with 9 in H14;try ring.
  
Admitted. 

(* 例2 垂心定理:▲ABC中,若AH⊥BC,BH⊥CA,求证:CH⊥AB． *)
Theorem Per_center : forall A B C H, Triangle A B C -> Perp A H B C /\ Perp B H C A
  -> Perp C H A B.
Proof.
  intros. destruct H1. unfold Perp in H1, H2. unfold Perp.
  assert ((C -.H) ·.(A -.B) + (A -.H) ·.(B -.C) + (B -.H) ·.(C -.A) = 0).
  { induction A, B, C, H. unfold point_minus, point_magn. ring. }
  rewrite H1, H2 in H3. repeat (rewrite Rplus_0_r in H3). auto.
Qed.

(* 例3 外心定理:▲ABC中,若点O在AB、BC的中垂线上,则点O在CA的中垂线上．*)
Theorem circumcenter : forall A B C D E F P, Midpoint F C A /\ C <> A 
  -> Perp_bisect D P D A B /\ Perp_bisect E P E B C -> Perp_bisect F P F C A.
Proof.
  intros. destruct H. destruct H0. unfold Perp_bisect in H0, H2. destruct H0 as [H0[H3 H4]].
  destruct H2 as [H2[H5 H6]]. unfold Perp_bisect. destruct H0, H2.
  repeat split; auto.
  - unfold col;auto. 
  - apply locate_P_2 in H. apply locate_P_2 in H0. apply locate_P_2 in H2. 
    rewrite Midpoint_tran in H, H0, H2. unfold Perp in H3, H5. unfold Perp. 
    symmetry in H, H0, H2. rewrite H. rewrite H0 in H3. rewrite H2 in H5.
    assert((P -.(A +.B) /.2) ·.(A -.B) + (P -.(B +.C) /.2) ·.(B -.C) 
          + (P -.(C +.A) /.2) ·.(C -.A) = 0).
    { induction A, B, C, P. unfold point_minus, point_plus, point_divR, point_magn, Rdiv. ring. }
    rewrite H3, H5 in H9. repeat (rewrite Rplus_0_l in H9). auto.
Qed.

(* 例1 DE为ΔABC的中位线，求证DE‖BC,且DE＝1/2BC． *)
Example ex_2_1 : forall B C D E, Mid_line D E O B C 
  -> vector' B C = 2 *.vector' D E.
Proof.
  intros. unfold Mid_line in H. destruct H. apply locate_P_2 in H. 
  apply locate_P_2 in H0. rewrite pplus_O_p in H,H0. unfold vector'.
  rewrite H,H0. rewrite pmult_minus_distr_l. auto.
Qed.

(* 例2 四边形ABCD为平行四边形，E、F分别是AD、BC的中点，BE、DF分别交AC于G、H．求证：四边形GBDH为平行四边形． *)
Lemma  ex_2_2' : forall A B a, a<>0 -> a *.A = a *.B <-> A = B.
Proof. 
  intros. split. 
  - intros. induction A,B; unfold point_mult in H0. inversion H0. 
  apply Rmult_eq_reg_l in H2. apply Rmult_eq_reg_l in H3. subst;auto.
  auto. auto.
  - intro. rewrite H0;auto.
Qed.

Lemma ex_2_2'' : forall A B C D, A +.B +.C +.D = A +.B +.(C +.D).
Proof.
  intros. induction A,B,C,D;unfold point_plus;f_equal;ring.
Qed. 

Example ex_2_2 : forall A B C D E F G H, Parallelogram A D B C -> Midpoint E A D -> Midpoint F B C
  -> Inter_p B E A C G -> Inter_p D F A C H -> G <> D -> Parallelogram G B D H.
Proof.
  intros. unfold Parallelogram in H0. apply locate_P_2 in H1. apply locate_P_2 in H2.
  destruct H0. unfold vector' in H0. 
  assert(2 *.(E -.D) = 2 *.(B -.F)).
  { repeat rewrite pmult_minus_distr_l. rewrite <- H1. rewrite <- H2.
    assert(A +.D -.2 *.D = A -.D). 
    { induction A,D;unfold point_minus,point_plus,point_mult. f_equal;ring. }
    assert(2 *.B -.(B +.C) = B -.C).
    { induction B,C;unfold point_minus,point_plus,point_mult. f_equal;ring. }
    rewrite H7,H8;auto. } 
  repeat rewrite pmult_minus_distr in H7. pose proof H7. pose proof H7. 
  rewrite <- H1 in H7. assert(B = 2 *.F -.C).
  { rewrite <- H2,pplus_minus_assoc,pminus_eq_O,pplus_O_p';auto. }
  rewrite H10 in H7. rewrite pmult_minus_distr_l,pmult_l_l_p in H7.
  replace (2 * 2) with 4 in H7;try ring. 
  assert(A -.D = 2 *.F -.2 *.C).
  { assert(A +.D -.2 *.D = A -.D). 
    { induction A,D;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    assert(4 *.F -.2 *.C -.2 *.F = 2 *.F -.2 *.C).
    { induction F,C;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    rewrite H11,H12 in H7;auto. }
  assert(A +.2 *.C = D +.2 *.F).
  { assert(A -.D +.D +.2 *.C = 2 *.F -.2 *.C +.D +.2 *.C). 
    { rewrite H11;auto. } 
    assert(A -.D +.D +.2 *.C = A +.2 *.C).
    { induction A,C,D;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    assert( 2 *.F -.2 *.C +.D +.2 *.C = D +.2 *.F).
    { induction F,C,D;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    rewrite H14,H13 in H12;auto. }
  rewrite <- H2 in H8. assert(D = 2 *.E -.A).
  { rewrite <- H1,pplus_comm,pplus_minus_assoc,pminus_eq_O,pplus_O_p';auto. }
  rewrite H13 in H8. rewrite pmult_minus_distr_l,pmult_l_l_p in H8.
  replace (2 * 2) with 4 in H8;try ring.
  assert(2 *.A -.2 *.E = B -.C).
  { assert(2 *.E -.(4 *.E -.2 *.A) = 2 *.A -.2 *.E).
    { induction A,E;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    assert(2 *.B -.(B +.C) = B -.C).
    { induction B,C;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    rewrite H15,H14 in H8;auto.  }
  assert(2 *.A +.C = B +.2 *.E).
  { assert(2 *.A -.2 *.E +.2 *.E +.C = B -.C +.2 *.E +.C). 
    {rewrite H14;auto. }
    assert(2 *.A -.2 *.E +.2 *.E +.C = 2 *.A +.C).
    { induction A,C,E;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    assert(B -.C +.2 *.E +.C = B +.2 *.E).
     { induction B,C,E;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    rewrite H17,H16 in H15;auto. }
  unfold Inter_p in * .  assert(1 *.D +.2 *.F = (1 + 2) *.H).
  { apply H4 with (r:=1)(s:=2). repeat rewrite pmult_1_p.
    rewrite H12. repeat split;auto;try ring. apply ex1_1.  }
  assert(1 *.B +.2 *.E = (1 + 2) *.G).
  { apply H3 with (r:=2)(s:=1). repeat rewrite pmult_1_p.
    rewrite H15. repeat split;auto;try ring. apply ex1_1. }
  repeat rewrite <- pmult_minus_distr in H9. apply ex_2_2' in H9.
  assert(E +.F = B +.D).
  { assert(E -.D +.D +.F = B -.F +.D +.F). { rewrite H9;auto. }
    assert(E -.D +.D +.F = E +.F).
    { induction D,E,F;unfold point_plus,point_minus,point_mult;f_equal;ring. }
    assert(B -.F +.D +.F = B +.D).
    { induction B,D,F;unfold point_plus,point_mult,point_minus;f_equal;ring. }
    rewrite H20,H19 in H18;auto. } 
  rewrite pmult_1_p in H16. replace (1+2) with 3 in H16;try ring.
  rewrite pmult_1_p in H17. replace (1+2) with 3 in H17;try ring.
  assert(3 *.G +.3 *.H = B +.D +.2 *.E +.2*.F).
  { rewrite <- H17,<- H16. induction B,D,E,F,G,H;unfold point_plus,point_mult;
    f_equal;ring. } 
  apply (ex_2_2') with (a:=2) in H18. repeat rewrite pmult_plus_distr_l in H18.
  rewrite ex_2_2'' in H19. rewrite H18 in H19.
  assert(B +.D +.(2 *.B +.2 *.D) = 3 *.B +.3 *.D).
  { induction B,D;unfold point_plus,point_mult;f_equal;ring. } rewrite H20 in H19.
  repeat rewrite <- pmult_plus_distr_l in H19. apply ex_2_2' in H19.
  unfold Parallelogram. split;auto;unfold vector'.
  assert(G = B +.D -.H).
  { rewrite <- H19. rewrite pplus_minus_assoc,pminus_eq_O,pplus_O_p';auto.  }
  rewrite H21.
  - induction B,D,H;unfold point_plus,point_minus;f_equal;ring.
  - replace 3 with (1 + 2);try ring. apply ex1_1. 
  - apply ex3_2'.
  - apply ex3_2'.  
Qed.

(* 例3 平行四边形ABCD中，点M是边AB的中点，点N在BD上，且BN＝1/3BD，证明：M、N、C三点共线。 *)
Lemma ex_2_3_1 : forall A B C, A - B = -C -> B - A = C.
Proof.
  intros. apply Ropp_eq_compat in H. rewrite Ropp_involutive in H. symmetry in H.
  rewrite H. ring.
Qed.

Lemma ex_2_3_2 : forall A B C,A -.B = --C -> B -.A = C.
Proof.
  intros. induction A,B,C. unfold point_inverse,point_minus.
  unfold point_inverse,point_minus in H. injection H as H1 H2.
  apply ex_2_3_1 in H1. apply ex_2_3_1 in H2. rewrite H1,H2. auto.
Qed.

Example ex_2_3 : forall A C D M N, Parallelogram A D O C -> Midpoint M O A -> 3 *.N = D 
  -> col M N C.
Proof.
  intros. apply Midpoint_p in H0. unfold Parallelogram in H.
  assert(2 *.M -.3 *.N = A -.D). { rewrite H0. rewrite H1. auto. }
  destruct H. unfold vector' in H. rewrite pminus_O_A in H. rewrite H in H2.
  assert(2 *.M +.C = 3 *.N). { apply ex_2_3_2 in H2. symmetry in H2. rewrite H2. 
  rewrite <- pplus_minus_assoc. rewrite pplus_comm. rewrite pplus_minus_assoc.
  rewrite (pminus_eq_O (2 *.M)). rewrite pplus_O_p'. auto. }
  apply(linear_com2 M C N 2 1). split. 
  - replace 2 with (3 + -1); try ring. apply ex3_2.
  - pose proof Rlt_0_1. apply Rlt_not_eq in H5;auto.
  - rewrite <- (pmult_1_p C) in H4. replace (2 + 1) with 3;try ring;auto.
Qed.

(* 例4 在△ABC中,点M是BC的中点,点N在边AC上,且AN=2NC,AM与BN相交于点P,求证：AP:PM=4:1,BP:PN=3:2. *)
Lemma ex_2_4_1 : forall A B C, A = B -.C -> A +.C = B.
Proof.
  intros. rewrite H. rewrite <- pplus_minus_tran.
  assert((-- C) +.C = O). { induction C; unfold point_inverse, point_plus, O. 
  repeat (rewrite Rplus_opp_l). auto. } 
  rewrite pplus_assoc'. rewrite H0. rewrite pplus_O_p'; auto.
Qed.

Lemma ex_2_4_2 : 1 + 4 <> 0.
Proof.
  intros. replace (1 + 4) with (1 + 2 + 2);try ring.
  pose proof Rlt_0_1. pose proof H. apply Rplus_lt_0_compat with (r1:=1) in H.
  assert(0 < 1 + 2). { apply Rplus_lt_0_compat; auto. }
  assert(0 < 1 + 2 + 2). { apply Rplus_lt_0_compat; auto. }
  apply Rlt_not_eq in H2;auto. auto.
Qed.

Example ex_2_4 : forall B C M N P,Triangle O B C -> Midpoint M B C -> vector' O N = 2 *.vector' N C 
  -> Inter_p O M B N P -> vector' O P = 4 *.vector' P M /\ 2 *.vector' B P = 3 *.vector' P N.
Proof.
  intros. apply locate_P_2 in H0. unfold vector' in H1. rewrite pminus_O in H1. 
  rewrite pmult_minus_distr in H1. 
  assert(3 *.N = 2 *.C). { apply ex_2_4_1 in H1. 
  assert(1 *.N +.2 *.N = N +.2 *.N). { rewrite pmult_1_p. auto. } 
  rewrite <- H3 in H1. rewrite <- pmult_plus_distr_l' in H1. replace (1+2) with 3 in H1.
  apply H1. auto.  } 
  assert(2 *.(B +.C) = 4 *.M). { replace 4 with (2 * 2). apply e8_1. apply H0. auto. }
  rewrite pmult_plus_distr_l in H4. rewrite <- H3 in H4. unfold Inter_p in H2.
  replace(4 *.M) with (1 *.O +.4 *.M) in H4. symmetry in H4.
  assert(1 *.O +.4 *.M = (1 + 4) *.P). 
  { apply H2 with (r:=2) (s:=3). repeat split;auto;try ring. apply ex_2_4_2. }
  assert(2 *.B +.3 *.N = (2 + 3) *.P).
  { rewrite H4 in H5. replace (1 + 4) with (2 + 3) in H5;try ring;auto.  }
  split. - apply linear_com1' in H5. rewrite <- H5. unfold vector'.
  rewrite pmult_1_p;auto.
  - apply linear_com1' in H6;auto.
  - rewrite pmult_0_l,pplus_O_p;auto.
Qed.

(* 例5 在ΔABC中,点D和点E分别在边BC与AC上,且BD＝1/3BC,CE＝1/3CA,AD与BE交于F,求证:FD＝1/7AD,FE＝4/7BE. *)
Lemma ex_2_5_1 : forall A B C D,A +.B = C -> A +.B -.D = C -.D.
Proof.
  intros. rewrite H; auto.
Qed.

Lemma ex_2_5_2 : forall A B C, A -.B +.C = A +.C -.B.
Proof.
  intros. induction A,B,C; unfold point_minus,point_plus.
  replace (r - r1 + r3) with (r + r3 - r1); replace (r0 - r2 + r4) with (r0 + r4 - r2).
  auto. ring. ring. ring.
Qed.

Lemma ex_2_5_3 : 1 + 6 <> 0.
Proof.
Admitted.

Example ex_2_5 : forall B C D E F,Triangle O B C -> col D B C /\ col E O C 
  -> 3 *.vector' B D = vector' B C -> 3 *.vector' C E = vector' C O -> Inter_p O D B E F
  -> 7 *.vector' F D = vector' O D /\ 7 *.vector' F E = 4 *.vector' B E.
Proof.
  intros. unfold vector' in H1,H2. rewrite pmult_minus_distr_l in H1,H2. 
  rewrite pminus_O_A in H2. apply ex_2_3_2 in H2. symmetry in H2. apply ex_2_4_1 in H2.
  rewrite pplus_comm in H2. apply (ex_2_5_1 (3 *.E) C (3 *.C) C) in H2.
  rewrite pplus_minus_assoc,pminus_eq_O,pplus_O_p' in H2. 
  replace (3 *.C -.C) with (2 *.C) in H2.
  assert(3 *.D -.3 *.B +.3 *.B = C -.B +.3 *.B). { rewrite H1; auto. } 
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H4.
  rewrite ex_2_5_2, pplus_minus_assoc in H4. 
  replace (3 *.B -.B) with (2 *.B) in H4. symmetry in H4.
  assert(2*.(C +.2 *.B) = 2 * 3 *.D). { apply e8_1. apply H4. }
  rewrite pmult_plus_distr_l in H5. replace (2 *.(2 *.B)) with (4 *.B) in H5.
  assert (2 * 3 = 6). { ring. } rewrite H6 in H5. 
  symmetry in H2. rewrite H2 in H5. unfold Inter_p in H3. 
  replace (6 *.D) with (1 *.O +.6 *.D) in H5.
  assert(1 *.O +.6 *.D = (1 + 6) *.F).
  { apply H3 with (r:=4) (s:=3). repeat split;try rewrite <- H5;try ring.
    rewrite pplus_comm;auto. apply ex_2_5_3. }
  split. - unfold vector'. apply linear_com1' in H7. unfold vector' in H7.
  rewrite pmult_minus_distr,pminus_O. rewrite pminus_O,pmult_minus_distr,pmult_1_p in H7.
  assert(F -.F = 6 *.D -.6*.F -.F).
  { symmetry in H7. rewrite H7. auto. }
  rewrite pminus_eq_O in H8. assert(6 *.D -.6 *.F -.F = 6 *.D -.7*.F).
  { induction D,F;unfold point_mult,point_minus. f_equal;ring. }
  rewrite H9 in H8. assert(O +.D = 6 *.D +.D -.7 *.F).
  { rewrite H8. rewrite ex_2_5_2. auto. } 
  rewrite pplus_O_p in H10. replace(6 *.D +.D) with (7 *.D) in H10.
  symmetry in H10. apply H10. induction D;unfold point_mult,point_plus.
  f_equal;ring.
  - rewrite <- H5 in H7. replace (1 + 6) with (3 + 4) in H7;try ring.
    apply linear_com1 in H7. unfold vector'. repeat rewrite pmult_minus_distr.
    repeat rewrite pmult_minus_distr in H7.
    assert(3 *.E -.3 *.F +.4 *.E = 4 *.F -.4 *.B +.4 *.E). { rewrite H7;auto. }
    assert(3 *.E -.3 *.F +.4 *.E -.4 *.F = 4 *.F -.4 *.B +.4 *.E -.4 *.F).
    { rewrite H8;auto. }
    assert(3 *.E -.3 *.F +.4 *.E -.4 *.F = 7 *.E -.7 *.F).
    { induction E,F;unfold point_mult,point_minus,point_plus. f_equal;ring. }
    assert(4 *.F -.4 *.B +.4 *.E -.4 *.F = 4 *.E -.4 *.B).
    { induction B,E,F;unfold point_mult,point_minus,point_plus. f_equal;ring. }
    rewrite H10,H11 in H9. apply H9.
  - rewrite pmult_0_l,pplus_O_p;auto.
  - rewrite pmult_l_l_p. replace (2 * 2) with 4;try ring;auto.
  - induction B;unfold point_mult,point_minus. f_equal;ring.
  - induction C;unfold point_mult,point_minus. f_equal;ring.
Qed.

Lemma ex_2_5'_1 : forall A B, A = B -> A -.B = O.
Proof.
  intros. rewrite H, pminus_eq_O; auto.
Qed.

Example ex_2_5' : forall A B D E F,Triangle A B O -> col D B O /\ col E A O 
  -> 3 *.vector' B D = vector' B O -> 3 *.vector' O E = vector' O A -> Inter_p A D B E F
  -> 7 *.vector' F D = vector' A D /\ 7 *.vector' F E = 4 *.vector' B E.
Proof.
  intros. unfold vector' in H1,H2. rewrite pmult_minus_distr,pminus_O_A in H1. 
  repeat rewrite pminus_O in H2.
  assert(3 *.D -.3 *.B +.3 *.B = --B +.3 *.B). { rewrite H1; auto. } 
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H4. 
  replace (--B +.3 *.B) with (2 *.B) in H4. symmetry in H2,H4.
  apply ex_2_5'_1 in H2. apply ex_2_5'_1 in H4. 
  assert(2 *.(2 *.B -.3 *.D) = A -.3 *.E). { rewrite H2,H4,pmult_0_l; auto. }
  rewrite pmult_minus_distr in H5. repeat rewrite pmult_l_l_p in H5. 
  replace (2 * 2) with 4 in H5. replace (2 * 3) with 6 in H5.
  assert(4 *.B -.6 *.D +.6 *.D = A -.3 *.E +.6 *.D).
  { rewrite H5; auto. } 
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H6.
  assert(4 *.B +.3 *.E = A -.3 *.E +.3 *.E +.6 *.D).
  {rewrite H6. rewrite pplus_assoc'. rewrite (pplus_comm (6 *.D) (3 *.E)).
   rewrite pplus_assoc';auto.  }
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H7.
  rewrite <- (pmult_1_p A) in H7. unfold Inter_p in H3.
  assert(1 *.A +.6 *.D = (1 + 6) *.F).
  { apply H3 with (r:=4) (s:=3). repeat split;try rewrite <- H7;try ring.
    auto. apply ex_2_5_3. }
Admitted.

(* 例6 在ΔABC中,F是AB的中点,BG:GC=3:1,BD:DC=1:2,AE:EC=1:4,H是FG、DE的交点.求DH:HE和FH:HG.  *)
Lemma ex_2_6_1 : forall a A B C, a *.(A +.B -.C) = a *.A +.a *.B -.a *.C.
Proof.
  intros. induction A,B,C;unfold point_mult,point_plus,point_minus.
  assert(a * (r + r1 - r3) = a * r + a * r1 - a * r3). { ring. }
  assert(a * (r0 + r2 - r4) = a * r0 + a * r2 - a * r4). { ring. }
  rewrite H,H0;auto.
Qed.

Lemma ex_2_6_2 : 40 + 24 <> 0.
Proof.

Admitted.

Example ex_2_6 : forall B C D E F G H,Triangle O B C -> Midpoint F O B 
  -> vector' B G = 3 *.vector' G C -> 2 *.vector' B D = vector' D C ->
  4 *.vector' O E = vector' E C -> Inter_p F G D E H -> 39 *.vector' D H = 25 *.vector' H E
  /\ 40 *.vector' F H = 24 *.vector' H G.
Proof.
  intros. apply locate_P_2 in H1. rewrite pplus_O_p in H1.
  unfold vector' in H4. rewrite pminus_O in H4.
  assert(4 *.E +.E = C -.E +.E). { rewrite H4;auto. }
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H6.
  rewrite <- pmult_plus_distr_l'' in H6. replace (4 + 1) with 5 in H6;try ring.
  unfold vector' in H3. rewrite pmult_minus_distr in H3.
  assert(2 *.D -.2 *.B +.2 *.B = C -.D +.2 *.B). { rewrite H3;auto. }
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H7.
  assert(2 *.D +.D = C -.D +.D +.2 *.B).
  { rewrite H7. rewrite pplus_assoc'. rewrite (pplus_comm (2 *.B) (D)).
    rewrite pplus_assoc';auto. }
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H8.
  rewrite <- pmult_plus_distr_l'' in H8. replace (2 + 1) with 3 in H8;try ring.
  unfold vector' in H2. rewrite pmult_minus_distr_l in H2.
  assert(G -.B +.3 *.G = 3 *.C -.3 *.G +.3 *.G). { rewrite H2;auto. }
  symmetry in H9. rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H9.
  assert(3 *.C +.B = G -.B +.B +.3 *.G).
  { rewrite H9. rewrite pplus_assoc'. rewrite (pplus_comm (3 *.G) (B)).
    rewrite pplus_assoc';auto. }
  rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H10.
  rewrite (pplus_comm(G) (3 *.G)) in H10.
  rewrite <- pmult_plus_distr_l'' in H10. replace (3 + 1) with 4 in H10;try ring.
  assert(2 *.B = 4 *.F). { rewrite H1. rewrite pmult_l_l_p. 
  replace(2 * 2) with 4. auto. ring. }
  rewrite H11 in H8. rewrite <- H6 in H8.
  assert(3 *.C = 15 *.E). { rewrite <- H6. rewrite pmult_l_l_p. 
  replace(3 * 5) with 15. auto. ring. }
  rewrite H1,H12 in H10.
  assert(13 *.(5 *.E +.4 *.F -.3 *.D) = 6 *.(15 *.E +.2 *.F -.4 *.G)).
  { rewrite H10,H8. repeat rewrite pminus_eq_O. 
    repeat rewrite pmult_0_l;auto. }
  repeat rewrite ex_2_6_1 in H13;try ring. repeat rewrite pmult_l_l_p in H13;try ring.
  replace (13 * 5) with 65 in H13;try ring. replace (13 * 4) with 52 in H13;try ring.
  replace (13 * 3) with 39 in H13;try ring. replace (6 * 15) with 90 in H13;try ring.
  replace (6 * 2) with 12 in H13;try ring. replace (6 * 4) with 24 in H13;try ring.
  assert(65 *.E +.52 *.F -.39 *.D +.39 *.D +.24 *.G -.12 *.F -.65 *.E =
      90 *.E +.12 *.F -.24 *.G +.39 *.D +.24 *.G -.12 *.F -.65 *.E).
  { rewrite H13;auto. }
  assert(65 *.E +.52 *.F -.39 *.D +.39 *.D +.24 *.G -.12 *.F -.65 *.E =
         24 *.G +.40 *.F). 
  { induction D,E,F,G;unfold point_mult,point_plus,point_minus. f_equal;ring. }
  assert(90 *.E +.12 *.F -.24 *.G +.39 *.D +.24 *.G -.12 *.F -.65 *.E =
         25 *.E +.39 *.D).
  { induction D,E,F,G;unfold point_mult,point_plus,point_minus. f_equal;ring. }
  rewrite H15,H16 in H14.
  unfold Inter_p in H5. rewrite pplus_comm in H14.
  assert(40 *.F +.24 *.G = (40 + 24) *.H).
  { apply H5 with (r:=39) (s:=25). rewrite H14,pplus_comm.
    repeat split;try ring;auto. apply ex_2_6_2.  }
  assert(39 *.D +.25 *.E = (39 + 25) *.H).
  { rewrite pplus_comm. rewrite H14 in H17. 
    replace (40 + 24) with (39 + 25) in H17;try ring;auto. }
  split. apply linear_com1' in H18;auto. apply linear_com1' in H17;auto.
Qed.
                           
Example ex11 : forall A B C D,Parallelogram A B C D 
  -> vector' C A = vector' D B /\ vector' B A = vector' D C.
Proof.
  intros. unfold Parallelogram in H. destruct H. split.
  - unfold vector' in * . assert(A -.B +.B = C -.D +.B). 
    { rewrite H; auto. }
    rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H1.
    rewrite H1. induction B,C,D; unfold point_plus,point_minus. f_equal; ring.
  - auto.
Qed.
                           
Example ex12 : forall A B C D E F G H,Midpoint E A B -> Midpoint F C B 
  -> Midpoint G C D -> Midpoint H A D -> E <> H -> Parallelogram E F H G.
Proof.
  intros. apply locate_P_2 in H0. apply locate_P_2 in H1. apply locate_P_2 in H2.
  apply locate_P_2 in H3. assert(A -.C = 2 *.E -.2 *.F).
  { symmetry in H0,H1. rewrite H0,H1. induction A,B,C; unfold point_plus,point_minus.
    f_equal;ring. }
  assert(A -.C = 2 *.H -.2*.G).
  { symmetry in H2,H3. rewrite H2,H3. induction A,C,D; unfold point_plus,point_minus.
    f_equal;ring. }
  assert(2 *.(E -.F) = 2*.(H -.G)). { repeat rewrite pmult_minus_distr. 
  rewrite <- H5. auto. } 
  apply ex_2_2' in H7. unfold Parallelogram. split.
  - unfold vector'; apply H7. - apply H4.
  - pose proof Rlt_0_1. pose proof H9. apply Rplus_lt_0_compat with (r1:=1) in H9.
    replace 2 with (1 + 1); try ring. apply Rlt_not_eq in H9;auto. auto.
Qed.
                           
                       

