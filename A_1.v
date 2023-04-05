Require Export A_0.
Require Import Base.
Open Scope R_scope.

(* 性质1 若B=λA，则O，A，B共线，且向量OB=λ*向量OA。 *)
Theorem point_col :
  forall A B λ, λ <> 0 -> B = λ *.A -> vector' O B = λ *.vector' O A 
  /\ col B O A.
Proof.
  intros; split.
  - unfold point_mult; rewrite H0. induction A; simpl.
  repeat(rewrite Rminus_0_r);auto.
  - unfold col. left. exists λ; rewrite H0.
    unfold point_mult; induction A; simpl. 
    repeat(rewrite Rminus_0_r);auto.
Qed.

(* 性质2 (1)若A+B=P,则AOBP为平行四边形。 *)
Theorem locate_P_1 :
  forall A B P, A<>O /\ B<>O /\ A<>B -> P = A +.B -> Parallelogram A O P B.
Proof.
  intros; unfold Parallelogram; split.
  - unfold point_plus in H0; unfold vector', point_minus; 
    induction A, B, P; simpl. 
    repeat (rewrite Rminus_0_r). injection H0 as H1 H2. rewrite H1, H2. 
    repeat (rewrite pm_assoc'); rewrite (Rminus_eq_0 r1),(Rminus_eq_0 r2).
    repeat (rewrite Rplus_0_r);auto.
  - destruct H as [H1[H2 H3]]; destruct (classical(A=P)); auto. 
    rewrite H in H0. induction A, B, P; unfold point_plus in H0; 
    unfold O in H1,H2; injection H0 as H4 H5.
    destruct H2. symmetry in H4, H5; apply Rplus_0_r_uniq in H4; 
    apply Rplus_0_r_uniq in H5.
    rewrite H4, H5; auto.
Qed.

Theorem locate_P_1' :
  forall A B P, Parallelogram A O P B -> P = A +.B.
Proof.
  intros. unfold Parallelogram in H. destruct H. unfold vector' in H. 
  rewrite pminus_O in H. rewrite H. 
  induction P, B. unfold point_plus, point_minus. 
  repeat (rewrite minus_eq); auto.
Qed.

(* 性质2 (2)若A+B=2*P，则P为AB中点。 *)
Lemma Midpoint_tran :
forall A B P, A +.B = 2 *.P <-> (A +.B) /.2 = P.
Proof.
  split; intros.
  - rewrite H. induction P; unfold point_mult, point_divR. rewrite Rmult_comm. 
    rewrite (Rmult_comm 2 r0). unfold Rdiv. rewrite Rmult_assoc. 
    rewrite (Rmult_assoc r0). repeat (rewrite Rinv_r, Rmult_1_r). 
    rewrite (Rmult_1_r r0). auto. auto.
  - symmetry in H. rewrite H. induction A, B; 
    unfold point_plus, point_mult, point_divR.
    rewrite Rmult_comm. rewrite (Rmult_comm 2). unfold Rdiv. 
    rewrite Rmult_assoc. rewrite (Rmult_assoc (r0 + r2)). 
    rewrite (Rmult_comm (/ 2)). repeat (rewrite Rinv_r, Rmult_1_r). 
    rewrite (Rmult_1_r (r0 + r2)). auto. auto.
Qed.

Theorem locate_P_2 :
  forall A B P, A +.B = 2 *.P <-> Midpoint P A B.
Proof.
  split; intros.
  - unfold Midpoint. induction A, B, P; unfold vector', point_minus; 
    unfold point_mult, point_plus in H. 
    injection H as H1 H2. rewrite Rmult_2_r in H1, H2. 
    apply Rplus_minus' in H1; apply Rplus_minus' in H2.
    assert (r3 - r1 = r - r3). 
    { symmetry; apply Rplus_minus'; rewrite pm_assoc; 
    rewrite Rplus_comm; apply H1. }
    assert (r4 - r2 = r0 - r4). 
    { symmetry; apply Rplus_minus'; rewrite pm_assoc; 
    rewrite Rplus_comm; apply H2. }
  rewrite H, H0; auto.
  - induction A, B, P; unfold Midpoint, vector', point_minus in H; 
    unfold point_plus, point_mult.
    injection H as H1 H2. 
    assert (r + r1 = r3 + r3). 
    { apply Rplus_minus' in H1. symmetry in H1. rewrite test2' in H1.
      apply test3 in H1. rewrite test4 in H1. auto. }
    assert (r0 + r2 = r4 + r4). 
    { apply Rplus_minus' in H2. symmetry in H2. rewrite test2' in H2.
      apply test3 in H2. rewrite test4 in H2. auto. }
    repeat (rewrite Rmult_2_r). rewrite H, H0; auto.
Qed.

(* 性质2 (3)若A+B=3*P，则P是▲ABO的重心。 *)
Theorem locate_P_3 :
forall A B P, A +.B = 3 *.P -> focus P A B O.
Proof.
  intros. unfold focus, v0, vector'. induction A, B, P; simpl. 
  repeat (rewrite Rminus_0_l);repeat (rewrite Ropp_0). 
  unfold point_mult, point_plus in H. 
  injection H as H1 H2. rewrite Rmult_3_r in H1, H2.
  apply Rplus_minus' in H1; apply Rplus_minus' in H2.
  assert (0 = r + r1 - r3 - r3 - r3). 
  { apply Rplus_minus'; symmetry; rewrite Rplus_0_r; rewrite test2 in H1; apply H1. }
  assert (0 = r0 + r2 - r4 - r4 - r4). 
  { apply Rplus_minus'; symmetry; rewrite Rplus_0_r; rewrite test2 in H2; apply H2. }
  symmetry in H, H0.
  assert (r + r1 - r3 - r3 - r3 = r - r3 + (r1 - r3) + - r3). {ring. }
  assert (r0 + r2 - r4 - r4 - r4 = r0 - r4 + (r2 - r4) + - r4). {ring. }
  symmetry in H3, H4; rewrite H3, H4; rewrite H, H0; auto.
Qed.

Theorem locate_P_3' :
forall A B P, focus P A B O -> A +.B = 3 *.P.
Proof.
  intros. unfold focus in H. unfold vector', v0 in H; unfold vector' in H.
  rewrite pminus_O in H. induction A, B, P. unfold point_minus, point_plus, O in H.
  unfold point_plus, point_mult. injection H as H H0. repeat (rewrite Rmult_3_r).
  assert (r - r3 + (r1 - r3) + (0 - r3) = r + r1 - (r3 + r3 + r3)). {ring. }
  assert (r0 - r4 + (r2 - r4) + (0 - r4) = r0 + r2 - (r4 + r4 + r4)). {ring. }
  rewrite H1 in H; rewrite H2 in H0. 
  apply Rminus_diag_uniq in H; apply Rminus_diag_uniq in H0.
  rewrite H, H0; auto.
Qed.

(* 性质3 两点差为向量，即 B-A=t*P=vAB. *)
Definition cons A B := A<>O /\ B<>O /\ A<>B -> exists t P, B -.A = t *.P.
(* 当t=1时，OABP为平行四边形。 *)
Theorem switch_1 : 
  forall A B P, A<>O /\ B<>O /\ A<>B -> B -.A = P -> Parallelogram B A P O.
Proof.
  intros. unfold Parallelogram. split.
  - unfold vector'. rewrite pminus_O. auto.
  - destruct H as [H1[H2 H3]]. destruct (classical(B = P));auto.
    rewrite H in H0. induction A, B, P. unfold point_minus, point_mult in H0;
    injection H0 as H4 H5; unfold O in H1,H2.
    destruct H1. apply Rminus_r_0 in H4; apply Rminus_r_0 in H5. rewrite H4, H5; auto.
Qed.

Theorem switch_1' :
  forall A B P, Parallelogram B A P O -> B -.A = P.
Proof.
  intros. unfold Parallelogram in H. destruct H. unfold vector' in H. 
  rewrite pminus_O in H; auto.
Qed.

(* 性质4 两点线性组合u*A+v*B=t*P的意义：(1)当t=u+v时，令u*A+v*B=(u+v)*F，可改写为u*(A-F)=v*(F-B). *)
Theorem linear_com1 :
forall A B P u v,u *.A +.v *.B = (u + v) *.P -> u *.(A -.P) = v *.(P -.B).
Proof.
  intros. 
  induction A,B,P; unfold point_minus, point_mult; 
  unfold point_plus, point_mult in H. injection H as H1 H2. 
  rewrite Rmult_plus_distr_r in H1, H2.
  rewrite Rplus_comm in H1; apply Rplus_minus' in H1. 
  assert (u * r - u * r3 = v * r3 - v * r1). 
  { apply Rplus_minus'; rewrite pm_assoc; apply H1. }
  rewrite Rplus_comm in H2; apply Rplus_minus' in H2.
  assert (u * r0 - u * r4 = v * r4 - v * r2). 
  { apply Rplus_minus'; rewrite pm_assoc; apply H2. }
  repeat (rewrite Rmult_minus_distr_l). rewrite H, H0; auto.
Qed.

Theorem linear_com1' :
forall A B P u v,u *.A +.v *.B = (u + v) *.P
  -> u *.vector' A P = v *.vector' P B.
Proof.
  intros; unfold vector'. 
  induction A,B,P; unfold point_minus, point_mult; 
  unfold point_plus, point_mult in H. injection H as H1 H2. rewrite Rmult_plus_distr_r in H1, H2.
  rewrite Rplus_comm in H1; apply Rplus_minus' in H1.
  assert (u * r - u * r3 = v * r3 - v * r1). 
  { apply Rplus_minus'; rewrite pm_assoc; apply H1. }
  rewrite Rplus_comm in H2; apply Rplus_minus' in H2.
  assert (u * r0 - u * r4 = v * r4 - v * r2). 
  { apply Rplus_minus'; rewrite pm_assoc; apply H2. }
  assert (- (u * r - u * r3) = - (v * r3 - v * r1)). { rewrite H; auto. }
  assert (- (u * r0 - u * r4) = - (v * r4 - v * r2)). { rewrite H0; auto. }
  repeat (rewrite minus_eq1 in H3, H4). repeat (rewrite Rmult_minus_distr_l). 
  rewrite H3, H4; auto.
Qed.
  
(* 当t=u+v时，令u*A+v*B=(u+v)*F，此时F在直线AB上。 *)
Theorem linear_com2 : 
forall A B P u v,u <> 0 /\ v <> 0 -> u *.A +.v *.B = (u + v) *.P
  -> col A P B.
Proof.
  intros. destruct H. apply linear_com1 in H0. unfold col,vector'. left. 
  exists (-v/u); induction A, P, B.
  unfold point_minus, point_mult; unfold point_minus, point_mult in H. 
  injection H0 as H2 H3. unfold Rdiv; repeat (rewrite Rmult_assoc); 
  repeat (rewrite (Rmult_comm (/ u))); repeat (rewrite Rmult_assoc').
  assert (- v * (r3 - r1) = v * (r1 - r3)). { ring. }
  assert (- v * (r4 - r2) = v * (r2 - r4)). { ring. }
  rewrite H0, H4; symmetry in H2, H3; rewrite H2, H3. repeat (rewrite Rinv_r_simpl_m).
  split; auto.
  - assert (- v <> 0). { apply Ropp_neq_0_compat in H1; apply H1. }
    assert (/ u <> 0). { apply Rinv_neq_0_compat in H; apply H. }
    apply Rmult_integral_contrapositive_currified; auto.
  - auto.
  - auto.
Qed.

Theorem linear_com2' :
forall A B P,col A P B -> exists u v,u *.A +.v *.P = (u + v) *.B.
Proof.
  intros. unfold col in H. destruct H. destruct H. unfold vector' in H.
  - destruct H. exists 1,(-(1-x)). rewrite pmult_1_p. 
    assert(A +.- (1-x) *.P = A -.(1-x) *.P). 
    { induction A,P;unfold point_plus,point_mult,point_minus. 
      assert(r + - (1 - x) * r1 = r - (1 - x) * r1). { ring. }
      assert(r0 + - (1 - x) * r2 = r0 - (1 - x) * r2). { ring. } rewrite H1,H2;auto. }
    rewrite H1. rewrite rplus_minus_tran.
    rewrite pmult_minus_distr in H0. 
    assert(A -.P +.x *.P = x *.B -.x *.P +.x *.P). { rewrite H0; auto. }
    symmetry in H2. rewrite pplus_minus_assoc',pminus_eq_O,pminus_O in H2.
    symmetry in H2. rewrite pplus_minus_assoc' in H2.
    assert(P -.x *.P = (1 - x) *.P). 
    { rewrite pmult_minus_distr'. rewrite pmult_1_p. auto. }
    rewrite H3 in H2. replace(1 - (1 - x)) with x.
    apply H2. ring.
  - destruct H. exists 0,0. repeat rewrite pmult_0_p.
    rewrite pplus_O_p. replace (0+0) with 0. rewrite pmult_0_p.
    auto. ring.
    destruct H. exists 1,0. rewrite pmult_0_p,pmult_1_p,pplus_O_p'.
    replace (1+0) with 1. rewrite pmult_1_p. apply H. ring.
    exists 0,1. rewrite pmult_0_p,pmult_1_p,pplus_O_p.
    replace (0+1) with 1. rewrite pmult_1_p. rewrite H;auto. ring.
Qed.

(* 性质4 两点线性组合u*A+v*B=t*P的意义：(2)u*A+v*B=(u+v)*F,一般来说，P是直线OF上的点。 *)
Theorem linear_com3 :
forall A B P F u v t,(u + v) <> 0 /\ t <> 0 -> u *.A +.v *.B = t *.P 
  /\ u *.A +.v *.B = (u+v) *.F -> col P O F.
Proof.
  intros. destruct H0. rewrite H0 in H1. unfold col;left. exists ((u+v)/t). 
  unfold vector', O; induction A, B, P, F; simpl. 
  unfold point_mult, point_plus in H0, H1. repeat(rewrite Rminus_0_r);
  unfold Rdiv; repeat (rewrite Rmult_assoc); repeat (rewrite (Rmult_comm (/ t))); 
  repeat (rewrite Rmult_assoc').
  injection H1 as H2 H3; symmetry in H2, H3; rewrite H2, H3. repeat (rewrite Rinv_r_simpl_m).
  destruct H. split; auto.
  - assert (/ t <> 0). { apply Rinv_neq_0_compat in H1; apply H1. }
    apply Rmult_integral_contrapositive_currified; auto.
  - tauto. 
  - tauto. 
Qed.

(* 性质5 两线相交u*A+v*B=r*C+s*D的表示：(1)当u+v=r+s≠0时，令(u+v)*F=u*A+v*B=r*C+s*D=(r+s)*G，
则等式表示F=G为直线AB、CD之交点. *)
Definition Inter A B C D := A <> B /\ C <> D /\ exists u v r s, u *.A +.v *.B = r *.C +.s *.D. 

Definition Inter_p A B C D X := forall u v r s, u *.A +.v *.B = r *.C +.s *.D /\ u + v = r + s
  /\ u + v <> 0 -> u *.A +.v *.B = (u + v) *.X.

(* 性质5 两线相交u*A+v*B=r*C+s*D的表示：(2)(u+v)*F=u*A+v*B=r*C+s*D=(r+s)*G，一般情形表示O、G、F共线。 *)
Theorem TL_relate2 :
forall A B C D F G u v r s, u +v <>0 /\ r+s <> 0 -> u *.A +.v *.B = r *.C +.s *.D 
  -> (u + v) *.F = u *.A +.v *.B /\ r *.C +.s *.D = (r + s) *.G
  -> col G O F.
Proof.
  intros. destruct H,H1. unfold col. left. exists ((u+v)/(r+s)). rewrite H0 in H1. 
  symmetry in H1. rewrite H1 in H3.
  induction A,B,C,D,F,G. unfold O, vector', point_mult; simpl. 
  repeat(rewrite Rminus_0_r). unfold Rdiv. unfold point_mult in H3. injection H3 as H4 H5.
  repeat (rewrite Rmult_assoc); repeat (rewrite (Rmult_comm (/ (r+s)))); repeat (rewrite Rmult_assoc').
  rewrite H4, H5. repeat (rewrite Rinv_r_simpl_m).
  split; auto.
  - assert (/ (r + s) <> 0). { apply Rinv_neq_0_compat in H2; apply H2. }
    apply Rmult_integral_contrapositive_currified; auto.
  - auto.
  - auto.
Qed.

Lemma Midpoint_p : forall A B, Midpoint A O B -> B = 2 *.A.
Proof.
  intros. unfold Midpoint in H. induction A, B. unfold vector', O, point_minus in H; unfold point_mult.
  injection H as H1 H2. rewrite Rminus_0_l in H1, H2. 
  apply Rplus_minus' in H1. apply Rplus_minus' in H2. rewrite tt in H1, H2. 
  apply Ropp_eq_compat in H1. apply Ropp_eq_compat in H2. repeat (rewrite Ropp_involutive in H1,H2).
  repeat (rewrite Rmult_2_r). rewrite H1, H2; auto.
Qed.

Lemma Midpoint_p' : forall A B, B = 2 *.A -> Midpoint A O B.
Proof.
  intros. unfold Midpoint. unfold vector'. rewrite pminus_O_A. rewrite H.
  induction A. unfold point_inverse, point_minus, point_mult.
  repeat (rewrite Rmult_2_r, test2, Rminus_eq_0, Rminus_0_l); auto.
Qed.  

(* 性质6 A · B = B · A，且数量积对加法有分配律。 *)
Lemma Pmagn_comm : forall A B,A ·.B = B ·.A.
Proof.
  intros. induction A, B; unfold point_magn; ring.
Qed.

Lemma Pmagn_plus_distr' : forall A B C,(A +.B) ·.C = A ·.C + B ·.C.
Proof. 
  intros. induction A, B, C; unfold point_plus, point_magn; ring.
Qed.

(* 性质7 (A-B)·(C-D)=向量AB·向量CD。*)
Lemma Pminus_magn_v : forall A B C D,(A -.B) ·.(C -.D) = vector' A B ·.vector' C D.
Proof.
  intros. induction A, B, C, D; unfold vector', point_minus, point_magn; ring.
Qed.

(* 性质8 AB=-BA. *)
Lemma Oprod_comm : forall A B,A /pB = -- (B /pA).
Proof.
  intros. induction A, B; unfold point_Oprod, point_minus.
  unfold point_inverse.
  assert (r1 - r = - (r - r1)). { ring. }
  assert (r2 - r0 = - (r0 - r2)). { ring. }
  rewrite H; rewrite H0; auto.
Qed.

(* 性质9 若u*A+v*B=(u+v)*C，则有u*AP+v*BP=(u+v)*CP，u*PA+v*PB=(u+v)*PC． *)
Lemma Oprod_plus_distr : forall A B C P u v,u *.A +.v *.B = (u + v) *.C
  -> u *.(P /pA) +.v *.(P /pB) = (u+v) *.(P /pC).
Proof.
  intros. unfold point_Oprod. repeat (rewrite pmult_minus_distr).
  symmetry in H. rewrite H. 
  induction A, B, P. unfold point_mult, point_plus, point_minus.
  assert (u * r - u * r3 + (v * r1 - v * r3) = u * r + v * r1 - (u + v) * r3). { ring. }
  assert (u * r0 - u * r4 + (v * r2 - v * r4) = u * r0 + v * r2 - (u + v) * r4). { ring. }
  rewrite H0, H1; auto.
Qed.

Lemma Oprod_plus_distr' : forall A B C P u v,u *.A +.v *.B = (u + v) *.C
  -> u *.(A /pP) +.v *.(B /pP) = (u+v) *.(C /pP).
Proof.
  intros. unfold point_Oprod. repeat (rewrite pmult_minus_distr).
  symmetry in H. rewrite H. 
  induction A, B, P. unfold point_mult, point_plus, point_minus.
  assert (u * r3 - u * r + (v * r3 - v * r1) = (u + v) * r3 - (u * r + v * r1)). { ring. }
  assert (u * r4 - u * r0 + (v * r4 - v * r2) = (u + v) * r4 - (u * r0 + v * r2)). { ring. }
  rewrite H0, H1; auto.
Qed.

(* 等式“u*A+v*B=(u+v)*C两端同用B做外积，则得u*AB=(u+v)*CB. *)
Lemma Oprod_B : forall A B C u v, u *.A +.v *.B = (u + v) *.C
  -> u *.(A /pB) = (u + v) *.(C /pB).
Proof.
  intros. apply Oprod_plus_distr' with (P := B) in H.
  unfold point_Oprod. unfold point_Oprod in H.
  rewrite pminus_eq_O in H. rewrite pmult_0_l in H.
  rewrite pplus_O_p' in H; auto.
Qed.

(* 等式“u*A+v*B=(u+v)*C两端同用C做外积，则得u*AC+v*BC=0，即u*AC=v*CB． *)
Lemma Oprod_C : forall A B C u v, u *.A +.v *.B = (u + v) *.C
  -> u *.(A /pC) = v *.(C /pB).
Proof.
  intros. apply Oprod_plus_distr' with (P := C) in H.
  unfold point_Oprod. unfold point_Oprod in H.
  rewrite pminus_eq_O in H. rewrite pmult_0_l in H.
  induction A, B, C; unfold point_mult, point_minus, point_plus in H.
  unfold point_mult, point_minus. injection H as H H1.
  rewrite Rplus_comm in H, H1. apply Rplus_opp_r_uniq in H. apply Rplus_opp_r_uniq in H1.
  assert (- (v * (r3 - r1)) = v * (r1 - r3)). { ring. }
  assert (- (v * (r4 - r2)) =  v * (r2 - r4)). { ring. }
  rewrite H0 in H; rewrite H2 in H1. rewrite H, H1; auto.
Qed.

(* 性质10 若u*A+v*B=r*C，因原点O坐标为零，故u*A+v*B=r*C+(u+v—r)*O，这时可以用分配律，注意到P=OP=-PO，得
u*AP+v*BP—r*CP+(u+v-r)*P，u*PA+v*PB—r*PC-(u+v-r)*P． *)
Lemma Oprod_plus_distr_ex : forall A B C P u v r, u *.A +.v *.B = r *.C
  -> u *.A +.v *.B = r *.C +.(u + v - r) *.O
  -> u *.(A /pP) +.v *.(B /pP) = r *.(C /pP) +.(u + v - r) *.P.
Proof.
  intros.
  assert ((u + v - r) *.P = (u + v - r) *.(O /pP)). { rewrite Oprod_O_l_mult; auto. }
  rewrite H1. unfold point_Oprod. repeat (rewrite pmult_minus_distr).
  induction A, B, C, P. unfold point_mult, point_minus, point_plus, O.
  unfold point_mult, point_plus, O in H0; injection H0 as H0 H2.
  assert (u * r6 - u * r0 + (v * r6 - v * r2) = (u + v) * r6 - (u * r0 + v * r2)). { ring. }
  assert (u * r7 - u * r1 + (v * r7 - v * r3) = (u + v) * r7 - (u * r1 + v * r3)). { ring. }
  assert (r * r6 - r * r4 + ((u + v - r) * r6 - (u + v - r) * 0) = 
              (u + v) * r6 - (r * r4 + (u + v - r) * 0)). { ring. } 
  assert (r * r7 - r * r5 + ((u + v - r) * r7 - (u + v - r) * 0) =
              (u + v) * r7 - (r * r5 + (u + v - r) * 0)). { ring. }
  rewrite H3, H4, H5, H6, H0, H2; auto.
Qed.

Lemma Oprod_plus_distr_ex' : forall A B C P u v r, u *.A +.v *.B = r *.C
  -> u *.A +.v *.B = r *.C +.(u + v - r) *.O
  -> u *.(P /pA) +.v *.(P /pB) = r *.(P /pC) -.(u + v - r) *.P.
Proof.
  intros.
  assert ((u + v - r) *.P = -- (u + v - r) *.(P /pO)). {rewrite Oprod_O_l'_mult; auto. }
  rewrite H1.  unfold point_Oprod. repeat (rewrite pmult_minus_distr).
  induction A, B, C, P. unfold point_mult, point_minus, point_plus, point_inverse, O.
  unfold point_mult, point_plus, O in H0; injection H0 as H0 H2.
  assert (u * r0 - u * r6 + (v * r2 - v * r6) = u * r0 + v * r2 - (u + v) * r6). { ring. }
  assert (u * r1 - u * r7 + (v * r3 - v * r7) = u * r1 + v * r3 - (u + v) * r7). { ring. }
  assert (r * r4 - r * r6 - - ((u + v - r) * 0 - (u + v - r) * r6) =
              r * r4 + (u + v - r) * 0 - (u + v) * r6). { ring. }
  assert (r * r5 - r * r7 - - ((u + v - r) * 0 - (u + v - r) * r7) = 
              r * r5 + (u + v - r) * 0 - (u + v) * r7). { ring. }
  rewrite H3, H4, H5, H6, H0, H2; auto.
Qed.

(* 特款 (1)若A=r*C，则AP=rCP+(1-r)*P且PA=r*PC-(1-r)*P. *)
Lemma Oprod_plus_distr_sp1 : forall A C P r, A = r *.C -> 
  A /pP = r *.(C /pP) +.(1 - r) *.P /\ P /pA = r *.(P /pC) -.(1 - r) *.P.
Proof.
  intros. unfold point_Oprod. repeat (rewrite pmult_minus_distr).
  induction A, C, P; unfold point_minus, point_mult, point_plus.
  unfold point_mult in H. injection H as H0 H. split.
  - assert (r * r4 - r * r2 + (1 - r) * r4 = r4 - r * r2).
    { ring. }
    assert (r * r5 - r * r3 + (1 - r) * r5 = r5 - r * r3).
    { ring. }
    rewrite H0, H, H1, H2; auto.
  - assert (r * r2 - r * r4 - (1 - r) * r4 = r * r2 - r4).
    { ring. }
    assert (r * r3 - r * r5 - (1 - r) * r5 = r * r3 - r5).
    { ring. }
    rewrite H0, H, H1, H2; auto.
Qed.

(* 特款 (2)若u*A=r*C，则u*AP=r*CP+(u—r)*P且u*PA=r*PC-(u-r)*P． *)
Lemma Oprod_plus_distr_sp2 : forall A C P u r, u *.A = r *.C ->
  u *.(A /pP) = r *.(C /pP) +.(u - r) *.P /\ u *.(P /pA) = r *.(P /pC) -.(u - r) *.P.
Proof.
  intros. unfold point_Oprod. repeat (rewrite pmult_minus_distr).
  induction A, C, P; unfold point_minus, point_mult, point_plus.
  unfold point_mult in H. injection H as H0 H. split.
  - assert (r * r4 - r * r2 + (u - r) * r4 = u * r4 - r * r2).
    { ring. }
    assert (r * r5 - r * r3 + (u - r) * r5 = u * r5 - r * r3).
    { ring. }
    rewrite H0, H, H1, H2; auto.
  - assert (r * r2 - r * r4 - (u - r) * r4 = r * r2 - u * r4).
    { ring. }
    assert (r * r3 - r * r5 - (u - r) * r5 = r * r3 - u * r5).
    { ring. }
    rewrite H0, H, H1, H2; auto.
Qed.

(* 性质11 ABC=BCA=CAB=-ACB=-BAC=-CBA.其直观的几何意义是：在右手坐标系中，三角形三顶点A、B、C顺序为
反时针方向则ABC>0，否则ABC<0；若A、B、C共线则ABC=0． *)
Lemma pprod_order : forall A B C, point_3prod A B C = point_3prod B C A /\ point_3prod B C A =
  point_3prod C A B /\ point_3prod C A B = - point_3prod A C B /\ point_3prod A C B = point_3prod B A C 
  /\ point_3prod B A C = point_3prod C B A.
Proof.
  intros. induction A, B, C; unfold point_3prod. repeat split; ring.
Qed.

Lemma pprod_col : forall A B C, col A B C -> point_3prod A B C = 0.
Proof.
  intros. unfold col in H. induction A,B,C. unfold point_3prod. destruct H.
  - destruct H as [X[]]. unfold vector',point_mult,point_minus in H0.
    inversion H0. assert(r - r1 + r1 = X * (r3 - r1) + r1). { rewrite H2;auto. }
    rewrite minus_eq in H1.
    assert(r0 - r2 + r2 = X * (r4 - r2) + r2). { rewrite H3;auto. } 
    rewrite minus_eq in H4. rewrite H1,H4. ring.
  - destruct H as [H|[H|H]]; inversion H; subst; ring.
Qed.
   
(* 性质12 若u*A+v*B=(u+v)*C，则有u*APQ+v*BPQ=(u+v)*CPQ；因而易知，u*PAQ+v*PBQ=(u+v)PCQ，u*PQA+v*PQB=(u+v)*PQC．*)
Lemma pprod_distr_eq1 : forall A B C P Q u v, u *.A +.v *.B = (u + v) *.C 
  -> u * point_3prod A P Q + v * point_3prod B P Q = (u + v) * point_3prod C P Q.
Proof.
  intros. induction A, B, C, P, Q. unfold point_3prod.
  unfold point_mult, point_plus in H. injection H as H H0.
  assert ((u + v) * (r3 * r6 + r5 * r8 + r7 * r4 - r3 * r8 - r5 * r4 - r7 * r6)
  = (u + v) * r3 * (r6 - r8) + (u + v) * r4 * (r7 - r5) + (u + v) * (r5 * r8 - r7 * r6)).
  { ring. }
  symmetry in H, H0; rewrite H1, H, H0; ring.
Qed.

Lemma pprod_distr_eq2 : forall A B C P Q u v, u *.A +.v *.B = (u + v) *.C 
  -> u * point_3prod P A Q + v * point_3prod P B Q = (u + v) * point_3prod P C Q.
Proof.
  intros. induction A, B, C, P, Q. unfold point_3prod.
  unfold point_mult, point_plus in H. injection H as H H0.
  assert ((u + v) * (r5 * r4 + r3 * r8 + r7 * r6 - r5 * r8 - r3 * r6 - r7 * r4) 
  = (u + v) * r3 * (r8 - r6) + (u + v) * r4 *(r5 - r7) + (u + v) * (r7 * r6 - r5 * r8)).
  { ring. }
  symmetry in H, H0; rewrite H1, H, H0; ring.
Qed.

Lemma pprod_distr_eq3 : forall A B C P Q u v, u *.A +.v *.B = (u + v) *.C 
  -> u * point_3prod P Q A + v * point_3prod P Q B = (u + v) * point_3prod P Q C.
Proof.
  intros. induction A, B, C, P, Q. unfold point_3prod.
  unfold point_mult, point_plus in H. injection H as H H0.
  assert ((u + v) * (r5 * r8 + r7 * r4 + r3 * r6 - r5 * r4 - r7 * r6 - r3 * r8)
  = (u + v) * r3 * (r6 - r8) + (u + v) * r4 * (r7 - r5) + (u + v) * (r5 * r8 - r7 * r6)).
  { ring. }
  symmetry in H, H0; rewrite H1, H, H0; ring.
Qed.

(* 当“u+v=r+s≠0时，等式(u+v)*F=u*A+v*B=r*C+s*D同用CD做外积得u*ACD+v*BCD=0，即ACD/BCD=-v/u=向量AF/向量BF，
这就是共边定理. *)
Lemma pprod_distr_uneq : forall A B C D F u v r s, u + v = r + s /\ u + v <> 0 -> 
  (u + v) *.F = u *.A +.v *.B /\ (u + v) *.F = r *.C +.s *.D 
  -> u * point_3prod A C D + v * point_3prod B C D = 0.
Proof.
  intros. destruct H0, H.
  assert ((u + v) * point_3prod F C D = u * point_3prod A C D + v * point_3prod B C D).
  { symmetry. apply (pprod_distr_eq1 A B F C D u v). auto. } 
  assert ((u + v) * point_3prod F C D = r * point_3prod C C D + s * point_3prod D C D).
  { rewrite H. symmetry. apply (pprod_distr_eq1 C D F C D r s). symmetry in H; rewrite H; auto. }
  assert (r * point_3prod C C D + s * point_3prod D C D = 0).
  { induction C, D. unfold point_3prod. ring. }
  rewrite H5 in H4. symmetry in H3; rewrite H3; auto.
Qed.

(* 性质13 u*A+v*B=rC，原点为O，则有u*APQ+v*BPQ=r*CPQ+(u+v-r)*OPQ． *)
Lemma  pprod_distr_uneq_trim : forall A B C P Q u v r, u *.A +.v *.B = r *.C
  -> u * point_3prod A P Q + v * point_3prod B P Q = r * point_3prod C P Q + (u + v - r) * point_3prod O P Q.
Proof.
  intros. induction A, B, C, P, Q. unfold point_3prod, O. unfold point_mult, point_plus in H.
  injection H as H H0.
  assert (r * (r4 * r7 + r6 * r9 + r8 * r5 - r4 * r9 - r6 * r5 - r8 * r7) = 
  r * r4 * (r7 - r9) + r * r5 * (r8 - r6) + r * (r6 * r9 - r8 * r7)). { ring. }
  symmetry in H, H0. rewrite H, H0 in H1. rewrite H1; ring.
Qed.

(* 特款：若原点在直线PQ上，则附加的配平项为0，相当于分配律成立． *)  
Lemma  pprod_distr_uneq_trim' : forall A B C P Q u v r, u *.A +.v *.B = r *.C -> col O P Q
  -> u * point_3prod A P Q + v * point_3prod B P Q = r * point_3prod C P Q.
Proof.
  intros.
  assert(u * point_3prod A P Q + v * point_3prod B P Q = r * point_3prod C P Q + (u + v - r) * point_3prod O P Q).
  { apply pprod_distr_uneq_trim. auto. }
  assert(point_3prod O P Q = 0). { apply pprod_col. auto. } rewrite H2 in H1. 
  rewrite Rmult_0_r,Rplus_0_r in H1. auto.
Qed.
 
(* 性质14 i(iA)=-A． *)
Lemma point_mult_ii : forall A, i*.(i*.A) = --A.
Proof.
  intros. induction A; unfold point_mult_i, point_inverse; auto.
Qed.

(* 性质15 iA·A=0． *)
Lemma point_mult_i_inprod : forall A, (i*.A) ·.A = 0.
Proof.
  intros. induction A; unfold point_mult_i, point_magn; ring.
Qed.

(* 性质16 B=(u,v)时，有iA·B=(-y,x)·(u,v)=v*x-u*y=-A·iB． *)
Lemma point_mult_i_opp : forall A B, (i*.A) ·.B = -(A ·.(i*.B)).
Proof.
  intros. induction A, B; unfold point_mult_i, point_magn; ring.
Qed.

(* 性质17 复数乘点的几何意义：若在笛卡尔坐标系中，A=(x,y)而复数α=u+vi．记r=|α|=√u²+v²且θ为a=u+vi
的幅角主值，即满足α=rcosθ+irsinθ且0≤θ<2π，则按复数乘法的几何意义，将点rA绕原点反时针旋转θ弧度即得αA． 
  通常记e^iθ=cosθ+isinθ，则A=(x,y)绕原点反时针旋转毋弧度得到的点可简单地记作e^iθA，
  即e^iθA=(xcosθ-ysinθ，ycosθ+xsinθ)．*)
Definition exp(theta : R) : Complex :=
 [cos(theta),sin(theta)].

(* 性质18 A绕点B反时针旋转θ弧度得到的点为B+e^iθ(A—B)． *)
Definition ccw A B theta := B +.exp theta */c(A -.B).

(* 性质19 复数乘点的运算法则:(α+β)A=αA+βA,α(A+B)=αA+αB,α(βA)=(αβ)A=β(αA)(α,β为复数)． *)
Lemma Complex_mult_ppdistr : forall c1 c2 A, (c1 +/C c2) */c A = c1 */cA +.c2 */cA.
Proof.
  intros. induction c1, c2, A. unfold Cplus, point_mult_complex, point_plus, point_mult,
  point_mult_i. 
  assert ((r + r1) * r3 + (r0 + r2) * - r4 = r * r3 + r0 * - r4 +(r1 * r3 + r2 * - r4)).
  { ring. }
  assert ((r + r1) * r4 + (r0 + r2) * r3 = r * r4 + r0 * r3 + (r1 * r4 + r2 * r3)).
  { ring. }
  rewrite H, H0; auto.
Qed.

Lemma Complex_mult_pcdistr : forall c A B, c */c(A +.B) = c */cA +.c*/cB.
Proof.
  intros. induction c, A, B. unfold point_mult_complex, point_plus. unfold point_mult_i, point_mult.
  assert (r * (r1 + r3) + r0 * - (r2 + r4) = r * r1 + r0 * - r2 + (r * r3 + r0 * - r4)).
  { ring. }
  assert (r * (r2 + r4) + r0 * (r1 + r3) = r * r2 + r0 * r1 + (r * r4 + r0 * r3)).
  { ring. }
  rewrite H, H0; auto.
Qed.

Lemma Complex_mult_passoc : forall c1 c2 A, c1 */c(c2 */cA) = (c1 */C c2) */cA /\
  c1 */c(c2 */cA) = c2 */c(c1*/cA) /\ (c1 */C c2) */cA = c2 */c(c1*/cA).
Proof.
  intros. induction c1, c2, A. repeat split; unfold point_mult_complex, 
  point_mult_i, point_mult, point_plus, Cmult.
  - assert (r * (r1 * r3 + r2 * - r4) + r0 * - (r1 * r4 + r2 * r3) = (r * r1 - r0 * r2) * r3 +
    (r * r2 + r0 * r1) * - r4). { ring. }
    assert (r * (r1 * r4 + r2 * r3) + r0 * (r1 * r3 + r2 * - r4) = (r * r1 - r0 * r2) * r4 +
    (r * r2 + r0 * r1) * r3). { ring. }
    rewrite H, H0; auto.
  - assert (r * (r1 * r3 + r2 * - r4) + r0 * - (r1 * r4 + r2 * r3) = r1 * (r * r3 + r0 * - r4) +
    r2 * - (r * r4 + r0 * r3)). { ring. }
    assert (r * (r1 * r4 + r2 * r3) + r0 * (r1 * r3 + r2 * - r4) = r1 * (r * r4 + r0 * r3) +
    r2 * (r * r3 + r0 * - r4)). { ring. }
    rewrite H, H0; auto.
  - assert ((r * r1 - r0 * r2) * r3 + (r * r2 + r0 * r1) * - r4 = r1 * (r * r3 + r0 * - r4) +
    r2 * - (r * r4 + r0 * r3)). { ring. }
    assert ((r * r1 - r0 * r2) * r4 + (r * r2 + r0 * r1) * r3 = r1 * (r * r4 + r0 * r3) +
    r2 * (r * r3 + r0 * - r4)). { ring. }
    rewrite H, H0; auto.
Qed.

