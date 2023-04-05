Require Export Reals.
Require Import Base.
Open Scope R_scope.

Axiom classical : forall P,P \/ ~P.

(* 点的定义 *)
Inductive Point : Type := pair : R -> R -> Point.
Notation "( x , y )" := (pair x y).
Definition O : Point := (0,0).

Definition point_inverse A := match A with (x,y) => (-x,-y) end.
Notation "-- A" := (point_inverse A)(at level 50, left associativity).

Lemma point_eq : forall A B x1 y1 x2 y2, A = (x1,y1) /\ B = (x2,y2) 
  -> (A = B <-> x1 = x2 /\ y1 = y2).
Proof.
  intros. split; intros. 
  - destruct H. rewrite H, H1 in H0. injection H0 as H2 H3; auto. 
  - destruct H, H0. rewrite H, H1; rewrite H0, H2; auto.
Qed.

(* 点的加法 *)
Definition point_plus A B : Point :=
  match A, B with (x1,y1), (x2,y2)
   => (x1 + x2,y1 + y2)
  end.
Notation "A +. B" := (point_plus A B)(at level 50, left associativity).

Lemma pplus_comm : forall A B, A +.B = B +.A.
Proof.
  intros. induction A, B; unfold point_plus. rewrite Rplus_comm.
  rewrite (Rplus_comm r0); auto.
Qed.

Lemma pplus_assoc : forall A B C, (A +.B) +.C = A +.(B +.C).
Proof.
  intros. induction A, B, C; unfold point_plus. rewrite Rplus_assoc.
  rewrite (Rplus_assoc r0); auto.
Qed.

Lemma pplus_assoc' : forall A B C, A +.B +.C = A +.(B +.C).
Proof.
  intros. induction A,B,C; unfold point_plus. 
  repeat(rewrite Rplus_assoc); auto.
Qed.

Lemma pplus_O_p : forall A, O +.A = A.
Proof.
  intros. induction A; simpl. repeat (rewrite Rplus_0_l); auto.
Qed.

Lemma pplus_O_p' : forall A, A +.O = A.
Proof.
  intros. rewrite pplus_comm; apply pplus_O_p.
Qed.

(* 点的数乘 *)
Definition point_mult (λ : R) A : Point :=
  match A with (x,y) 
   => (λ * x,λ * y)
  end. 
Notation "λ *. A" := (point_mult λ A)(at level 40, left associativity).

Lemma pmult_0_p : forall A, 0 *.A = O.
Proof.
  intros. induction A; unfold point_mult, O. repeat (rewrite Rmult_0_l); auto.
Qed. 

Lemma pmult_1_p : forall A, 1 *.A = A.
Proof.
  intros. induction A; unfold point_mult. repeat (rewrite Rmult_1_l); auto.
Qed.

Lemma pmult_l_l_p : forall A a b,a *.(b *.A) = a * b *.A.
Proof.
  intros. induction A; unfold point_mult. repeat rewrite Rmult_assoc; auto.
Qed.

Lemma pmult_opp_p : forall A, -1 *.A = --A.
Proof.
  intros. induction A; unfold point_mult, point_inverse. 
  repeat (rewrite Rmult_opp_r); auto.
Qed.

Lemma pmult_opp_p' : forall A a, -a *.A = --a *.A.
Proof.
  intros. induction A; unfold point_mult,point_inverse.
  repeat (rewrite Ropp_mult_distr_l); auto.
Qed.

Lemma pmult_0_l : forall λ, λ *.O = O.
Proof.
  intros. unfold O, point_mult. repeat (rewrite Rmult_0_r); auto.
Qed.

Lemma pmult_plus_distr_l : forall a A B, a *.(A +.B) = a *.A +.a *.B.
Proof.
  intros. induction A, B; unfold point_mult, point_plus. rewrite Rmult_plus_distr_l.
  rewrite (Rmult_plus_distr_l a); auto.
Qed.

Lemma pmult_plus_distr_l' : forall a b A,(a + b) *.A = a *.A +.b *.A.
Proof.
  intros. induction A; unfold point_mult, point_plus.
  rewrite Rmult_comm. rewrite Rmult_plus_distr_l. 
  rewrite (Rmult_comm (a+b)). rewrite Rmult_plus_distr_l.
  rewrite Rmult_comm. rewrite (Rmult_comm r). 
  rewrite (Rmult_comm r0 a). rewrite (Rmult_comm r0 b). auto.
Qed. 

Lemma  pmult_plus_distr_l'' : forall a A,(a + 1) *.A = a *.A +.A.
Proof.
  intros. assert(a *.A +.A = a *.A +.1 *.A).
  { rewrite pmult_1_p;auto. } rewrite H.
  apply (pmult_plus_distr_l' a 1 A).
Qed.

(* 点的数除 *)
Definition point_divR (λ : R) A :=
  match A with (x,y)
  => (x / λ,y / λ)
  end.
Notation "A /. λ" := (point_divR λ A)(at level 40, left associativity).

(* 点的减法 *)
Definition point_minus A B : Point :=
  match A, B with (x1,y1), (x2,y2)
   => (x1 - x2,y1 - y2)
  end.
Notation "A -. B" := (point_minus A B)(at level 50, left associativity).

Lemma pminus_O : forall A, A -.O = A.
Proof.
  intros. induction A; unfold O, point_minus. repeat (rewrite Rminus_0_r); auto.
Qed.

Lemma pminus_O_A : forall A, O -.A = -- A.
Proof.
  intros. induction A; unfold O, point_minus, point_inverse. repeat (rewrite Rminus_0_l); auto.
Qed.

Lemma pminus_eq_O : forall A, A -.A = O.
Proof.
  intros. induction A; unfold point_minus, O. repeat (rewrite Rminus_eq_0); auto.
Qed.

Lemma pmult_minus_distr : forall a A B, a *.(A -.B) = a *.A -.a *.B.
Proof.
  intros. induction A, B; unfold point_mult, point_minus. rewrite Rmult_minus_distr_l.
  assert (a * (r0 - r2) = a * r0 - a * r2). { ring. }
  rewrite H; auto.
Qed.

Lemma pmult_minus_distr' : forall a b A,(a - b) *.A = a *.A -.b *.A.
Proof.
  intros. induction A; unfold point_mult, point_minus.
  repeat rewrite Rmult_minus_distr_r'. rewrite Rmult_comm.
  rewrite (Rmult_comm r b). rewrite (Rmult_comm r0 a).
  rewrite (Rmult_comm r0 b). auto.
Qed.

Lemma pmult_minus_opp : forall A B, -1 *.(A -.B) = B -.A.
Proof.
  intros. induction A, B; unfold point_mult, point_minus.
  assert (-1 * (r - r1) = r1 - r). { ring. }
  assert (-1 * (r0 - r2) = r2 - r0). { ring. }
  rewrite H, H0; auto.
Qed.

Lemma pmult_minus_opp' : forall A B a, -a *.(A -.B) = a *.(B -.A).
Proof.
  intros. induction A, B; unfold point_mult, point_minus.
  f_equal; ring.
Qed.

Lemma pplus_minus_tran : forall A B, A +.(-- B) = A -.B.
Proof.
  intros. induction A, B; unfold point_plus, point_inverse, point_minus.
  repeat (rewrite rplus_minus_tran); auto.
Qed.

Lemma pplus_minus_tran' : forall A B, (-- A) +.B = B -.A.
Proof.
  intros. induction A, B; unfold point_plus, point_inverse, point_minus.
  repeat (rewrite rplus_minus_tran'); auto.
Qed.

Lemma pplus_minus_assoc : forall A B C, A +.B -.C = A +.(B -.C).
Proof.
  intros. induction A, B, C; unfold point_plus, point_minus.
  repeat (rewrite pm_assoc'); auto.
Qed.

Lemma pplus_minus_assoc' : forall A B C, A -.B +.C = A -.(B -.C).
Proof.
  intros. induction A,B,C; unfold point_plus, point_minus.
  assert(r - r1 + r3 = r - (r1 - r3)). { ring. }
  assert(r0 - r2 + r4 = r0 - (r2 - r4)). { ring. }
  rewrite H,H0;auto.
Qed.

Lemma pmult_minus_distr_l : forall a A B, a *.(A -.B) = a *.A -.a *.B.
Proof.
  intros. induction A, B; unfold point_mult, point_minus. 
  repeat(rewrite Rmult_minus_distr_l); auto.
Qed.

(* 点的乘法 *)
Definition point_magn A B : R :=
  match A, B with (x,y), (u,v)
   => x * u + v * y
  end.
Notation "A ·. B" := (point_magn A B)(at level 40, left associativity).

Lemma Pmagn_minus_distr : forall A B C, A ·.(B -.C) = A ·.B - A ·.C.
Proof.
  intros. induction A, B, C; unfold point_magn, point_minus; ring.
Qed.

Lemma Pmagn_minus_distr' : forall A B C, (B -.C) ·.A = B ·.A - C ·.A.
Proof.
  intros. induction A, B, C; unfold point_minus, point_magn; ring.
Qed.

Lemma Pmagn_minus3_distr : forall A B C D, (A -.B -.C) ·.D = A ·.D - B ·.D - C ·.D.
Proof.
  intros. induction A, B, C, D; unfold point_magn, point_minus; ring.
Qed.

Lemma Pmagn_plus_distr : forall A B C, A ·.(B +.C) = A ·.B + A ·.C.
Proof.
  intros. induction A, B, C; unfold point_magn, point_plus; ring.
Qed.

Lemma Pmagn_plus_distr' : forall A B C, (A +.B)·.C = A ·.C + B ·.C.
Proof.
  intros. induction A, B, C; unfold point_magn, point_plus; ring.
Qed.

Lemma Pmagn_mult_assoc : forall λ A B,(λ *.A) ·.B = λ * (A ·.B).
Proof.
  intros. induction A,B;unfold point_magn,point_mult;ring.
Qed.

Lemma Pmagn_mult_assoc' : forall λ A B,A ·.(λ *.B) = λ * (A ·.B).
Proof.
  intros. induction A,B;unfold point_magn,point_mult;ring.
Qed.

Lemma Pmagn_minus_0 : forall A B, A ·.B - A ·.B = 0.
Proof.
  intros. induction A, B; unfold point_magn; ring.
Qed.

(* 两点的外积 *)
Definition point_Oprod A B := B -.A.
Notation "A /p B" := (point_Oprod A B)(at level 50, left associativity).

Lemma Oprod_l_l : forall P,P /pP = O.
Proof.
  intros. unfold point_Oprod. apply pminus_eq_O.
Qed.

Lemma Oprod_O_l : forall P, P = O /pP.
Proof.
  intros; induction P; unfold point_Oprod, point_minus, point_inverse, O.
  repeat (rewrite Rminus_0_r); auto.
Qed.

Lemma Oprod_O_l_mult : forall P u, u *.P = u *.(O /pP).
Proof.
  intros. induction P; unfold point_mult, point_Oprod, point_minus, O.
  repeat (rewrite Rminus_0_r); auto.
Qed.

Lemma Oprod_O_l' : forall P, P = -- (P /pO).
Proof.
  intros; induction P; unfold point_Oprod, point_minus, point_inverse, O.
  repeat (rewrite Rminus_0_l; rewrite Ropp_involutive); auto.
Qed.

Lemma Oprod_O_l'_mult : forall P u, u *.P = -- u *.(P /pO).
Proof.
  intros. induction P; unfold point_mult, point_Oprod, point_minus, point_inverse, O.
  repeat (rewrite Rminus_0_l; rewrite Ropp_mult_distr_r_reverse; rewrite Ropp_involutive);
  auto.
Qed.

(* 三点的外积 *)
Definition point_3prod A B C :=
  match A, B, C with (x1,y1), (x2,y2), (x3,y3) 
  => x1 * y2 + x2 * y3 + x3 * y1 - x1 * y3 - x2 * y1 - x3 * y2
  end.
Notation "A /e B /e C" := (point_3prod A B C)(at level 50, left associativity).

(* 复数乘点 *)
Definition point_mult_i A :=
  match A with (x,y) 
  => (-y,x)
  end.
Notation "i*. A" := (point_mult_i A)(at level 40, left associativity).

Inductive Complex : Type := prod : R -> R -> Complex.
Notation "[ u , v ]" := (prod u v)(at level 60).
Definition R_R_to_C (a : R) (b : R) : Complex := [a,b]. 

Definition Cre (c : Complex) : R :=
  match c with [r1,i1] => r1 end.

Definition Cim (c : Complex) : R :=
  match c with [r1,i1] => i1 end.

Definition Creal (c : Complex) : R := 
  match c with [u,v] => sqrt(u²+v²)end.

Definition Cplus c1 c2 :=
  match c1, c2 with [a,b], [c,d]
  => [a + c,b + d]
  end.
Notation "c1 +/C c2" := (Cplus c1 c2)(at level 50, left associativity).

Definition Cminus c1 c2 :=
  match c1, c2 with [a,b], [c,d]
  => [a - c,b - d]
  end.

Definition Cmult c1 c2 :=
  match c1, c2 with [a,b], [c,d]
  => [a*c - b*d,a*d + b*c]
  end.
Notation "c1 */C c2" := (Cmult c1 c2)(at level 40, left associativity).

Definition Cinv c :=
  match c with [a,b]
  => [a/(a*a+b*b),-b/(a*a+b*b)]
  end.

Definition Cconj c :=
  match c with [a,b]
  => [a,-b]
  end.

Definition Cnorm_sqr c :=
  match c with [a,b]
  => [a*a,b*b]
  end.

Definition Cnorm c :=
  match c with [a,b]
  => [sqrt(a*a),sqrt(b*b)]
  end.

Definition Copp c :=
  match c with [a,b]
  => [-a,-b]
  end.

Definition Cscal (λ : R) c :=
  match c with [a,b]
  => [λ*a,λ*b]
  end.
(* Infix " '+i' " := R_R_to_C (at level 60). *)

Definition point_mult_complex A (α : Complex) :=
  match α with [u,v]
  => u *.A +.v *.(i*.A)
  end.
Notation "α */c A" := (point_mult_complex A α)(at level 40, left associativity).

Definition point_to_complex A := 
  match A with (x,y)
  => [x,y]
  end.
Notation "f( A )" := (point_to_complex A)(at level 40).

Definition complex_to_point (α : Complex) :=
  match α with [x,y]
  => (x,y)
  end.
Notation "p( α )" := (complex_to_point α)(at level 40).

Lemma map_1 : forall A, p(f(A)) = A.
Proof.
  intros. induction A; unfold point_to_complex, complex_to_point; auto.
Qed.

Lemma map_2 : forall α, f(p(α)) = α.
Proof.
  intros. induction α; unfold complex_to_point, point_to_complex; auto.
Qed.

Lemma map_3 : forall A α, α */cA = p(α */Cf(A)).
Proof.
  intros. induction α, A. unfold point_mult_complex, point_mult_i, point_mult, point_plus.
  unfold point_to_complex, Cmult, complex_to_point.
  f_equal;ring.
Qed.

(* 向量的定义 *)
Definition vector' A B := B -.A.
Definition v0 := vector' O O.

(* 记A²=A·A，则(A—B)²=|AB|²，而A²为点A到原点距离的平方。
当A和B都不是原点时，A·B=0表示∠AOB为直角；(A-B)·(C-D)=0表示向量AB⊥向量CD。 *)

Definition point_sqr A := A ·.A.
Definition gap_sqr A B := point_sqr(A -.B).
Definition gap A B := sqrt(point_sqr(A -.B)).
Definition Per A O B := A <> O /\ B <> O /\ A ·.B = 0.
Definition Perp A B C D := (A -.B) ·.(C -.D) = 0.
Definition cos1 B A C := (A -.B) ·.(A -.C) / (gap A B * gap A C).
Definition sin1_sqr B A C := 1 - (cos1 B A C)². 

Lemma gap_sqr_O : forall A, gap_sqr A O = point_sqr A.
Proof.
  intros. unfold gap_sqr, point_sqr. repeat(rewrite pminus_O); auto.
Qed.

Lemma gap_O : forall A, gap A O = sqrt(point_sqr A).
Proof.
  intros. unfold gap, point_sqr. repeat(rewrite pminus_O); auto.
Qed.

Lemma sqr_incr_0 : forall a b, 0 <= Rsqr a + Rsqr b.
Proof.
  intros. pose proof(Rle_0_sqr a). pose proof(Rle_0_sqr b).
  apply Rplus_le_le_0_compat; auto.
Qed.

Lemma sqr_0 : forall a,a <> 0 -> Rsqr a <> 0.
Proof.
  intros. apply Rlt_0_sqr in H. apply Rlt_not_eq in H. auto.
Qed.

Lemma gap_to_sqr : forall A B, Rsqr(gap A B) = gap_sqr A B.
Proof.
  intros. unfold Rsqr, gap, gap_sqr, point_sqr. 
  induction A, B; unfold point_minus, point_magn.
  assert((r - r1) * (r - r1) + (r0 - r2) * (r0 - r2) = Rsqr(r - r1)+ Rsqr(r0 -r2)).
  { unfold Rsqr; auto. } rewrite H.
  apply sqrt_def. apply sqr_incr_0. 
Qed.

Lemma gap_to_sqr_O : forall A, Rsqr(gap A O) = point_sqr A.
Proof.
  intros. rewrite gap_to_sqr, gap_sqr_O; auto.
Qed.

(* 三点共线 *)

Definition col A B C:= 
 (exists λ ,λ <> 0 /\ vector' B A = λ*.vector' B C) 
  \/ (A = B \/ A = C \/ B = C).

Lemma col_all : forall A B C, col A B C -> col A C B.
Proof.
  intros. unfold col in * . destruct H as [H|[H|[H|H]]]; auto. destruct H. destruct H.
  unfold vector' in * . destruct A,B,C. unfold point_minus,point_mult in H0.
  injection H0 as H1 H2. destruct (classical(r1 = r3)).
  - destruct (classical (r2=r4)).
    + right. subst. auto.
    + destruct(classical(x = 1)).
      * subst. rewrite Rminus_eq_0 in H1. rewrite Rmult_0_r in H1.
        apply Rminus_diag_uniq in H1. rewrite Rmult_1_l in H2.
        apply minus_same in H2. subst. auto.
      * left. exists (1-x). rewrite Rmult_minus_distr_l in H2. 
      assert(r0 - r2 + r2 = x * r4 - x * r2 + r2).
      { rewrite H2; auto. } rewrite minus_eq in H5.
      assert(x * r4 - x * r2 + r2 = x * r4 + (1 - x) * r2). { ring. }
      rewrite H6 in H5. rewrite H5. unfold point_minus,point_mult.
      split. apply Rminus_eq_contra. auto. subst. rewrite H1. f_equal; ring.
   - destruct (classical (r2=r4)).
    + destruct(classical(x = 1)).
      * subst. rewrite Rmult_1_l in H1,H2. rewrite <- minus_same in H1,H2.
        subst. auto.
      * left. exists (1-x). unfold point_minus,point_mult.
        split. apply Rminus_eq_contra. auto. f_equal.
        assert(r - r1 + r1 = x * (r3 - r1) + r1). { rewrite H1;auto. }
        rewrite minus_eq in H5. subst. ring. rewrite H3 in H2.
        rewrite H2. subst. repeat rewrite Rminus_eq_0. ring.
   + destruct(classical(x = 1)).
      * subst. rewrite Rmult_1_l in H1,H2. rewrite <- minus_same in H1,H2.
        subst. auto.
      * left. exists (1-x). unfold point_minus,point_mult.
        split. apply Rminus_eq_contra. auto. f_equal.
        assert(r - r1 + r1 = x * (r3 - r1) + r1). { rewrite H1;auto. }
        rewrite minus_eq in H5. subst. ring. 
        assert(r0 - r2 + r2 = x * (r4 - r2) + r2). { rewrite H2;auto. }
        rewrite minus_eq in H5. subst. ring.
Qed.

Lemma Popp_eq_compat : forall A B, A = B -> -- A = -- B.
Proof.
  intros. induction A, B; unfold point_inverse. injection H as H1 H2.
  apply Ropp_eq_compat in H1. apply Ropp_eq_compat in H2.
  rewrite H1, H2; auto.
Qed.

(* 中点 *)
Definition Midpoint M A B := vector' M A = vector' B M.

(* 重心 *)
Definition focus P A B C := vector' P A +.vector' P B +.vector' P C = v0.

(* 垂心 *)
Definition orthocenter P A B C := vector' P A ·.vector' P B = vector' P B ·.vector' P C
  /\ vector' P B ·.vector' P C = vector' P C ·.vector' P A.

(* 平行四边形：一组对边平行且相等。 *)
Definition Parallelogram A B C D := vector' B A = vector' D C /\ A <> C.

(* AC与BD互相平分 *)
Definition Plg M A B C D := (A <> C \/ B <> D) /\ Midpoint M A C /\ Midpoint M B D.

(* 三角形 *)
Definition Triangle A B C := ~col A B C.

(* 垂直平分线 *)
Definition Perp_bisect X P Q A B := (Midpoint X A B /\ col P Q X)
  /\ (Perp P Q A B) /\ A <> B.

(* 分角线 *)
Definition Angle_div E O B C:= (gap C O) *.B +.(gap B O) *.C = (gap B O + gap C O) *.E.

(* 中位线 *)
Definition Mid_line D E A B C := Midpoint D A B /\ Midpoint E A C.




