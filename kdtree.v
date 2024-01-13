From Coq Require Import Lia.

From Coq Require Import QArith.

From Coq Require Import QArith.Qcanon.

Notation "b1 && b2" := (andb b1 b2).

Definition q_less_than (q1 q2 : Qc) : bool :=
  match q1 ?= q2 with
  | Lt => true
  | Gt => false
  | Eq => false
  end.

Definition q_greater_than (q1 q2 : Qc) : bool :=
  match q1 ?= q2 with
  | Lt => false
  | Gt => true
  | Eq => false
  end.

Definition q_equal (q1 q2 : Qc) : bool :=
  match q1 ?= q2 with
  | Lt => false
  | Gt => false
  | Eq => true
  end.

Definition q_less_than_or_equal (q1 q2 : Qc) : bool :=
  match q1 ?= q2 with
  | Gt => false
  | Lt => true
  | Eq => true
  end.

Lemma qlt_iff_true : forall (q1 q2 : Qc), q1 < q2 <-> q_less_than q1 q2 = true.
Proof. intros q1 q2. split.
       - intros H. unfold q_less_than. destruct (q1 ?= q2) as [] eqn:E; try reflexivity;
           try (rewrite Qclt_alt in H; rewrite H in E; inversion E).
       - unfold q_less_than. destruct (q1 ?= q2) as [] eqn:E; intros H; try inversion H.
         apply Qclt_alt. apply E.
Qed.

Lemma qgt_iff_true : forall (q1 q2 : Qc), q1 > q2 <-> q_greater_than q1 q2 = true.
Proof. intros q1 q2. split.
       - intros H. unfold q_greater_than. destruct (q1 ?= q2) as [] eqn:E; try reflexivity;
           try (rewrite Qcgt_alt in H; rewrite H in E; inversion E).
       - unfold q_greater_than. destruct (q1 ?= q2) as [] eqn:E; intros H; try inversion H.
         apply Qcgt_alt. apply E.
Qed.

Lemma qeq_iff_true : forall (q1 q2 : Qc), q1 = q2 <-> q_equal q1 q2 = true.
Proof. intros q1 q2. split.
       - intros H. unfold q_equal. destruct (q1 ?= q2) as [] eqn:E; auto.
         + apply Qclt_alt in E. apply Qclt_not_eq in E. auto.
         + apply Qcgt_alt in E. apply Qclt_not_eq in E. symmetry in H. auto.
       - unfold q_equal. destruct (q1 ?= q2) as [] eqn:E; intros H; try inversion H.
         apply Qceq_alt in E. apply E.
Qed.

Lemma qgt_if_false : forall (q1 q2 : Qc), q1 <> q2 -> q_less_than q1 q2 = false ->  q2 < q1.
Proof. unfold q_less_than. intros q1 q2 H1. destruct (q1 ?= q2) as [] eqn:E; intros.
       - rewrite <- Qceq_alt in E. rewrite E in H1. unfold not in H1. destruct H1. reflexivity.
       - discriminate H.
       - rewrite <- Qcgt_alt in E. apply E.
Qed.

Lemma qeq_false_iff : forall (q1 q2 : Qc), q1 <> q2 <-> q_equal q1 q2 = false.
Proof. intros. split.
       - intros H. unfold q_equal. destruct (q1 ?= q2) as [] eqn:E; try auto. unfold not in H.
         exfalso. apply H. apply Qceq_alt. assumption.
       - unfold q_equal. destruct (q1 ?= q2) as [] eqn:E; intros H; try inversion H.
         + apply Qclt_not_eq; auto.
         + rewrite <- Qcgt_alt in E. unfold not. intros contra. rewrite contra in E.
           apply Qlt_irrefl in E. assumption. (*where is that used?*)
Qed.

Lemma Qcle_lt_or_eq : forall x y, x<=y -> x<y \/ x==y.
Proof.
  unfold Qcle, Qclt; intros; apply Qle_lt_or_eq; auto.
Qed.
       
Lemma qeq_refl : forall (q : Qc), q_equal q q = true.
Proof. intros q. apply qeq_iff_true. reflexivity. Qed.

Inductive Dim : Type :=
| X
| Y.

Definition Vector : Type := Qc*Qc.
Definition Coord : Type :=  option Vector.
Definition Rectangle : Type := Vector*Vector.

Inductive tree : Type :=
| Point : Coord -> tree
| Split : Dim -> Qc -> tree -> tree -> tree.

Notation "'[' t1 '|' cv '|' t2 ']'" := (Split X cv t1 t2) (at level 40).
Notation "'[' t1 '~' cv '~' t2 ']'" := (Split Y cv t1 t2) (at level 40).
Notation "'{' x ',' y '}'" := (Point (Some x, Some y)) (at level 40).
Notation "'{' '}'" := (Point None) (at level 40).

Inductive Bounded : Rectangle -> Vector -> Prop :=
| B : forall r v, fst v < fst (snd r) -> fst (fst r) < fst v ->
                  snd v < snd (snd r) -> snd (fst r) < snd v -> Bounded r v.

Inductive Aligned : Qc -> Dim -> Rectangle -> Rectangle -> Prop :=
| CY : forall cv r1 r2, (snd (snd r1)) = cv -> (fst (fst r1)) = (fst (fst r2)) ->
                        (snd (snd r1)) = (snd (fst r2)) -> (fst (snd r1)) = (fst (snd r2)) ->
                        Aligned cv Y r1 r2
| CX : forall cv r1 r2, (fst (snd r1)) = cv -> (snd (snd r1)) = (snd (snd r2)) ->
                        (fst (snd r1)) = (fst (fst r2)) -> (snd (fst r1)) = (snd (fst r2)) ->
                        Aligned cv X r1 r2.

Inductive Merged : Rectangle -> Rectangle -> Rectangle -> Prop :=
| M : forall r1 r2 r3, fst (fst r3) = fst (fst r1) -> snd (fst r3) = snd (fst r1) ->
                       fst (snd r3) = fst (snd r2) -> snd (snd r3) = snd (snd r2) ->
                       Merged r1 r2 r3.

Inductive KDT : Rectangle -> tree -> Prop :=
| KDT_Point_Empty : forall r, KDT r (Point None)
| KDT_Point_Coord : forall r v, Bounded r v -> KDT r (Point (Some v))
| KDT_Split : forall r1 r2 r3 d cv t1 t2, KDT r1 t1 -> KDT r2 t2 -> Aligned cv d r1 r2 ->
                                             Merged r1 r2 r3 -> KDT r3 (Split d cv t1 t2).

Definition bounded (r : Rectangle) (v : Vector) : bool :=
  q_less_than (fst (fst r)) (fst v) && q_less_than (snd (fst r)) (snd v) &&
    q_less_than (fst v) (fst (snd r)) && q_less_than (snd v) (snd (snd r)).
          

Definition aligned (cv : Qc) (d : Dim) (r1 r2 : Rectangle) : bool :=
  match d with
  | X => (q_equal (fst (snd r1)) cv) && (q_equal (snd (snd r1)) (snd (snd r2))) &&
           (q_equal (fst (snd r1)) (fst (fst r2))) && (q_equal (snd (fst r1)) (snd (fst r2)))
  | Y => (q_equal (snd (snd r1)) cv) && (q_equal (fst (fst r1)) (fst (fst r2))) &&
           (q_equal (snd (snd r1)) (snd (fst r2))) && (q_equal (fst (snd r1)) (fst (snd r2)))
  end.

Definition merged (r1 r2 r3 : Rectangle) : bool :=
  (q_equal (fst (fst r3)) (fst (fst r1))) && (q_equal (snd (fst r3)) (snd (fst r1))) &&
    (q_equal (fst (snd r3)) (fst (snd r2))) && (q_equal (snd (snd r3)) (snd (snd r2))).
                           

Fixpoint kdt (r : Rectangle) (t : tree) : bool :=
  match t with
  | Point coord => match coord with
                   | None => true
                   | Some v =>  bounded r v
                   end
  | Split d cv t1 t2 => match d with
                        | X => (kdt ((fst r), (cv, snd (snd r))) t1) &&
                              (kdt ((cv, snd (fst r)),(snd r)) t2) &&
                          aligned cv X ((fst r), (cv, snd (snd r))) ((cv, snd (fst r)),(snd r))
                          && merged ((fst r), (cv, snd (snd r))) ((cv, snd (fst r)),(snd r)) r
                        | Y => (kdt ((fst r), (fst (snd r),cv)) t1) &&
                                 (kdt ((fst (fst r),cv), (snd r)) t2) &&
                          aligned cv Y ((fst r), (fst (snd r),cv)) ((fst (fst r),cv), (snd r))
                          && merged ((fst r), (fst (snd r),cv)) ((fst (fst r),cv), (snd r)) r
                        end
  end.


#[export] Hint Constructors Dim tree Bounded Aligned KDT Merged : core.


Ltac try_replace_eq H := try rewrite qlt_iff_true in H;
                         try rewrite qgt_iff_true in H;
                         try rewrite qeq_iff_true in H.

Ltac try_replace_eq' := try rewrite qlt_iff_true;
                        try rewrite qgt_iff_true;
                        try rewrite qeq_iff_true.

Ltac try_rep_eq_auto := match goal with
                        | H : ?T1 < ?T2 |- _ => try_replace_eq H
                        | H : ?T1 > ?T2 |- _ => try_replace_eq H
                        | H : ?T1 = ?T2 |- _ => try_replace_eq H
                        end.

Ltac invert H := inversion H; subst; clear H.

Ltac bool_cases := match goal with
                        | b : bool |- _ => destruct b; simpl; try discriminate
                        end.

Lemma bool_to_prop : forall (b1 b2 b3 b4 : bool), (b1 && b2 && b3 && b4) = true ->
                                          ((b1 = true /\ b2 = true) /\ b3 = true) /\ b4 = true.
Proof.
  intros. do 3 try split; repeat bool_cases; assumption.
Qed.

Lemma s : forall (b1 b2 b3 b4 : bool), b1 = true -> b2 = true -> b3 = true -> b4 = true ->
                                       b1 && b2 && b3 && b4 = true.
Proof. intros. rewrite H, H0, H1, H2. reflexivity. Qed.

Lemma bounded_iff_Bounded : forall (v : Vector) (r : Rectangle), Bounded r v <-> bounded r v = true.
Proof. intros v r. split.
       - intros H. invert H. unfold bounded. repeat try_rep_eq_auto. destruct r.
         destruct v,v0,v1. simpl in *. rewrite H0, H1, H2, H3. reflexivity.
       - intros H. destruct r. destruct v, v0, v1. unfold bounded in H.
         simpl in H. apply bool_to_prop in H. do 3 destruct H as [H ?H].
         apply B; simpl; try_replace_eq'; assumption.
Qed.

Lemma aligned_iff_Aligned : forall (cv : Qc) (d : Dim) (r1 r2 : Rectangle),
    Aligned cv d r1 r2 <-> aligned cv d r1 r2 = true.
Proof. intros cv d [v0 v1] [v2 v3]. destruct v0, v1, v2, v3. split.
       - intros H. invert H; simpl in *; try_replace_eq H1; try_replace_eq H2;
           try_replace_eq H3; rewrite H1, H2, H3; rewrite qeq_refl; reflexivity.
       - intros H. destruct d; simpl in H; apply bool_to_prop in H; do 3 destruct H as [H ?H];
         try apply CX; try apply CY; simpl; try_replace_eq'; assumption.
Qed.

Ltac elim_rect := match goal with
                        | r : Rectangle |- _ => destruct r; simpl
                        end.
Ltac elim_vect := match goal with
                        | v : Vector |- _ => destruct v; simpl
                        end.

Lemma merged_iff_Merged : forall (r1 r2 r3 : Rectangle), Merged r1 r2 r3 <-> merged r1 r2 r3 = true.
Proof. intros. unfold merged. repeat elim_rect. repeat elim_vect. split.
       - intros H. invert H. simpl in *. subst. repeat rewrite qeq_refl. reflexivity.
       - intros H. apply bool_to_prop in H. do 3 destruct H as [H ?H].
         apply M; simpl; try_replace_eq'; assumption.
Qed.

Ltac bool_to_prop' H := apply bool_to_prop in H; do 3 destruct H as [H ?H].

Ltac elimi := repeat elim_rect; repeat elim_vect; simpl in *.

Ltac clear_eq := match goal with
                 | H : ?T = ?T |- _ => clear H
                 end.
#[export] Hint Unfold merged aligned : core.
#[export] Hint Resolve merged_iff_Merged aligned_iff_Aligned qeq_iff_true qeq_refl : core.
#[export] Hint Resolve bounded_iff_Bounded : core.

Theorem kdt_iff_KDT : forall (t : tree) (r : Rectangle), KDT r t <-> kdt r t = true.
Proof. intros t r. split.
       - intros H. induction H.
         + reflexivity.
         + simpl. apply bounded_iff_Bounded. assumption.
         + destruct d;
             try (apply merged_iff_Merged in H2; apply aligned_iff_Aligned in H1;
                  elimi; unfold merged in *; bool_to_prop' H1;
                  bool_to_prop' H2; simpl in *; rewrite <- qeq_iff_true in *; subst;
                  repeat rewrite qeq_refl; simpl; apply s; try assumption; reflexivity).
       - intros H. generalize dependent r. induction t.
         + intros r H. destruct c; constructor. apply bounded_iff_Bounded in H. assumption.
         + intros r H. destruct d; simpl in H; bool_to_prop' H; bool_to_prop' H1;
           econstructor; eauto.
Qed.

(*
Definition ex_kdtree1 := Split X (Q2Qc 5) (Point (Some ((Q2Qc 2),(Q2Qc 2))))
                           (Split Y (Q2Qc 5)
                              (Point None) (Point (Some ((Q2Qc 7),(Q2Qc 7))))).

Definition simpleX := [ { } | 5 | { } ].
Definition simpleY := [ { } ~ 5 ~ { } ].

Definition ex_kdtree1_notation := [ { 2, 2 } | 5 | [ { } ~ 5 ~ { 7, 7 }]].

Example test_notation : ex_kdtree1 = ex_kdtree1_notation.
Proof. auto. Qed.

Example isKDT1' : KDT ( (Q2Qc 0, Q2Qc 0), (Q2Qc 10, Q2Qc 10) ) ex_kdtree1.
Proof.
  apply kdt_iff_KDT. auto.
Qed.

*)

Definition mid (d : Dim) (v1 v2 : Vector) : Qc :=
  match d with
  | X => (fst v1 + fst v2)/(Q2Qc 2)
  | Y => (snd v1 + snd v2)/(Q2Qc 2)
  end.

Definition max_wrt_dim (d : Dim) (v1 v2 : Vector) : Vector :=
  match d with
  | X => if (q_less_than (fst v1) (fst v2)) then v2 else v1
  | Y => if (q_less_than (snd v1) (snd v2)) then v2 else v1
  end.

Definition min_wrt_dim (d : Dim) (v1 v2 : Vector) : Vector :=
  match d with
  | X => if (q_less_than (fst v1) (fst v2)) then v1 else v2
  | Y => if (q_less_than (snd v1) (snd v2)) then v1 else v2
  end.

Lemma mid_lemma1 : forall (q1 q2 m : Qc), m = (q1 + q2) / (Q2Qc 2) -> q1 < q2 -> q1 < m.
Proof. Admitted.

Lemma mid_lemma2 : forall (q1 q2 m : Qc), m = (q1 + q2) / (Q2Qc 2) -> q1 < q2 -> q2 > m.
Proof. Admitted.

Lemma generalized_bounded_lemma_x1 : forall (v1 : Vector) (r1 r2 r3 : Rectangle) (cv : Qc),
    Bounded r3 v1 -> fst v1 < cv -> Aligned cv X r1 r2 -> Merged r1 r2 r3 -> Bounded r1 v1.
Proof. intros v1 r1 r2 r3 cv HB HL HA HM. inversion HB; subst; clear HB. inversion HA; subst;
         clear HA. inversion HM; subst; clear HM. repeat elim_rect. repeat elim_vect. simpl in *.
       apply B; simpl; try eauto.
       - rewrite H3 in H0. assumption.
       - rewrite <- H4 in H9. rewrite H9 in H1. assumption.
       - rewrite H7 in H2. assumption.
Qed.


Lemma generalized_bounded_lemma_x2 : forall (v1 : Vector) (r1 r2 r3 : Rectangle) (cv : Qc),
    Bounded r3 v1 -> cv < fst v1 -> Aligned cv X r1 r2 -> Merged r1 r2 r3 -> Bounded r2 v1.
Proof. intros v1 r1 r2 r3 cv HB HL HA HM. inversion HB; subst; clear HB. inversion HA; subst;
         clear HA. inversion HM; subst; clear HM. repeat elim_rect. repeat elim_vect. simpl in *.
       apply B; simpl; try eauto.
       - rewrite H8 in H. assumption.
       - rewrite H5 in HL. assumption.
       - rewrite H9 in H1. assumption.
       - rewrite H6 in H7. rewrite H7 in H2. assumption.
Qed.

Lemma generalized_bounded_lemma_y1 : forall (v1 : Vector) (r1 r2 r3 : Rectangle) (cv : Qc),
    Bounded r3 v1 -> snd v1 < cv -> Aligned cv Y r1 r2 -> Merged r1 r2 r3 -> Bounded r1 v1.
Proof. intros v1 r1 r2 r3 cv HB HL HA HM. inversion HB; subst; clear HB. inversion HA; subst;
         clear HA. inversion HM; subst; clear HM. repeat elim_rect. repeat elim_vect. simpl in *.
       apply B; simpl; try eauto.
       - rewrite <- H8 in H6. rewrite <- H6 in H. assumption.
       - rewrite H3 in H0. assumption.
       - rewrite H7 in H2. assumption.
Qed.

Lemma generalized_bounded_lemma_y2 : forall (v1 : Vector) (r1 r2 r3 : Rectangle) (cv : Qc),
    Bounded r3 v1 -> cv < snd v1 -> Aligned cv Y r1 r2 -> Merged r1 r2 r3 -> Bounded r2 v1.
Proof. intros v1 r1 r2 r3 cv HB HL HA HM. inversion HB; subst; clear HB. inversion HA; subst;
         clear HA. inversion HM; subst; clear HM. repeat elim_rect. repeat elim_vect. simpl in *.
       apply B; simpl; try eauto.
       - rewrite H8 in H. assumption.
       - rewrite H4 in H3. rewrite H3 in H0. assumption.
       - rewrite H9 in H1. assumption.
       - rewrite H5 in HL. assumption.
Qed.

Definition split (d : Dim) (r : Rectangle) (v1 v2 : Vector) :=
  match d with
  | X => ((fst r, (mid d v1 v2, snd (snd r))), ((mid d v1 v2, snd (fst r)), snd r))
  | Y => ((fst r, (fst (snd r), mid d v1 v2)), ((fst (fst r), mid d v1 v2), snd r))
  end.

Definition lt_d (d : Dim) (v1 v2 : Vector) :=
  match d with
  | X => fst v1 < fst v2
  | Y => snd v1 < snd v2
  end.

Definition neq_d (d : Dim) (v1 v2 : Vector) :=
  match d with
  | X => fst v1 <> fst v2
  | Y => snd v1 <> snd v2
  end.

Definition bneq_d (d : Dim) (v1 v2 : Vector) :=
  match d with
  | X => negb (q_equal (fst v1) (fst v2))
  | Y => negb (q_equal (snd v1) (snd v2))
  end.

Lemma neq_d_iff_true : forall d v1 v2, neq_d d v1 v2 <-> bneq_d d v1 v2 = true.
Proof.
  intros. split.
  - destruct d; simpl; intros H; apply negb_true_iff; apply qeq_false_iff; assumption.
  - destruct d; simpl; intros H; apply qeq_false_iff; apply negb_true_iff; assumption.
Qed.

Lemma neq_to_lt : forall d v1 v2, neq_d d v1 v2 ->
                                 lt_d d (min_wrt_dim d v1 v2) (max_wrt_dim d v1 v2).
Proof.
  intros. destruct d; simpl in *.
  - destruct (q_less_than (fst v1) (fst v2)) eqn:LT.
    + apply qlt_iff_true. assumption.
    + apply qgt_if_false; assumption.
  - destruct (q_less_than (snd v1) (snd v2)) eqn:LT.
    + apply qlt_iff_true. assumption.
    + apply qgt_if_false; assumption.
Qed.

#[export] Hint Resolve mid_lemma1 : core.
#[export] Hint Resolve mid_lemma2 : core.
#[export] Hint Constructors Bounded : core.

Lemma split_lemma_fst : forall r d v1 v2, lt_d d v1 v2 -> Bounded r v1 -> Bounded r v2 ->
                                     Bounded (fst (split d r v1 v2)) v1.
Proof.
  intros. destruct d; simpl in *; invert H0; constructor; simpl; eauto.
Qed.

Lemma split_lemma_snd : forall r d v1 v2, lt_d d v1 v2 -> Bounded r v1 -> Bounded r v2 ->
                                     Bounded (snd (split d r v1 v2)) v2.
Proof.
  intros. destruct d; invert H1; simpl in *;
    constructor; simpl; try assumption; eapply mid_lemma2; try reflexivity; assumption.
Qed.

Lemma min_split : forall d v1 v2, min_wrt_dim d v1 v2 = v1 \/ min_wrt_dim d v1 v2 = v2.
Proof.
  intros. destruct d; simpl.
  - destruct (q_less_than (fst v1) (fst v2)); auto.
  - destruct (q_less_than (snd v1) (snd v2)); auto.
Qed.

Lemma max_split : forall d v1 v2, max_wrt_dim d v1 v2 = v1 \/ max_wrt_dim d v1 v2 = v2.
Proof.
  intros. destruct d; simpl.
  - destruct (q_less_than (fst v1) (fst v2)); auto.
  - destruct (q_less_than (snd v1) (snd v2)); auto.
Qed.

Lemma min_bounded : forall r d v1 v2, Bounded r v1 -> Bounded r v2 -> Bounded r (min_wrt_dim d v1 v2).
Proof.
  intros. destruct (min_split d v1 v2); rewrite H1; assumption.
Qed.
Lemma max_bounded : forall r d v1 v2, Bounded r v1 -> Bounded r v2 -> Bounded r (max_wrt_dim d v1 v2).
Proof.
  intros. destruct (max_split d v1 v2); rewrite H1; assumption.
Qed.

Lemma b_split_min : forall r d v1 v2, neq_d d v1 v2 -> Bounded r v1 -> Bounded r v2 ->
    Bounded (fst (split d r (min_wrt_dim d v1 v2) (max_wrt_dim d v1 v2))) (min_wrt_dim d v1 v2).
Proof.
  intros. apply split_lemma_fst; try (apply neq_to_lt; assumption).
  - apply min_bounded; assumption.
  - apply max_bounded; assumption.
Qed.

Lemma b_split_max : forall r d v1 v2, neq_d d v1 v2 -> Bounded r v1 -> Bounded r v2 ->
    Bounded (snd (split d r (min_wrt_dim d v1 v2) (max_wrt_dim d v1 v2))) (max_wrt_dim d v1 v2).
Proof.
  intros. apply split_lemma_snd; try (apply neq_to_lt; assumption).
  - apply min_bounded; assumption.
  - apply max_bounded; assumption.
Qed.

Fixpoint insert (v : Vector) (d : Dim) (t : tree) : tree :=
  match t with
  | Point c => match c with
              | None => Point (Some v)
              | Some v' => if bneq_d d v v' then
                  Split d (mid d v v')
                    (Point (Some (min_wrt_dim d v v')))
                    (Point (Some (max_wrt_dim d v v')))
                          else
                            t
              end
  | Split X cv t1 t2 => if q_equal (fst v) cv then t else
                          if (q_less_than (fst v) cv) then [ (insert v Y t1) | cv | t2 ]
                          else [ t1 | cv | (insert v Y t2) ]
  | Split Y cv t1 t2 => if q_equal (snd v) cv then t else
                          if (q_less_than (snd v) cv) then [ (insert v X t1) ~ cv ~ t2 ]
                          else [ t1 ~ cv ~ (insert v X t2) ]
  end.

#[export] Hint Unfold insert mid max_wrt_dim min_wrt_dim insert : core.

(* Definition coord_d (d : Dim) (v : Vector) :=
  match d with
  | X => fst v
  | Y => snd v
  end.

Lemma gen_bound_lemma_d1 :  forall d (v1 : Vector) (r1 r2 r3 : Rectangle) (cv : Qc),
    Bounded r3 v1 -> coord_d d v1 < cv -> Aligned cv d r1 r2 -> Merged r1 r2 r3 -> Bounded r1 v1.
Proof.
  intros. destruct d.
  - eapply generalized_bounded_lemma_x1.
    + apply H.
    + apply H0.
    + apply H1.
    + assumption.
   - eapply generalized_bounded_lemma_y1.
    + apply H.
    + apply H0.
    + apply H1.
    + assumption.
Qed. *)

Theorem insertion_correctness : forall r t v d, KDT r t -> Bounded r v -> KDT r (insert v d t).
Proof with eauto.
  intros. generalize dependent d. induction H.
  - simpl. auto.
  - simpl. intros d. destruct (bneq_d d v v0) eqn:DEQ.
    + econstructor; apply neq_d_iff_true in DEQ.
      * constructor. apply b_split_min; eauto.
      * constructor. apply b_split_max; eauto.
      * destruct d.
        -- constructor; simpl; try reflexivity. destruct (q_less_than (fst v) (fst v0));
           try reflexivity. rewrite Qcplus_comm. reflexivity.
        -- constructor; simpl; try reflexivity. destruct (q_less_than (snd v) (snd v0));
           try reflexivity. rewrite Qcplus_comm. reflexivity.
      * constructor; destruct d; reflexivity.
    + auto.
  - intros d0. destruct d.
    + simpl. destruct (q_equal (fst v) cv) eqn:DEQ; try eauto.
      destruct (q_less_than (fst v) cv) eqn:INEQ.
      * apply KDT_Split with r1 r2; try apply IHKDT1; try assumption.
        eapply generalized_bounded_lemma_x1.
        -- apply H0.
        -- apply qlt_iff_true in INEQ. apply INEQ.
        -- apply H2.
        -- assumption.
      * apply KDT_Split with r1 r2; try apply IHKDT2; try assumption.
        eapply generalized_bounded_lemma_x2.
        -- apply H0.
        -- apply qeq_false_iff in DEQ. apply qgt_if_false in INEQ; try apply INEQ; assumption.
        -- apply H2.
        -- assumption.
    + simpl. destruct (q_equal (snd v) cv) eqn:DEQ; try eauto.
      destruct (q_less_than (snd v) cv) eqn:INEQ.
      * apply KDT_Split with r1 r2; try apply IHKDT1; try assumption.
        eapply generalized_bounded_lemma_y1.
        -- apply H0.
        -- apply qlt_iff_true in INEQ. apply INEQ.
        -- apply H2.
        -- assumption.
      * apply KDT_Split with r1 r2; try apply IHKDT2; try assumption.
        eapply generalized_bounded_lemma_y2.
        -- apply H0.
        -- apply qeq_false_iff in DEQ. apply qgt_if_false in INEQ; try apply INEQ; assumption.
        -- apply H2.
        -- assumption.
Qed.

(**)
