Require Import VST.floyd.proofauto.
Require Import Coq.micromega.Psatz.

Local Open Scope logic.

Lemma sepalg_Tsh: sepalg.nonidentity Tsh.
Proof.
  apply top_share_nonidentity.
Qed.

Lemma andp_eliminate:
  forall (A : Type) (NA : NatDed A) (P Q Q' : A),
  Q |-- Q' -> P && Q |-- P && Q'.
Proof.
  intros.
  apply andp_derives.
  - apply derives_refl.
  - apply H.
Qed.

Lemma saturate_local_or:
  forall (b : bool) p1 p2, 
  !! (is_pointer_or_null p1) && !! (is_pointer_or_null p2)
  |-- !! (is_pointer_or_null (if b then p1 else p2)).
Proof.
  intros.
  destruct b; entailer.  
Qed.
(* #[export] *)Hint Resolve saturate_local_or: saturate_local.

Lemma tc_val_or:
  forall (b : bool) p1 p2 ty, 
  !! (tc_val ty p1) && !! (tc_val ty p2)
  |-- !! (tc_val ty (if b then p1 else p2)).
Proof.
  intros.
  destruct b; entailer.  
Qed.
(* #[export] *)Hint Resolve tc_val_or: saturate_local.

Lemma valid_pointer_or:
  forall (b : bool) p1 p2, 
    valid_pointer p1 * valid_pointer p2 
    |-- valid_pointer (if b then p1 else p2).
Proof.
  intros.
  destruct b; entailer. 
Qed.
(* #[export] *)Hint Resolve valid_pointer_or: valid_pointer.

Ltac strip_0 := 
  rewrite Z.add_0_l in *; rewrite Z.add_0_r in *.

Ltac arith_bool :=
  repeat match goal with
  | x: ?a >= ?b |- _  => 
    rewrite Z.ge_le_iff in x; rewrite <- Z.ltb_ge in x
  | x: ?a < ?b  |- _  => rewrite Zlt_is_lt_bool in x
  end.
  
Lemma arith_bool_1 : forall a b, 
  (if a <? b then true else a =? b) = (a <=? b).
Proof.
  intros.
  destruct (a <=? b) eqn:E.
  - rewrite Z.leb_le in E.
    destruct (a <? b) eqn:E'.
    + reflexivity.
    + assert (a = b).
      { rewrite Z.ltb_ge in E'. lia. }
      rewrite H. apply Z.eqb_refl.
  - rewrite Z.leb_gt in E. 
    destruct (a <? b) eqn:E'.
    + rewrite Z.ltb_lt in E'. lia. 
    + destruct (a =? b) eqn:E''.
      * rewrite Z.eqb_eq in E''. 
        rewrite E'' in E. lia.
      * reflexivity.
Qed.

Lemma zlt_bool_1 : forall a b, 
  (a <? b) = (if zlt a b then true else false).
Proof.
  intros.
  destruct (a <? b) eqn:E.
  - rewrite zlt_true.
    + reflexivity.
    + rewrite <- Z.ltb_lt. exact E.
  - rewrite zlt_false.
    + reflexivity.
    + rewrite Z.ge_le_iff. rewrite <- Z.ltb_ge. exact E.
Qed.

Lemma list_cons_app : forall {A : Type} (l1 : list A) (x : A), 
  exists (l2 : list A) (a : A), 
  x :: l1 = l2 ++ [a].
Proof.
  intros A l1. induction l1; intros.
  - exists nil, x. auto.
  - specialize (IHl1 a).
    destruct IHl1 as [l2 [b H]].
    exists (x :: l2), b.
    rewrite H. reflexivity.
Qed.

Lemma true_Cne_neq: 
  forall x y, 
    typed_true tint (force_val (sem_cmp_pp Cne x y)) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H.
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?;
    try destruct (Int.eq i i0) eqn:?;
    simpl in H; try inversion H.
    intro. 
    inversion H0. subst i. 
    try pose proof (Int64.eq_spec i0 i0). 
    try pose proof (Int.eq_spec i0 i0). 
    rewrite Heqb in *.
    contradiction. 
  - intro. inversion H0.
  - intro. inversion H0.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. inversion H.  
      * intro. inversion H0.
        subst i.
        pose proof (Ptrofs.eq_spec i0 i0). rewrite Heqb1 in H2.
        contradiction.  
    + intro. inversion H0. subst b. contradiction.
Qed.

Lemma true_Ceq_eq: 
  forall x y, 
    typed_true tint (force_val (sem_cmp_pp Ceq x y)) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?; 
    try destruct (Int.eq i i0) eqn:?; 
    simpl in H; try inversion H.
    f_equal.
    try pose proof (Int64.eq_spec i i0).
    try pose proof (Int.eq_spec i i0).
    rewrite Heqb in *. auto.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i Int64.zero) eqn:?; 
    try destruct (Int.eq i Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i0 Int64.zero) eqn:?; 
    try destruct (Int.eq i0 Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0) eqn:E.
    + subst b. 
      destruct (Ptrofs.eq i i0) eqn:E'.
      * pose proof (Ptrofs.eq_spec i i0). rewrite E' in H0. subst i.
        reflexivity.
      * simpl in H. inversion H.
    + simpl in H. inversion H.
Qed.

Lemma false_Cne_neq: 
  forall x y, 
    typed_false tint (force_val (sem_cmp_pp Cne x y)) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?; 
    try destruct (Int.eq i i0) eqn:?; 
    simpl in H; try inversion H.
    f_equal.
    try pose proof (Int64.eq_spec i i0).
    try pose proof (Int.eq_spec i i0).
    rewrite Heqb in *. auto.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i Int64.zero) eqn:?; 
    try destruct (Int.eq i Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i0 Int64.zero) eqn:?; 
    try destruct (Int.eq i0 Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. reflexivity.  
      * simpl in H. inversion H.
    + simpl in H. inversion H.
Qed.

Lemma false_Ceq_eq: 
  forall x y, 
    typed_false tint (force_val (sem_cmp_pp Ceq x y)) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H. 
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H.
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?;
    try destruct (Int.eq i i0) eqn:?;
    simpl in H; try inversion H.
    intro. 
    inversion H0. subst i. 
    try pose proof (Int64.eq_spec i0 i0). 
    try pose proof (Int.eq_spec i0 i0). 
    rewrite Heqb in *.
    contradiction. 
  - intro. inversion H0.
  - intro. inversion H0.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. inversion H.
      * intro. inversion H0. subst b i. pose proof (Ptrofs.eq_spec i0 i0). 
        rewrite Heqb1 in H2. contradiction.
    + intro. inversion H0. contradiction. 
Qed.

Ltac pointer_destructor :=
  repeat match goal with
  | x : typed_false tint (force_val (sem_cmp_pp Ceq ?Y ?Z)) |- _  =>
    try apply false_Ceq_eq in x; try contradiction
  | x : typed_true tint (force_val (sem_cmp_pp Ceq ?Y ?Z)) |- _ =>
    try apply true_Ceq_eq in x; try subst Y; try (assert_PROP False; entailer!)
  | x : typed_true tint (force_val (sem_cmp_pp Cne ?Y ?Z)) |- _ =>
    try apply true_Cne_neq in x; try contradiction
  | x : typed_false tint (force_val (sem_cmp_pp Cne ?Y ?Z)) |- _ =>
    try apply false_Cne_neq in x; try subst Y; try (assert_PROP False; entailer!)
  | _   => idtac
  end.

Ltac forward_if_wrp := forward_if; try pointer_destructor.

Fact minsigned_lt_maxsigned : Int.min_signed < Int.max_signed. 
Proof. 
  unfold Int.min_signed, Int.max_signed.
  unfold Int.half_modulus.
  unfold Int.modulus.
  unfold Int.wordsize.
  unfold Wordsize_32.wordsize.
  simpl. lia. 
Qed.