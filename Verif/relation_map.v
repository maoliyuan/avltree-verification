Require Import RBT.Verif.RBtree_Type.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.

Section Section_relation_map.

Context { rbt : RBtree_setting }.
Existing Instance rbt.

Definition relate_map := Key -> option Value .
(*example : *)
Definition relate_default : relate_map  := fun  x => None.


(*Operations*)
Definition v_update (k:Key)(v: Value )(m: relate_map):relate_map :=
 fun x =>  if  k =?x then Some v else m x.
Definition tag_update (t: Tag) (m : relate_map ) : relate_map :=
 fun x => match (m x) with 
        | None => None 
        | Some v' => Some (f v' t)
        end.
Definition segment_update (lo hi : Key) (delta : Tag) (m : relate_map) : relate_map :=
 fun x => match  (m x) with
        |None => None
        |Some v => if   (lo <=? x) && ( x <=? hi)  then Some (f v delta)
                   else Some v
        end.
Definition k_delete (k: Key) (m : relate_map) : relate_map :=
 fun x => if k =? x then None else m x.
Definition combine (m1 m2: relate_map ) : relate_map :=
  fun x => match m1 x , m2 x with 
          |None, Some v => Some v
          |Some v, None => Some v
          |_ ,_ => None
          end.


(*---------------------  Operation Lemmas -----------------------*)
(*v_update *)
  Theorem v_update_twice : forall m k v1 v2 ,
          v_update k v1  (v_update k v2 m) = v_update k v1 m.
  Proof.
    intros; extensionality x.
    unfold v_update.
    destruct (k =? x).
    - reflexivity.
    - reflexivity.
  Qed.
  Theorem v_update_comm : forall k0 v0 k1 v1 m, (k0 < k1 \/ k1 < k0) ->
    v_update k0 v0 (v_update k1 v1 m) = v_update k1 v1 (v_update k0 v0 m).
  Proof.
    intros.
    extensionality x.
    unfold v_update.
    remember (k0 =? x) as u. remember (k1 =? x) as v.
    destruct u .
    assert (  k0 = x). {  apply (eqb_eq_k _ ). auto. }
    destruct v.
    assert ( k1 = x). { apply (eqb_eq_k _ ). auto. } subst. destruct H. exfalso.  solve_order. solve_order.
    reflexivity.
    reflexivity.
  Qed.
  Theorem tag_update_default : forall m , tag_update default m = m.
  Proof.
    intros.
    extensionality t.
    unfold tag_update.
    destruct (m t).
    - rewrite f_defualt. reflexivity.
    - auto.
  Qed.
  Theorem tag_update_defaultmap : forall m , tag_update  m relate_default = relate_default.
  Proof.
    intros.
    extensionality t.
    unfold tag_update.
    unfold relate_default.
    reflexivity.
  Qed.
  Theorem tag_update_twice : forall m x y , tag_update x (tag_update y m) = tag_update (Optt x y) m.
  Proof.
    intros.
    extensionality k.
    unfold tag_update.
    destruct (m k).
    -  rewrite f_tag. reflexivity.
    - reflexivity.
  Qed.
  Theorem v_up_tagupdate_iff : forall k v t m, 
   v_update k (f v t) (tag_update t m) = tag_update t (v_update k v m).
  Proof.
    intros.
    extensionality x.
    unfold v_update, tag_update.
    destruct (m x).
    - destruct (k =? x). reflexivity. reflexivity.
    - destruct (k =? x). reflexivity. reflexivity.
  Qed.
  Theorem tag_v_update : forall k v t m ,
             tag_update t (v_update k v m) = v_update k (f v t) (tag_update t m).
  Proof.
    intros.
    extensionality x.
    unfold tag_update , v_update.
    destruct (m x), (k=? x).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
  (*TODO TODO*)
  (* Theorem seg_tag_update : forall  lo hi t t0 m ,
   segment_update lo hi t (tag_update t0 m) =
     tag_update t0 (segment_update lo hi t m).
  Proof.
    intros.
    extensionality x.
    unfold segment_update, tag_update.
    destruct (m x).
    destruct (lo <=? x) ,( x <=? hi).
    simpl. rewrite f_twice_comm. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    reflexivity.
  Qed. *)
  Theorem k_delete_not_in : forall m k ,
   m k = None -> k_delete k m = m.
  Proof.
    intros.
    extensionality x.
    unfold k_delete.
    remember (k =? x).
    destruct b.
    - assert (k = x).
      { eapply eqb_eq_k. symmetry. auto. }
      rewrite <- H0.
      symmetry. auto.
    - reflexivity.
  Qed.
  Theorem v_update_delete :
   forall k v m ,
     m k = Some v ->
     v_update k v (k_delete k m) = m.
  Proof.
    intros.
    extensionality x.
    unfold v_update.
    remember (k =? x ).
    destruct b.
    - assert ( k = x). { eapply eqb_eq_k. auto. }
      subst. auto.
    - unfold k_delete. 
      rewrite <- Heqb.
      auto.
   Qed.
  Theorem k_delete_tag_update : forall m k t,
    k_delete k (tag_update t m) = tag_update t (k_delete k m).
  Proof.
    intros.
    extensionality x.
    unfold k_delete.
    unfold tag_update.
    remember (k =? x).
    destruct b.
    - reflexivity.
    - reflexivity.
  Qed.
  Theorem combine_xyz: forall x y z,
   x = y -> combine x z = combine y z.
  Proof.
   intros.
   rewrite H.
   reflexivity.
  Qed.
  Theorem combine_comm : forall m1 m2 , 
    combine m1 m2 = combine m2 m1.
  Proof.
    intros.
    unfold combine.
    extensionality x.
    destruct (m1 x) ,(m2 x).
    auto. auto. auto. auto.
  Qed.
  Theorem combine_default: forall m ,
   combine m relate_default = m.
  Proof.
    intros.
    extensionality x.
    unfold combine.
    destruct (m x).
    - simpl. reflexivity.
    - reflexivity.
  Qed.


(*Restriction *)
Definition restriction (m : relate_map)  (pm:  Key -> Prop) : Prop :=
 forall x,   ~ m x = None -> pm x .

Definition union (p1 p2 : Key -> Prop) := fun k => p1 k \/ p2 k.
Definition inter (p1 p2 : Key -> Prop) := fun k => p1 k /\ p2 k.
Definition sub (p1 p2 : Key ->  Prop) := fun k => p1 k /\ ~ p2 k.
Definition sym_diff (p1 p2 : Key -> Prop) := sub (union p1 p2) (inter p1 p2).
Definition add_one (k : Key) (p : Key -> Prop) := fun x => x = k \/ p x.
Definition an_ele (k : Key) : Key -> Prop := fun x => x = k.

End Section_relation_map.

Ltac super_destruct H :=
  cbv beta delta [add_one union] in H;
  match type of H with
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              super_destruct H;
              super_destruct H0
  | _ \/ _ => destruct H as [H | H];
              super_destruct H
  | _ => idtac
  end.

Section Section_relation_map_2.

Context { rbt : RBtree_setting }.
Existing Instance rbt.

(*RESTRICTION THEOREMS*)
  Lemma restriction_default : forall pm , restriction relate_default pm.
  Proof.
    intros.
    unfold restriction. intros.
    unfold relate_default in H.
    exfalso. apply H. auto.
  Qed.
  Lemma res_vupdate : forall   cts k v p, restriction cts p -> restriction (v_update k v cts) (add_one k p) .
  Proof.
    intros.
    unfold restriction; intros. unfold add_one.
    unfold v_update in H0.
    remember (k =? x).
    destruct b.
    - left. apply (eqb_eq_k  x k). symmetry. rewrite eqb_comm. auto.
    - right. unfold restriction in H. apply H. auto.
  Qed.
  Lemma res_tagupdate : forall cts t p, restriction cts p -> restriction (tag_update t cts) p.
  Proof.
    intros ; unfold restriction; intros.
    unfold tag_update in H0.
    unfold  restriction in H. pose proof H x. destruct (cts x).
    - apply H1. unfold not. intros. inversion H2.
    - exfalso.  apply H0. auto.
  Qed.
  Lemma seg_v_update: forall lo hi t k v m ,
   segment_update lo hi t (v_update k v m)=
     v_update k (if ( lo <=? k ) && ( k <=? hi ) then f v t else v) 
       (segment_update lo hi t m).
  Proof.
    unfold restriction; intros.
    extensionality x.
    unfold segment_update, v_update.
    remember ( k =? x) as u.
    remember ( lo <=? k) as w.
    remember ( k <=? hi) as r.
    symmetry in Hequ, Heqw , Heqr.
    destruct u.
    - assert (k = x). { eapply eqb_eq_k; try eassumption. }
      subst.
      destruct (lo <=? x),(x <=? hi) ; first [reflexivity ].
    - destruct (m x).
      reflexivity.
      reflexivity.
  Qed.
  Lemma change_up_notin: forall lo hi m pm t,
   restriction m pm ->
   (forall k, (  lo <= k /\  k <= hi) -> ~ pm k ) ->
     segment_update lo hi t m = m.
  Proof.
    intros. extensionality k.
    pose proof H0 k.
    unfold segment_update.
    unfold restriction in H.
    pose proof H k.
    destruct (m k).
    - remember ( lo <=? k) as u. remember ( k <=? hi) as w. symmetry in Hequ, Heqw.
      destruct u, w.
      assert ( lo <= k /\ k <= hi). { split.  eapply lteb_lte; try eassumption. eapply lteb_lte; try eassumption. }
      exfalso. pose proof H1 H3. apply H4. apply H2. discriminate.
      simpl. reflexivity. reflexivity. reflexivity.
    - reflexivity.
  Qed.
  Lemma change_up_allin: forall lo hi m pm t,
   restriction m pm ->
   (forall k, pm k -> (lo <= k /\  k <= hi)  ) ->
     segment_update lo hi t m = tag_update t m.
  Proof.
    intros. extensionality k.
    pose proof H0 k.
    unfold segment_update , tag_update.
    unfold restriction in H.
    pose proof H k.
    destruct (m k).
    - remember ( lo <=? k) as u. remember ( k <=? hi) as w. symmetry in Hequ, Heqw.
      assert ( lo <= k /\ k <= hi). { apply H1.  apply H2. discriminate. } destruct H3.
      destruct u, w. reflexivity.  solve_order. solve_order. solve_order.
    - reflexivity.
  Qed.
  Lemma k_delete_update: forall m pm k v,
    restriction m pm -> ~ pm k ->
      k_delete k (v_update k v m) = m.
  Proof.
    unfold restriction.
    intros.
    extensionality x.
    pose proof H x ; clear H.
    unfold k_delete.
    remember (k =? x).
    symmetry in Heqb; destruct b.
    - destruct (m x);[ | reflexivity].
      assert (k = x) by ( eapply eqb_eq_k; try eassumption); subst.
      assert (Some v0 <> None).
      { unfold not; intros. inversion H. }
      apply H1 in H.
      apply H0 in H.
      inversion H.
    - unfold v_update.
      rewrite Heqb.
      reflexivity.
  Qed.

(*Combine Restriction Lemmas*)
Theorem res_combine : forall a b pa pb ,
 restriction a pa -> restriction b pb ->
   (forall k , pa k -> pb k -> False ) ->
   (forall k , pb k -> pa k -> False ) ->
     restriction ( combine a b) (union pa pb).
Proof.
  unfold restriction; unfold combine; unfold union; intros.
  pose proof H x.  pose proof H0 x. pose proof H1 x. pose proof H2 x.
  destruct (a x) , (b x).
  - exfalso. apply H3. auto.
  - left. apply H4.  unfold not; intros. inversion H8.
  - right. apply H5. unfold not; intros. inversion H8.
  - exfalso. apply H3. auto.
Qed.
Theorem combine_asso: forall x y z px py pz , restriction x px -> restriction y py -> restriction z pz -> 
 (forall k , px k -> py k -> False ) ->
   (forall k , px k -> pz k -> False ) ->
      (forall k , pz k -> py k -> False ) ->
 combine x ( combine y z) = combine y ( combine x z ).
Proof.
  intros.
  extensionality k.
  unfold combine.
  pose proof H k.
  pose proof H0 k.
  pose proof H1 k.
  pose proof H2 k.
  pose proof H3 k.
  pose proof H4 k.
  remember (x k) as u.
  remember (y k) as w.
  remember (z k) as r.
  destruct u, w.
  - assert (Some v <> None). { unfold not. intros. inversion H11. }
  assert (Some v0 <> None). { unfold not. intros. inversion H12. }
  apply H5 in H11. apply H6 in H12. pose proof H8 H11 H12. inversion H13.
  - destruct r.
    +
     reflexivity.
    + reflexivity.
  - destruct r.
    +
     reflexivity.
    + reflexivity.
  - destruct r.
    +
     reflexivity.
    + reflexivity.
Qed.
Theorem v_update_combine : forall k v m1 m2 pm1 pm2, restriction m1 pm1 -> restriction m2 pm2 ->
  (forall x , pm1 x -> pm2 x -> False ) ->
  (~ pm1 k) ->
  combine m1 ( v_update k v m2 ) = v_update k v ( combine m1 m2).
Proof.
  intros.
  extensionality x.
  unfold combine at 1.
  pose proof H x. pose proof H0 x. pose proof H1 x. clear H H0 H1 .
  remember  ( m1 x ) as u.
  remember  ( m2 x)  as w.
  remember ( k =? x ) as r.
  destruct u, w.
  - assert (pm1 x). { apply H3.  unfold not.  intros.  inversion H. }
    assert (pm2 x). { apply H4.  unfold not.  intros.  inversion H0. }
    pose proof H5 H H0. inversion H1.
  - assert (pm1 x). { apply H3.  unfold not.  intros.  inversion H. }
    unfold v_update. destruct r.
    +  assert (k = x). { apply (eqb_eq_k k x). symmetry . auto. } subst.
       exfalso. apply H2. auto.
    +  rewrite <- Heqr. unfold combine.  rewrite <- Heqw. rewrite <- Hequ. reflexivity.
  -  unfold v_update. destruct r.
    assert (pm2 x). { apply H4.  unfold not.  intros.  inversion H. }
    + rewrite <- Heqr.
      reflexivity.
    + rewrite <- Heqr. unfold combine.  rewrite <- Heqw. rewrite <- Hequ. reflexivity.
  - unfold v_update.
  destruct r.
   + rewrite <- Heqr. reflexivity.
   +  rewrite <- Heqr. unfold combine. rewrite <-Hequ. reflexivity.
Qed.
Theorem tagupdate_combine : forall a b t ,
        tag_update t (combine a b) = combine (tag_update t a) (tag_update t b).
Proof.
  intros; extensionality x ; intros.
  unfold tag_update, combine.
  destruct (a x) , (b x).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
Theorem segment_combine: forall l r lo hi t pl pr,
 restriction l pl -> restriction r pr ->
   (forall k, pl k -> ~ pr k) ->
     (forall k, pr k-> ~ pl k) ->
       segment_update lo hi t (combine l r) =
         combine (segment_update lo hi t l) (segment_update lo hi t r).
Proof.
  unfold restriction; intros.
  extensionality x.
  pose proof H1 x. pose proof H2 x. clear H1. clear H2.
  pose proof H x. pose proof H0 x. clear H. clear H0.
  unfold segment_update, combine.
  remember (l x) as u ; remember (r x) as v.
  destruct u, v.
  - exfalso. assert (pl x). { apply H1. discriminate. }
    assert (pr x). { apply H2. discriminate. }
    apply H3; try eassumption.
  - destruct (lo <=? x), ( x <=? hi); first [ reflexivity ].
  - destruct (lo <=? x), ( x <=? hi); first [ reflexivity ].
  - reflexivity.
Qed.
Theorem k_delete_combine : forall x y k px py, 
  restriction x px -> restriction y py ->
   (forall z , px z -> py z -> False ) ->
     px k -> ~ py k ->
       k_delete k (combine x y) = combine (k_delete k x) y.
Proof.
  unfold restriction.
  intros.
  extensionality z.
  pose proof H1 z. clear H1.
  pose proof H z.
  pose proof H0 z.
  clear H H0.
  unfold k_delete at 1.
  remember (k =? z). symmetry in Heqb.
  destruct b.
  + assert (k = z).
    { eapply eqb_eq_k; try eassumption. }
    subst.
    unfold combine.
    unfold k_delete.
    rewrite Heqb.
    destruct (y z);[ |reflexivity].
    assert (Some v <> None).
    { unfold not. intros. inversion H. }
    apply H5 in H.
    apply H4 in H2; [ | auto].
    inversion H2.
  + unfold combine.
    unfold k_delete.
    rewrite Heqb.
    reflexivity.
Qed.

End Section_relation_map_2.

