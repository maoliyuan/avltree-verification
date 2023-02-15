From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.

Section Section_Abstract.

Context {rbt:RBtree_setting}. 
Existing Instance rbt. 

Inductive Abs : RBtree -> relate_map -> Prop :=
|Abs_E : Abs Empty (relate_default)
|Abs_T: forall a b left right k v t c,
  Abs left a ->
  Abs right b ->
  Abs (T c left k v t right) ( tag_update t (v_update k v (combine  a b) )).
Inductive Abs_half : list Half_tree -> relate_map -> Prop :=
|Abs_nil : Abs_half nil relate_default
|Abs_cons : forall l lmap kb kco k kv kt ktree tmap lt,
   Abs_half l lmap -> Abs ktree tmap -> lt = accumulate_tag_for_ht l ->
     Abs_half ((kb,kco,k,kv,kt,ktree)::l) (combine lmap (tag_update (Optt lt kt) (v_update k kv tmap))).

(*Simple theorems*)
  Theorem Abs_exist : forall tree, exists x, Abs tree x .
  Proof.
    intros.
    induction tree.
    - exists relate_default.
      apply Abs_E.
    - destruct IHtree1.
      destruct IHtree2.
      exists ( tag_update t (v_update k v (combine x x0) )).
      eapply Abs_T; try eassumption.
  Qed.
  Theorem Abs_exist_h : forall h, exists x, Abs_half h x .
  Proof.
    intros.
    induction h.
    - exists relate_default.
      apply Abs_nil.
    - destruct a. repeat destruct p.
      destruct IHh.
      pose proof Abs_exist r.
      destruct H0.
      exists (combine x (tag_update (Optt (accumulate_tag_for_ht h) t) (v_update k v x0))).
      apply Abs_cons; try eassumption.
      auto.
  Qed.
  Theorem Abs_unique : forall tree x y, Abs tree x -> Abs tree y -> x = y .
  Proof.
    intro.
    induction tree.
    - intros. inversion H.
      inversion H0.
      reflexivity.
    - intros.
      inversion H. subst.
      inversion H0. subst.
      pose proof IHtree1 _ _ H8 H10.
      subst.
      pose proof IHtree2 _ _ H9 H11.
      subst.
      reflexivity.
  Qed.
  Theorem tag_tree_abs : forall tree t map , Abs tree map -> Abs (tag_tree_t t tree) (tag_update t map).
  Proof.
    intros.
    induction H.
    - simpl.  rewrite tag_update_defaultmap. apply Abs_E.
    - simpl.
      rewrite tag_update_twice. eapply Abs_T; try eassumption.
  Qed.
  Theorem makeBlack_abs : forall s cts , Abs s cts ->
    Abs (makeBlack s) cts .
  Proof.
    intros.
    inversion H.
    - simpl. subst. auto.
    - simpl. subst. apply Abs_T. auto. auto.
  Qed.
  Theorem makeRed_abs : forall s cts , Abs s cts ->
    Abs (makeRed s) cts .
  Proof.
    intros.
    inversion H.
    - simpl. subst. auto.
    - simpl. subst. apply Abs_T. auto. auto.
  Qed.
  
(*RESTRICTION AND TREE*)
  Lemma search_relate :
    forall k t cts lo hi, SearchTree' lo t hi -> Abs t cts ->  ~ cts k = None  ->  lo < k /\  k < hi .
  Proof.
    intros.
    induction H0.
    + intros. unfold relate_default in H1. unfold not in H1.
    assert (False). apply H1; reflexivity. inversion H0.
    + intros. unfold tag_update, v_update, combine in  H1.
    inversion H. subst.
    remember (Equal_bool k0 k) as h.
    destruct h.
    - symmetry in Heqh.
    apply eqb_eq_k in Heqh. subst. split. apply search_popro with left. auto. apply search_popro with right. auto.
    - remember (a k) as kl. remember (b k) as kr.
      destruct kl.
      {
      destruct kr. unfold not in H1.
    assert (False). apply H1; reflexivity. inversion H0.
      apply IHAbs1. eapply search_popro2. apply H9. eapply search_popro. apply H10. unfold not. intros. inversion H0.
       }
      {
      destruct kr. apply IHAbs2. eapply search_popro3.  2: eapply search_popro; apply H9. auto. unfold not. intros. inversion H0.
      unfold not in H1.
    assert (False). apply H1; reflexivity. inversion H0.
      }
  Qed.
  Theorem restriction_rb : forall t lo hi cts , SearchTree' lo t hi -> Abs t cts -> restriction cts (fun x => lo < x /\ x <hi).
  Proof.
    intros.
    unfold restriction.
    intros.
    eapply search_relate ; try eassumption.
  Qed.
  Theorem restriction_rb_v_hi : forall t lo  cts k v , 
  SearchTree' lo t k -> Abs t cts -> restriction (v_update k v cts) (fun x => lo < x /\ (x <= k )) .
  Proof.
    intros. unfold restriction. intros.
    unfold v_update in H1.
    remember (k =? x).
    destruct b.
    - symmetry in Heqb. apply eqb_eq_k in Heqb. subst. split. eapply search_popro; try eassumption.  right; reflexivity.
    - pose proof search_relate _ _ _ _ _ H H0 H1.
      destruct H2.
      split. auto. left; auto.
  Qed.
  Theorem restriction_rb_v_lo : forall t hi  cts k v , 
  SearchTree' k t hi -> Abs t cts -> restriction (v_update k v cts) (fun x => k <= x   /\ x < hi) .
  Proof.
    intros. unfold restriction. intros.
    unfold v_update in H1.
    remember (k =? x).
    destruct b.
    - symmetry in Heqb. apply eqb_eq_k in Heqb. subst. split. right; reflexivity. eapply search_popro; try eassumption. 
    - pose proof search_relate _ _ _ _ _ H H0 H1.
      destruct H2.
      split.  left; auto. auto.
  Qed.
  Theorem restriction_half : forall h lo hi hmap , SearchTree_half lo h hi -> Abs_half h hmap -> restriction hmap (fun x => ( x <= lo) \/ ( hi <= x )).
  Proof.
    intros; unfold restriction; intros.
    revert  hmap x H0 H1.
    induction H.
    - intros. inversion H0. subst. unfold relate_default in H1. exfalso. unfold not in H1. apply H1. reflexivity.
    - intros. inversion H4. subst.
       pose proof IHSearchTree_half lmap x H14.
       unfold  combine in H5.
       remember (lmap x) as m.
       remember (v_update k kv tmap x) as n.
       destruct m,n.
       { exfalso.  apply H5.
        unfold tag_update.
        rewrite <- Heqn.
         auto. }
       { unfold tag_update in H5. rewrite <- Heqn in H5.
        apply H6 in H5.  destruct H5.  left. pose proof search_popro _ _ _ H1. TR 5.  right.  auto. }
       { pose proof search_popro _ _ _ H1. 
         pose proof restriction_rb_v_hi tree lo  tmap k kv  H1 H15.  unfold restriction in H8.
         assert ( v_update k kv tmap x <> None).
         { rewrite <- Heqn.
           unfold not; intros.
           inversion H9. }
         pose proof H8 x H9. destruct H10. left. tr.    }
       { exfalso. apply H5. unfold tag_update.
        rewrite <- Heqn. auto. }
    - intros. inversion H4. subst.
       pose proof IHSearchTree_half lmap x H14.
       unfold  combine in H5.
       remember (lmap x) as m.
       remember (v_update k kv tmap x) as n.
       destruct m,n.
       { exfalso. apply H5.
         unfold tag_update.
        rewrite <- Heqn.
         auto. }
       { unfold tag_update in H5.
        rewrite <- Heqn in H5. apply H6 in H5.  destruct H5.  left. auto.  right. TR 5. }
       { pose proof restriction_rb_v_lo tree hi tmap k kv  H1 H15.  unfold restriction in H7.
       assert (v_update k kv tmap x <> None).
       { rewrite <- Heqn.
           unfold not; intros.
           inversion H8. }
       pose proof H7 x H8. destruct H9. right. tr.     }
       { exfalso. apply H5.
         unfold tag_update.
        rewrite <- Heqn.
         auto. }
  Qed.
  Theorem restriction_half_plus : forall h lo hi olo ohi hmap , 
    SearchTree_half lo h hi -> SearchTree_half_out olo h ohi -> Abs_half h hmap ->
   restriction hmap (inter (fun x => ( x <= lo) \/ ( hi <= x )) (fun x => olo < x /\ x < ohi)).
  Proof.
    intro.
    induction h.
    - intros.
      inversion H1.
      subst.
      unfold restriction.
      intros.
      unfold not in H2.
      unfold relate_default in H2.
      contradiction.
    - intros.
      destruct a.
      repeat destruct p.
      destruct b.
      + inversion H; subst. inversion H0; subst.
        inversion H1; subst.
        inversion H17; subst.
        pose proof IHh _ _ _ _ _ H10 H16 H15; clear IHh.
        (* 使用 H12 或者 H9*)
        assert (SearchTree' (max_k lo0 low) r k).
        {
          pose proof lte_complete lo0 low.
          destruct H3.
          *  pose proof max_lte lo0 low H3.
             rewrite H4.
             auto.
          *  rewrite max_comm.
             pose proof max_lte low lo0 H3.
             rewrite H4.
             auto. }
        pose proof restriction_rb _ _ _ _ H3 H18.
        pose proof res_vupdate tmap k v _ H4.
        (* lo1 <= lo0 < k <= lo < hi <= hi0*)
        pose proof search_popro _ _ _ H12.
        assert  (forall kk : Key,
        inter (fun x : Key => x <= lo0 \/ hi <= x)
          (fun x : Key => lo1 < x /\ x < hi0) kk ->
        add_one k (fun x : Key => max_k lo0 low < x /\ x < k) kk ->
        False).
        { intros.
          unfold inter in H7;unfold add_one in H8.
          pose proof max_left lo0 low.
          repeat (
           match goal with 
           | H : (_ <= _ \/ _ <= _) /\ _ < _ /\ _ < _ |- _ => super_destruct H
           | H : _ \/ _  /\ _ |- _ => super_destruct H
           | H: _ = _  |- _ => subst; solve_order
           | |- False => solve_order
           end
          ). }
        assert  
       (forall kk : Key,
        add_one k (fun x : Key => max_k lo0 low < x /\ x < k) kk ->
        inter (fun x : Key => x <= lo0 \/ hi <= x)
          (fun x : Key => lo1 < x /\ x < hi0) kk -> False).
        { intros.
          unfold inter in H20;unfold add_one in H8.
          pose proof max_left lo0 low.
          repeat (
           match goal with 
           | H : (_ <= _ \/ _ <= _) /\ _ < _ /\ _ < _ |- _ => super_destruct H
           | H : _ \/ _  /\ _ |- _ => super_destruct H
           | H: _ = _  |- _ => subst; solve_order
           | |- False => solve_order
           end
          ). }
        pose proof res_combine lmap (v_update k v tmap) _ _ H2 H5 H7 H8;
        clear H7 H8.
        unfold restriction.
        intros.
        assert (hh :combine lmap (v_update k v tmap) x <> None).
        { unfold not.
          intros.
          unfold combine in H7, H8.
          unfold tag_update in H7.
          destruct (lmap x),  (v_update k v tmap x).
          contradiction.
          inversion H8.
          inversion H8.
          contradiction. }
        pose proof H20 x hh;clear H20 hh.
        pose proof search_popro _ _ _ H9.
        unfold union, inter, add_one in H8.
        unfold inter.
        pose proof min_right low lo1; pose proof max_right high hi0.
        pose proof min_left low lo1;pose proof max_left high hi0.
        pose proof max_right lo0 low;pose proof max_left high hi0.
        repeat (
          match goal with 
          | H : (_  \/ _ ) /\ _  /\ _ \/ _ \/ _ /\ _ |- _ => super_destruct H
          | |- _ /\ _ /\ _ => split
          | |- _ /\ _ => split
          | H: _ = _ |- _ => subst;tr
          | H: _ = _ |- _ \/ _ => subst;try (left;tr); try (right; tr)
          | |- _ < _ => tr
          | |- _ \/ _ => try (left;tr); try (right; tr)
          end
        ).

      + inversion H; subst. inversion H0; subst.
        inversion H1; subst.
        inversion H17; subst.
        pose proof IHh _ _ _ _ _ H10 H16 H15; clear IHh.
        (* 使用 H12 或者 H9*)
        assert (SearchTree' k r (min_k hi0 high)).
        {
          pose proof lte_complete hi0 high.
          destruct H3.
          *  pose proof min_lte hi0 high H3.
             rewrite H4.
             auto.
          *  rewrite min_comm.
             pose proof min_lte high hi0 H3.
             rewrite H4.
             auto. }
        pose proof restriction_rb _ _ _ _ H3 H18.
        pose proof res_vupdate tmap k v _ H4.
        (* lo1 <= lo0 < k <= lo < hi <= hi0*)
        pose proof search_popro _ _ _ H12.
        assert  (forall kk : Key,
        inter (fun x : Key => x <= lo \/ hi0 <= x)
          (fun x : Key => lo0 < x /\ x < hi1) kk ->
        add_one k (fun x : Key => k < x /\ x < min_k hi0 high)
          kk -> False).
        { intros.
          unfold inter in H7;unfold add_one in H8.
          pose proof min_left hi0 high.
          repeat (
           match goal with 
           | H : (_ <= _ \/ _ <= _) /\ _ < _ /\ _ < _ |- _ => super_destruct H
           | H : _ \/ _  /\ _ |- _ => super_destruct H
           | H: _ = _  |- _ => subst; solve_order
           | |- False => solve_order
           end
          ). }
        assert  (forall kk : Key,
        add_one k (fun x : Key => k < x /\ x < min_k hi0 high)
          kk ->
        inter (fun x : Key => x <= lo \/ hi0 <= x)
          (fun x : Key => lo0 < x /\ x < hi1) kk -> False).
        { intros.
          unfold inter in H20;unfold add_one in H8.
          pose proof min_left hi0 high.
          repeat (
           match goal with 
           | H : (_ <= _ \/ _ <= _) /\ _ < _ /\ _ < _ |- _ => super_destruct H
           | H : _ \/ _  /\ _ |- _ => super_destruct H
           | H: _ = _  |- _ => subst; solve_order
           | |- False => solve_order
           end
          ). }
        pose proof res_combine lmap (v_update k v tmap) _ _ H2 H5 H7 H8;
        clear H7 H8.
        unfold restriction.
        intros.
         assert (hh :combine lmap (v_update k v tmap) x <> None).
        { unfold not.
          intros.
          unfold combine in H7, H8.
          unfold tag_update in H7.
          destruct (lmap x),  (v_update k v tmap x).
          contradiction.
          inversion H8.
          inversion H8.
          contradiction. }
        pose proof H20 x hh;clear H20 hh.
        pose proof search_popro _ _ _ H9.
        unfold union, inter, add_one in H8.
        unfold inter.
        pose proof min_right low lo0;pose proof max_right high hi1.
        pose proof min_left low lo0;pose proof max_left high hi1. pose proof min_right hi0 high.
        repeat (
          match goal with 
          | H : (_  \/ _ ) /\ _  /\ _ \/ _ \/ _ /\ _ |- _ => super_destruct H
          | |- _ /\ _ /\ _ => split
          | |- _ /\ _ => split
          | H: _ = _ |- _ => subst;tr
          | H: _ = _ |- _ \/ _ => subst;try (left;tr); try (right; tr)
          | |- _ < _ => TR 5
          | |- _ \/ _ => try (left;tr); try (right; tr)
          end
        ). 
  Qed.

Definition Rb_equivalence  t1 t2 : Prop := forall cts , ( Abs t1 cts <-> Abs t2 cts).

End Section_Abstract.

Notation " x ~~ y " := (Rb_equivalence x y) (at level 70).

Ltac res_intros:= 
      let K  := fresh "K"  in
      let Hl := fresh "Hl" in
      let Hr := fresh "Hr" in
      intros K  Hl Hr;
      super_destruct Hl; super_destruct Hr;
      repeat (  subst; solve_order).
Ltac res_intro :=
     let Hl := fresh "Hl" in
      intros  Hl ;
      super_destruct Hl;
      repeat (  subst; solve_order).
Ltac res_simpl :=
 match goal with 
 | H : SearchTree' _ ?t _ , H0: Abs ?t ?cts |- restriction ?cts _ =>
                 apply (restriction_rb _ _ _ _  H H0)
 | H : SearchTree_half _ ?h _ , H0: Abs_half ?h ?hmap |- restriction ?hmap _ =>
                 apply (restriction_half _ _ _ _ H H0)
 | |- restriction ( v_update ?k ?v ?cts) _ =>
                 apply res_vupdate;res_simpl
 | |- restriction relate_default ?p => apply (restriction_default (fun x => x < x ))
 | |- restriction (tag_update ?t ?cts) _ => apply res_tagupdate; res_simpl
 | |- restriction (combine ?a ?b) _ => 
     apply res_combine; [ res_simpl | res_simpl | res_intros |res_intros ]
 end.



(*----------------  RedBlack Tree   Requivalence -----------------------*)
Section Section_Abstract_2.

Context {rbt:RBtree_setting}. 
Existing Instance rbt. 

(*Lemmas *)
Lemma Rb_equiv_trans: forall x y z, x ~~ y -> y ~~ z -> x ~~ z.
Proof.
  intros.
  split.
  - intros. apply H0. apply H. auto.
  - intros. apply H. apply H0. auto.
Qed.
Lemma Rb_equiv_symm: forall x y , x ~~ y -> y ~~ x .
Proof.
  intros.
  split.
  - intros. apply H. auto.
  - intros. apply H.  auto.
Qed.
Theorem  equiv_color : forall co1 co2 l k v t r,
 (T co1 l k v t r) ~~ (T co2 l k v t r).
Proof.
  intros.
  split.
  - intros. inversion H; subst. eapply Abs_T; try eassumption.
  - intros. inversion H; subst. eapply Abs_T; try eassumption.
Qed.
Theorem  equiv_left : forall co1 co2 l1 l2 k v t r, l1 ~~ l2 ->
 (T co1 l1 k v t r) ~~ (T co2 l2 k v t r).
Proof.
  intros.
  split.
  - intros. inversion H0; subst. eapply Abs_T; try eassumption. apply H. auto.
  - intros. inversion H0; subst. eapply Abs_T; try eassumption. apply H. auto.
Qed.
Theorem  equiv_right : forall co1 co2 l k v t r1 r2, r1 ~~ r2 ->
 (T co1 l k v t r1) ~~ (T co2 l k v t r2).
Proof.
  intros.
  split.
  - intros. inversion H0; subst. eapply Abs_T; try eassumption. apply H. auto.
  - intros. inversion H0; subst. eapply Abs_T; try eassumption. apply H. auto.
Qed.
Lemma comple_equi_strong : forall h lo hi tree t,
  SearchTree_half lo h hi -> SearchTree' lo tree hi ->  SearchTree' lo t hi ->
   tree ~~ t ->
      (complete_tree h tree) ~~   (complete_tree h t).
Proof.
  intro.
  induction h.
  - intros. simpl. auto.
  - intros.
    destruct a. repeat destruct p.
    destruct b.
    + inversion H. subst.
      repeat rewrite complete_tree_true.
      assert (SearchTree' lo0 (T c r k v t0 tree) hi).
      { eapply ST_T ; try eassumption.
        eapply search_popro3_lte; try eassumption.
       }
      assert (SearchTree' lo0 (T c r k v t0 t) hi).
      { eapply ST_T ; try eassumption.
        eapply search_popro3_lte; try eassumption.
       }
      assert ( (T c r k v t0 tree) ~~ (T c r k v t0 t) ).
      {
       unfold Rb_equivalence. intros. split.
       * intros. inversion H5. subst. eapply Abs_T; try eassumption.
         apply H2. auto.
       * intros. inversion H5. subst. eapply Abs_T; try eassumption.
         apply H2. auto.
      }
      eapply IHh; try eassumption.
    + inversion H. subst.
      repeat rewrite complete_tree_false.
      assert (SearchTree' lo (T c tree k v t0 r) hi0).
      { eapply ST_T ; try eassumption.
        eapply search_popro2_lte; try eassumption.
       }
      assert (SearchTree' lo (T c t k v t0 r) hi0).
      { eapply ST_T ; try eassumption.
        eapply search_popro2_lte; try eassumption.
       }
      assert ( (T c tree k v t0 r) ~~ (T c t k v t0 r) ).
      {
       unfold Rb_equivalence. intros. split.
       * intros. inversion H5. subst. eapply Abs_T; try eassumption.
         apply H2. auto.
       * intros. inversion H5. subst. eapply Abs_T; try eassumption.
         apply H2. auto.
      }
      eapply IHh; try eassumption.
Qed.
Lemma comple_equi : forall h lo hi tree t, Forall P h ->
  SearchTree_half lo h hi -> SearchTree' lo tree hi ->  SearchTree' lo t hi ->
   tree ~~ t ->
      (complete_tree h tree) ~~   (complete_tree h t).
Proof.
  intro.
  induction h.
  - intros. simpl. auto.
  - intros.
    destruct a. repeat destruct p.
    destruct b.
    + inversion H. subst.  inversion H6. simpl in H4. subst.
      inversion H0. subst. repeat rewrite complete_tree_true.
      assert (SearchTree' lo0 (T c r k v default tree) hi).
      { eapply ST_T ; try eassumption.
        eapply search_popro3_lte; try eassumption.
       }
      assert (SearchTree' lo0 (T c r k v default t) hi).
      { eapply ST_T ; try eassumption.
        eapply search_popro3_lte; try eassumption.
       }
      assert ( (T c r k v default tree) ~~ (T c r k v default t) ).
      {
       unfold Rb_equivalence. intros. split.
       * intros. inversion H8. subst. eapply Abs_T; try eassumption.
         apply H3. auto.
       * intros. inversion H8. subst. eapply Abs_T; try eassumption.
         apply H3. auto.
      }
      apply (IHh _ _ _ _ H7 H14 H4 H5 H8).
    + inversion H. subst. inversion H6. simpl in H4. subst.
      inversion H0. subst. repeat rewrite complete_tree_false.
      assert (SearchTree' lo (T c tree k v default r) hi0).
      { eapply ST_T ; try eassumption.
        eapply search_popro2_lte; try eassumption.
       }
      assert (SearchTree' lo (T c t k v default r) hi0).
      { eapply ST_T ; try eassumption.
        eapply search_popro2_lte; try eassumption.
       }
      assert ( (T c tree k v default r) ~~ (T c t k v default r) ).
      {
       unfold Rb_equivalence. intros. split.
       * intros. inversion H8. subst. eapply Abs_T; try eassumption.
         apply H3. auto.
       * intros. inversion H8. subst. eapply Abs_T; try eassumption.
         apply H3. auto.
      }
      eapply IHh; try eassumption.
Qed.

(*-equiv---ROTATE----PROPERTY---------------------------------------------*)
Theorem equiv_right_rotate : forall c0 k0 v0 t0 s c1 r1 k1 v1 t1 r2 lo hi ,
 SearchTree' lo
  (T c0 (T c1 r1 k1 v1 t1 r2) k0 v0 t0 s) hi ->
    (T c0 (T c1 r1 k1 v1 t1 r2) k0 v0 t0 s)  ~~
    (T c1 (tag_tree_t t1 r1) k1 (f v1 t1) t0 (T c0 (tag_tree_t t1 r2) k0 v0 default s )).
Proof.
  intros.
  inversion H; subst.
  inversion H8; subst.
  pose proof search_popro _ _ _ H9.
  pose proof search_popro _ _ _ H10.
  pose proof search_popro _ _ _ H11.
  split.
  - intro.
    inversion H3;subst. inversion H15; subst.
    erewrite <- (v_up_tagupdate_iff k1).
    erewrite tagupdate_combine.
    rewrite (combine_comm _ b).
    erewrite v_update_combine by (first [ res_simpl | res_intros | res_intro]).
    erewrite combine_asso by (first [ res_simpl | res_intros | res_intro]).
    erewrite v_update_comm; [| right; tr].
    erewrite <- v_update_combine by (first [ res_simpl | res_intros | res_intro]).
    eapply Abs_T; try eassumption.
    eapply tag_tree_abs; try eassumption.
    erewrite <- tag_update_default.
    rewrite combine_comm.
    eapply Abs_T; try eassumption.
    eapply tag_tree_abs; try eassumption.
 - intro.
   inversion H3; subst. inversion H16; subst.
   destruct r1, r2.
   + inversion H15;subst. inversion H17; subst.
     rewrite combine_comm; rewrite combine_default.
     rewrite combine_comm.
     rewrite tag_update_default.
     erewrite v_update_comm; [| left; tr].
     erewrite <- v_update_combine by (first [ res_simpl | res_intros | res_intro]).
     rewrite combine_comm.
     eapply Abs_T; try eassumption.
     rewrite <- (tag_update_defaultmap t1).
     rewrite v_up_tagupdate_iff.
     rewrite <- (combine_default relate_default).
     eapply Abs_T; try eassumption.
   + inversion H15.
     inversion H17; subst.
     inversion H11; subst.
     pose proof search_popro _ _ _ H22.
     pose proof search_popro _ _ _ H23.
     erewrite <- tag_update_twice.
     remember (tag_update t (v_update k v (combine a1 b))) as a.
     rewrite tag_update_default.
     rewrite combine_comm.
     rewrite combine_default.
     erewrite v_update_comm; [| left; tr].
     rewrite combine_comm.
     subst.
     erewrite <- (v_update_combine k1)by (first [ res_simpl | res_intros | res_intro]).
     remember (tag_update t (v_update k v (combine a1 b))) as a.
     rewrite v_up_tagupdate_iff.
     rewrite combine_comm.
     eapply Abs_T; try eassumption.
     rewrite <- (combine_default a).
     rewrite combine_comm.
     eapply Abs_T; try eassumption.
     subst.
     eapply Abs_T; try eassumption.
   + inversion H17; subst.
     inversion H15; subst.
     inversion H10; subst.
     pose proof search_popro _ _ _ H22.
     pose proof search_popro _ _ _ H23.
     erewrite <- tag_update_twice.
     remember (tag_update t (v_update k v (combine a0 b))) as a.
     rewrite tag_update_default.
     rewrite (combine_comm _ b0).
     rewrite combine_default.
     subst.
     erewrite (v_update_combine k0) by (first [ res_simpl | res_intros | res_intro]).
     remember (tag_update t (v_update k v (combine a0 b))) as a.
     erewrite v_update_comm; [| left; tr].
     rewrite combine_comm.
     subst.
     erewrite <- (v_update_combine k1) by (first [ res_simpl | res_intros | res_intro]).
     remember (tag_update t (v_update k v (combine a0 b))) as a.
     rewrite v_up_tagupdate_iff.
     rewrite combine_comm.
     eapply Abs_T; try eassumption.
     rewrite <- (combine_default a).
     eapply Abs_T; try eassumption.
     subst.
     eapply Abs_T; try eassumption.
   + inversion H15; inversion H17; subst.
     inversion H10; inversion H11; subst.
     pose proof search_popro _ _ _ H22.
     pose proof search_popro _ _ _ H23.
     pose proof search_popro _ _ _ H34.
     pose proof search_popro _ _ _ H35.
     erewrite <- tag_update_twice.
     erewrite <- tag_update_twice.
     remember ((tag_update t (v_update k v (combine a1 b)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a2 b1))) as rmap.
     rewrite tag_update_default.
     subst.
     erewrite (v_update_combine k0) by (first [ res_simpl | res_intros | res_intro]).
     remember ((tag_update t (v_update k v (combine a1 b)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a2 b1))) as rmap.
     erewrite v_update_comm; [| left; tr].
     rewrite (combine_comm _ b0).
     subst.
     erewrite combine_asso by (first [ res_simpl | res_intros | res_intro]).
     remember ((tag_update t (v_update k v (combine a1 b)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a2 b1))) as rmap.
     rewrite <- tagupdate_combine.
     subst.
     erewrite <- (v_update_combine k1) by (first [ res_simpl | res_intros | res_intro]).
     remember ((tag_update t (v_update k v (combine a1 b)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a2 b1))) as rmap.
     rewrite v_up_tagupdate_iff.
     rewrite combine_comm .
     eapply Abs_T; try eassumption.
     eapply Abs_T; try eassumption.
     subst. eapply Abs_T; try eassumption.
     subst. eapply Abs_T; try eassumption.
Qed.
Theorem equiv_left_rotate : forall c0 k0 v0 t0 s c1 r1 k1 v1 t1 r2 lo hi ,
 SearchTree' lo
  (T c0 s k0 v0 t0 (T c1 r1 k1 v1 t1 r2)) hi ->
    (T c0 s k0 v0 t0 (T c1 r1 k1 v1 t1 r2))  ~~
    (T c1 (T c0 s k0 v0 default (tag_tree_t t1 r1) ) k1 (f v1 t1) t0 (tag_tree_t t1 r2)).
Proof.
  intros.
  inversion H; subst.
  inversion H9; subst.
  pose proof search_popro _ _ _ H8.
  pose proof search_popro _ _ _ H10.
  pose proof search_popro _ _ _ H11.
  split.
  - intro.
    inversion H3;subst. inversion H16; subst.
    erewrite <- (v_up_tagupdate_iff k1).
    erewrite tagupdate_combine.
    erewrite v_update_combine by (first [ res_simpl | res_intros | res_intro]).
    rewrite (combine_comm (tag_update t1 a0)).
    erewrite combine_asso by (first [ res_simpl | res_intros | res_intro]).
    erewrite v_update_comm; [| left; tr].
    erewrite <- v_update_combine by (first [ res_simpl | res_intros | res_intro]).
    rewrite (combine_comm).
    eapply Abs_T; try eassumption.
    erewrite <- tag_update_default.
    eapply Abs_T; try eassumption.
    eapply tag_tree_abs; try eassumption.
    eapply tag_tree_abs; try eassumption.
 - intro.
   inversion H3; subst. inversion H15; subst.
   destruct r1, r2.
   + inversion H16;subst. inversion H18; subst.
     rewrite combine_default.
     rewrite tag_update_default.
     erewrite v_update_comm; [| right; tr].
     erewrite <- v_update_combine by (first [ res_simpl | res_intros | res_intro]).
     eapply Abs_T; try eassumption.
     rewrite <- (tag_update_defaultmap t1).
     rewrite v_up_tagupdate_iff.
     rewrite <- (combine_default relate_default).
     eapply Abs_T; try eassumption.
   + inversion H16; inversion H18; subst.
     inversion H11; subst.
     pose proof search_popro _ _ _ H22.
     pose proof search_popro _ _ _ H23.
     erewrite <- tag_update_twice.
     remember (tag_update t (v_update k v (combine a b1))) as b.
     rewrite tag_update_default.
     rewrite combine_default.
     rewrite combine_comm.
     subst.
     erewrite  (v_update_combine k0)by (first [ res_simpl | res_intros | res_intro]).
     remember (tag_update t (v_update k v (combine a b1))) as b.
     erewrite v_update_comm; [| right; tr].
     rewrite combine_comm.
     subst.
     erewrite  <- (v_update_combine k1)by (first [ res_simpl | res_intros | res_intro]).
     rewrite v_up_tagupdate_iff.
     eapply Abs_T; try eassumption.
     rewrite <- (combine_default (tag_update t (v_update k v (combine a b1)))).
     rewrite combine_comm.
     eapply Abs_T; try eassumption.
     eapply Abs_T; try eassumption.
   + inversion H16; subst.
     inversion H18; subst.
     inversion H10; subst.
     pose proof search_popro _ _ _ H22.
     pose proof search_popro _ _ _ H23.
     erewrite <- tag_update_twice.
     remember (tag_update t (v_update k v (combine a b))) as b0.
     rewrite tag_update_default.
     rewrite (combine_comm a0).
     rewrite combine_default.
     erewrite v_update_comm; [| right; tr].
     rewrite combine_comm.
     subst.
     erewrite <- (v_update_combine k1) by (first [ res_simpl | res_intros | res_intro]).
     remember (tag_update t (v_update k v (combine a b))) as b0.
     rewrite v_up_tagupdate_iff.
     eapply Abs_T; try eassumption.
     rewrite <- (combine_default b0).
     eapply Abs_T; try eassumption.
     subst.
     eapply Abs_T; try eassumption.
   + inversion H16; inversion H18; subst.
     inversion H10; inversion H11; subst.
     pose proof search_popro _ _ _ H22.
     pose proof search_popro _ _ _ H23.
     pose proof search_popro _ _ _ H34.
     pose proof search_popro _ _ _ H35.
     erewrite <- tag_update_twice.
     erewrite <- tag_update_twice.
     remember ((tag_update t (v_update k v (combine a1 b2)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a b1))) as rmap.
     rewrite tag_update_default.
     rewrite combine_comm.
     subst.
     erewrite (v_update_combine k0) by (first [ res_simpl | res_intros | res_intro]).
     remember ((tag_update t (v_update k v (combine a1 b2)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a b1))) as rmap.
     erewrite v_update_comm; [| right; tr].
     subst.
     erewrite combine_asso by (first [ res_simpl | res_intros | res_intro]).
     remember ((tag_update t (v_update k v (combine a1 b2)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a b1))) as rmap.
     rewrite <- tagupdate_combine.
     subst.
     erewrite <- (v_update_combine k1) by (first [ res_simpl | res_intros | res_intro]).
     remember ((tag_update t (v_update k v (combine a1 b2)))) as lmap.
     remember (tag_update t2 (v_update k2 v2 (combine a b1))) as rmap.
     rewrite v_up_tagupdate_iff.
     eapply Abs_T; try eassumption.
     rewrite combine_comm.
     eapply Abs_T; try eassumption.
     subst. eapply Abs_T; try eassumption.
     subst. eapply Abs_T; try eassumption.
Qed.
(*下面是不考虑tag的rotate*)
Theorem ri_ro_abs : forall co a k v  co' b k1 v1 c co1 co2 lo hi  cts,
 SearchTree' lo (T co (T co' b k1 v1 default c) k v default a) hi  ->
  Abs (T co (T co' b k1 v1 default c) k v default a) cts ->
   Abs (ri_rotate_notag co1 (T co2 b k1 v1 default c) k v default a) cts.
Proof.
  intros.
  simpl.
  inversion H0. subst. inversion H8. subst.
  inversion H. subst. inversion H13. subst.
  pose proof search_popro _ _ _ H13.
  pose proof search_popro _ _ _ H14.
  pose proof search_popro _ _ _ H15.
  pose proof search_popro _ _ _ H16.
  rewrite tag_update_default. rewrite tag_update_default.
  rewrite combine_comm.
  erewrite  (v_update_combine k1 v1 )by (first [ res_simpl | res_intros | res_intro]).
  erewrite v_update_comm ; [ | right; auto].
  erewrite combine_asso by (first [ res_simpl | res_intros | res_intro]).
  rewrite (combine_comm b0 b1).
  erewrite  <- (v_update_combine k v )by (first [ res_simpl | res_intros | res_intro]).
  rewrite <- tag_update_default.
  eapply Abs_T.
  auto.
  rewrite <- tag_update_default.
  apply Abs_T.
  auto. auto.
Qed.
Theorem le_ro_abs : forall co a k v  co' b k1 v1 c co1 co2 lo hi  cts,
 SearchTree' lo (T co a k v default (T co' b k1 v1 default c)) hi  ->
  Abs (T co a k v default (T co' b k1 v1 default c)) cts ->
   Abs (le_rotate_notag co1 a k v default (T co2 b k1 v1 default c)) cts.
Proof.
  intros.
  simpl.
  inversion H0. subst. inversion H9. subst.
  inversion H. subst. inversion H14. subst.
  pose proof search_popro _ _ _ H13.
  pose proof search_popro _ _ _ H14.
  pose proof search_popro _ _ _ H15.
  pose proof search_popro _ _ _ H16.
  rewrite tag_update_default. rewrite tag_update_default.
  erewrite  (v_update_combine k1 v1 )by (first [ res_simpl | res_intros | res_intro]).
  rewrite (combine_comm a1 b1).
  erewrite combine_asso by (first [ res_simpl | res_intros | res_intro]).
  erewrite v_update_comm; [ | tauto].
  erewrite  <- (v_update_combine k v )by (first [ res_simpl | res_intros | res_intro]).
  erewrite combine_comm.
  rewrite <- tag_update_default.
  eapply Abs_T.
  2: auto.
  rewrite <- tag_update_default.
  apply Abs_T.
  auto. auto.
Qed.

Theorem ro_equiv : forall co a k v  co' b k1 v1 c co1 co2 lo hi ,
 SearchTree' lo (T co a k v default (T co' b k1 v1 default c)) hi  -> 
  SearchTree' lo (le_rotate_notag co1 a k v default (T co2 b k1 v1 default c)) hi ->
   (T co a k v default (T co' b k1 v1 default c))  ~~ 
    (le_rotate_notag co1 a k v default (T co2 b k1 v1 default c)) .
Proof.
  intros.
  split.
  - eapply le_ro_abs ;try eassumption.
  - unfold le_rotate_notag. eapply ri_ro_abs; try eassumption.
Qed.

Theorem ri_le_ro_abs : forall co r k0 v0 s co' s1 k1 v1  co1 co2 lo hi  cts,
 SearchTree' lo (T co (T co' r k0 v0 default s) k1 v1 default s1) hi ->
  default_tag_tree s ->
  Abs (T co (T co' r k0 v0 default s) k1 v1 default s1) cts ->
   Abs
  (ri_rotate_notag co1 (le_rotate_notag co2 r k0 v0 default (makeBlack s)) k1 v1
     default s1) cts.
Proof.
  intros.
  inversion H. subst. inversion H10. subst.
  destruct s.
  - exfalso. apply H0.
  - unfold makeBlack.
    simpl in H0.  subst.
    inversion H13. subst.
    remember ( (le_rotate_notag co2 r k0 v0 default (T Black s2 k v default s3))) as tree.
    rewrite Heqtree.
    unfold le_rotate_notag .
    eapply (ri_ro_abs Red _ _ _  Black).
    eapply ST_T.   eapply ST_T. eapply ST_T. apply H12.  auto. apply H14. apply H11.
    inversion H1. subst.
    eapply Abs_T.
    2: auto.
    eapply le_ro_abs. 2: apply H8.
    eapply ST_T;try eassumption.
Qed.


(*complete relate*)
Lemma complete_relate_strong :
 forall h lo hi tree tmap hmap tag,
  SearchTree_half lo h hi -> SearchTree' lo tree hi ->
   Abs tree tmap -> Abs_half h hmap  -> tag = accumulate_tag_for_ht h ->
    Abs (complete_tree h tree) (combine (tag_update tag tmap) hmap).
Proof.
  intro.
  induction h.
  - intros. simpl.
    simpl in H3; subst.
    rewrite tag_update_default.
    inversion H2; subst.
    rewrite combine_default. auto.
  - intros.
    destruct a. repeat destruct p.
    simpl in H3.
    inversion H.
    + subst.
      simpl. 
      inversion H2; subst.
      assert (SearchTree' lo0 (T c r k v t tree) hi).
      { eapply ST_T; try eassumption.
        eapply search_popro3_lte;try eassumption. }
      assert (Abs (T c r k v t tree) (tag_update t (v_update k v (combine tmap0 tmap)))).
      { eapply Abs_T; try eassumption. }
      remember (accumulate_tag_for_ht h).
      assert (combine (tag_update (Optt t0 t) tmap)
     (combine lmap (tag_update (Optt t0 t) (v_update k v tmap0))) =
              combine (tag_update t0 (tag_update t(v_update k v (combine tmap0 tmap)))) lmap).
     {
       pose proof search_popro _ _ _ H15.
       pose proof search_popro _ _ _ H0.
       erewrite (combine_asso (tag_update (Optt t0 t) tmap))
         by (first [ res_simpl | res_intros | res_intro ]).
       erewrite (combine_comm lmap).
       rewrite <- tagupdate_combine.
       rewrite tag_update_twice.
       erewrite v_update_combine by (first [ res_simpl | res_intros | res_intro] ).
       rewrite (combine_comm tmap tmap0).
       auto.
      }
     rewrite H5; clear H15.
     eapply IHh; try eassumption. auto.
   +  subst.
      simpl.
      inversion H2; subst.
      assert (SearchTree' lo (T c tree k v t r) hi0).
      { eapply ST_T; try eassumption.
        eapply search_popro2_lte;try eassumption. }
      assert (Abs (T c tree k v t r) (tag_update t(v_update k v (combine tmap tmap0)))).
      { eapply Abs_T; try eassumption. }
      remember (accumulate_tag_for_ht h).
      assert (combine (tag_update (Optt t0 t) tmap)
     (combine lmap (tag_update (Optt t0 t) (v_update k v tmap0))) =
              combine (tag_update t0 (tag_update t(v_update k v (combine tmap tmap0)))) lmap).
     {
       pose proof search_popro _ _ _ H15.
       pose proof search_popro _ _ _ H0.
       erewrite (combine_asso (tag_update (Optt t0 t) tmap))
         by (first [ res_simpl | res_intros | res_intro ]).
       erewrite (combine_comm lmap).
       rewrite <- tagupdate_combine.
       rewrite tag_update_twice.
       erewrite v_update_combine by (first [ res_simpl | res_intros | res_intro] ).
       auto.
      }
     rewrite H5; clear H15.
     eapply IHh; try eassumption. auto.
Qed.
Lemma complete_relate_pre:
 forall h lo hi tree  tmap hmap, Forall P h ->
  SearchTree_half lo h hi -> SearchTree' lo tree hi -> Abs tree tmap -> Abs_half h hmap  ->
    Abs (complete_tree h tree) (combine tmap hmap).
Proof.
  intros.
  revert tree tmap hmap H1 H2 H3.
  assert (default = accumulate_tag_for_ht h).
  { eapply accumulate_default; try eassumption. }
  intros.
  rewrite <- (tag_update_default tmap).
  eapply complete_relate_strong; try eassumption.
Qed.

End Section_Abstract_2.
