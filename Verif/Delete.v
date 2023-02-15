From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import omega.Omega.

Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.
Require Import RBT.Verif.Abstract.
Require Import RBT.Verif.general_split.
Require Import RBT.Verif.Insert.

Section Section_Delete.

Context {rbt:RBtree_setting}.

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
 
 Ltac stt n :=
    first [assumption | apply ST_E |
      match n with
      | S ?m =>
          match goal with
          | |- _ <=  _ => TR 5;stt m
          | |- _ < _ => TR 5;stt m
          | H: SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Red Black);stt m
          | H: SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Black Red);stt m
          | H: SearchTree' ?k ?a ?hi |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro3_lte lo a hi k);stt m
          | H: SearchTree' ?lo ?a ?k |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro2_lte lo a hi k);stt m
          | H: SearchTree' ?lo ?a ?hi |- SearchTree' ?k0 ?a ?k1
                         =>  eapply (search_popro3_lte k0 a k1 lo);stt m
          | |- SearchTree' _ (T _ _ _ _ _ _ ) _ => eapply ST_T;stt m
          end
      end].
 
 Ltac rbco n :=
    first [assumption | apply (IsRB_co_leaf Red) | apply (IsRB_co_leaf Black)|
      match n with
      | S ?m =>
          match goal with
          | H: is_redblack_color ?a Red |- is_redblack_color ?a Black => eapply isr_isb;rbco m
          | H: is_redblack_color ?a Black,
            H0: Black_tree ?a |- is_redblack_color ?a Red => eapply (isb_isr_black _ H0);rbco m
          | |- is_redblack_color (tag_tree_t _ ?a) _ => eapply isrb_tagupdate;rbco m
          | H: is_redblack_color (T _ ?a _ _ _ _ ) _ |- is_redblack_color ?a _ => inversion H;subst;rbco m
          | H: is_redblack_color (T _ _ _ _ _ ?a ) _ |- is_redblack_color ?a _ => inversion H;subst;rbco m
          | |- is_redblack_color (T Red _ _ _ _ _ ) Black => apply IsRB_co_r;rbco m 
          | |- is_redblack_color (T Black _ _ _ _ _ ) _ => apply IsRB_co_b;rbco m
          end
      end].
Ltac rbdep n :=
    first [assumption | apply IsRB_dep_em |
      match n with
      | S ?m =>
          match goal with
          | H: is_redblack_dep (T ?c ?l _ _ _ ?r) ?n 
                |- is_redblack_dep (T ?c ?l _ _ _ ?r) ?n  
                     => eapply isrb_changekvt_dep;try eassumption
          | |- is_redblack_dep (tag_tree_t _ ?a) ?n
                    => eapply isrb_tagupdate_dep;rbdep m
          | H: is_redblack_dep (T Red ?l _ _ _ ?r) ?n
                |- is_redblack_dep (T Black ?l _ _ _ ?r) (S ?n)  
                     => eapply isrb_dep_RtoB;rbdep m
          | |- is_redblack_dep (T Red _ _ _ _ _ ) _ => eapply IsRB_dep_r;rbdep m
          | |- is_redblack_dep (T Black _ _ _ _ _ ) _ => eapply IsRB_dep_b;rbdep m
          end
      end].
   Ltac TR n :=
    first [assumption | apply lte_refl |
      match n with
      | S ?m =>
          match goal with
          | H: lt_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ (lt_lte _ _ H)); TR m
          | H: lte_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ H); TR m
          | H: lte_prop ?a _ |- lt_prop ?a _ => apply (lte_lt_trans _ _ _ H); TR m
          | H: lt_prop ?a _ |- lt_prop ?a _ => apply (lt_lte_trans _ _ _ H); TR m
          | H: lte_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TR m
          | H: lte_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TR m
          | H: lt_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (ltb_lt _ _ ) in H;TR m
          | H: lt_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (ltb_lt  _ _) in H;TR m
          | H: lte_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TR m
          | H: lte_bool _ ?a = false |- lt_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TR m
          | H: lt_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TR m
          | H: lt_bool _ ?a = false |- lt_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TR m
          | H: lt_prop ?a _ |- lt_bool ?a _ = true => rewrite (ltb_lt  _ _ ) in H;TR m
          end
      end].

Ltac solve_order :=
match goal with
| H: lt_prop ?a _ |- _ =>
    let CONTR := fresh "H" in
    assert (a < a) as CONTR by (TR 6);
    exfalso; exact (lt_refl _ CONTR)
| H: lte_prop ?a _ |- _ =>
    let CONTR := fresh "H" in
    assert (a < a) as CONTR by (TR 6);
    exfalso; exact (lt_refl _ CONTR)
| H: lt_bool ?a _ =true |- _  =>
    let CONTR := fresh "H" in
    assert (a < a) as CONTR by (TR 6);
    exfalso; exact (lt_refl _ CONTR)
end.
Ltac tr := TR 2.

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
   Ltac TRM n :=
    first [assumption | apply lte_refl |
      match n with
      | S ?m =>
          match goal with
          | |- _ /\ _ => split;TRM m
          | H: lt_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ (lt_lte _ _ H)); TRM m
          | H: lte_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ H); TRM m
          | H: lte_prop ?a _ |- lt_prop ?a _ => apply (lte_lt_trans _ _ _ H); TRM m
          | H: lt_prop ?a _ |- lt_prop ?a _ => apply (lt_lte_trans _ _ _ H); TRM m
          | H: lte_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TRM m
          | H: lte_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TRM m
          | H: lt_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (ltb_lt  _ _ ) in H;TRM m
          | H: lt_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (ltb_lt  _ _) in H;TRM m
          | H: lte_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TRM m
          | H: lte_bool _ ?a = false |- lt_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TRM m
          | H: lt_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TRM m
          | H: lt_bool _ ?a = false |- lt_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TRM m
          | H: lt_prop ?a _ |- lt_bool ?a _ = true => rewrite (ltb_lt  _ _ ) in H;TRM m
          | H: SearchTree' ?a ?t ?hi |-  ?a < _  => apply (search_popro a t hi ) in H;TRM m
          | H: SearchTree' ?a ?t ?hi |-  ?a <= _  => apply (search_popro a t hi ) in H;TRM m
          | |- min_k ?a ?b <= ?a => apply min_left
          | |- ?a <= max_k ?a ?b => apply max_left
          | |- min_k ?a ?b <= ?b => apply min_right
          | |- ?b <= max_k ?a ?b => apply max_right
          | |- ?x <= max_k ?y (max_k ?z ?x) => erewrite <- max_asso;TRM m
          | |- max_k ?x ?y < ?z => erewrite <- max_lt; TRM m
          | |- max_k ?x ?y <= ?z => erewrite <- max_lt_e; TRM m
          | |- ?z <  min_k ?x ?y  => erewrite <- min_lt; TRM m
          | |- ?z <=  min_k ?x ?y  => erewrite <- min_lt_e; TRM m
          end
      end].
Ltac stt2 n :=
    first [assumption |
      match n with
      | S ?m =>
          match goal with
          | |- _ <=  _ => TRM 5;stt2 m
          | |- _ < _ => TRM 5;stt2 m
          | H: SearchTree' ?lo ?t ?hi, 
            H1: SearchTree' ?low ?t ?hi
             |- SearchTree' (max_k ?lo ?low) ?t ?hi 
              => eapply search_left_max;stt2 m
          | H: SearchTree' ?lo ?t ?hi, 
            H1: SearchTree' ?lo ?t ?high
             |- SearchTree' ?lo ?t (min_k ?hi ?high)
              => eapply search_right_min;stt2 m
          | H: SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) ?hi, 
            H1: SearchTree' ?low (T _ ?l ?k ?v ?t ?r) ?hi
             |- SearchTree' (max_k ?lo ?low) (T _ ?l ?k ?v ?t ?r) ?hi 
              => eapply search_left_max;stt2 m
          | H: SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) ?hi, 
            H1: SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) ?high
             |- SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) (min_k ?hi ?high)
              => eapply search_right_min;stt2 m
          | H: SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Red Black);stt2 m
          | H: SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Black Red);stt2 m
          | H: SearchTree' ?k ?a ?hi |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro3_lte lo a hi k);stt2 m
          | H: SearchTree' ?lo ?a ?k |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro2_lte lo a hi k);stt2 m
          | H: SearchTree' ?lo ?a ?hi |- SearchTree' ?k0 ?a ?k1
                         =>  eapply (search_popro3_lte k0 a k1 lo);stt2 m
          | |- SearchTree' _ (T _ _ _ _ _ _ ) _ => eapply ST_T;stt2 m
          end
      end | apply ST_E ].


Definition delete_split (x: Key) (t : Tag) (s: RBtree) (b : list Half_tree) : list Half_tree * RBtree := insert_split x t s b.
Definition minimum_split (t : Tag) (s: RBtree) (b: list Half_tree):  list Half_tree
:= fst (general_split (fun k => true) (fun k =>  false) t s b).
(*fst作用为取出二元组中的第一个元素*)
Definition Up_split (b: list Half_tree) : list Half_tree * RBtree :=
match b with
| nil => (nil , Empty)
|(false, co, k, v, t, r)::l => (l , T co Empty k v t r)
|(true, co, k, v, t, r)::l => (l , T co r k v t Empty)
end.
(*upsplit的作用是取出右子树最小元素*)
Definition delete_root (s: RBtree) (h : list Half_tree): list Half_tree * RBtree * color :=
match s with
|Empty => (h, Empty, Red)
|T co Empty k v t Empty => (h, Empty, co)
|T co Empty k v t (T rco rl rk rv rt rr) => (h, T rco rl rk rv (Optt t rt) rr, co)
|T co (T lco ll lk lv lt lr) k v t Empty => (h, T lco ll lk lv (Optt t lt) lr, co)
|T co l k v t r => match Up_split (minimum_split default r nil) with
                  |(restr, T yco Empty yk yv yt x) =>
                              ( restr ++ ((true, co, yk, yv, t, l)::h),
                                          x, yco)
                  |(_ , _) => (h, Empty, Red)
                  end
end.
(*Balance Definition*)
  Definition CaseFour_sol (s :RBtree) (H : Half_tree) : RBtree :=
  match H with
  |(pb, pc, p, pv, pt, brother) =>
     match pb with
     |false => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |_  ,(T Red wrl wrk wrv wrt wrr) =>
                   (T pc (T Black s p pv default (tag_tree_t wt wl)) wk (f wv wt) pt (tag_tree_t wt (makeBlack wr)))
                |_ , _ => complete_tree_one s H
                end
             | _ => complete_tree_one s H
             end
     |true => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |(T Red wll wlk wlv wlt wlr),_  =>
                   (T pc (tag_tree_t wt (makeBlack wl)) wk (f wv wt) pt (T Black (tag_tree_t wt wr) p pv default s))
                |_ , _ => complete_tree_one s H
                end
             | _ => complete_tree_one s H
             end
     end
  end.

  Definition CaseThree_sol (s :RBtree) (H : Half_tree) : RBtree :=
  match H with
  |(pb, pc, p, pv, pt, brother) =>
     match pb with
     |false => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |(T Red wll wlk wlv wlt wlr), _ =>
       CaseFour_sol s
     (false, pc, p, pv, pt, (T Black (tag_tree_t wlt wll) wlk (f wlv wlt) wt 
                                     (T Red (tag_tree_t wlt wlr) wk wv default wr)))
                |_ , _ => complete_tree_one s H
                end
             | _ => complete_tree_one s H
             end
     |true => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |_ ,(T Red wrl wrk wrv wrt wrr) =>
       CaseFour_sol s (true, pc, p, pv, pt, 
        (T Black (T Red wl wk wv default (tag_tree_t wrt wrl)) wrk (f wrv wrt) wt 
                                     (tag_tree_t wrt wrr)))
                |_ , _ => complete_tree_one s H
                end
             | _ => complete_tree_one s H
             end
     end
  end.

  Definition CaseTwo_sol (s:RBtree) (H:Half_tree) :RBtree :=
  match H with
  |(pb, pc, p, pv, pt, brother) =>
     match pb with
     |false => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=>
            (T pc s p pv pt (T Red wl wk wv wt wr))
                |Empty , Empty => (T pc s p pv pt (T Red Empty wk wv wt Empty))
                |_ ,_ => complete_tree_one s H
                end
             | _ => complete_tree_one s H
             end
     |true => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=>
            (T pc (T Red wl wk wv wt wr) p pv pt s)
                |Empty, Empty => (T pc (T Red Empty wk wv wt Empty) p pv pt s)
                |_ , _ => complete_tree_one s H
                end
             | _ => complete_tree_one s H
             end
     end
  end.

  Definition CaseTTF_sol (s:RBtree) (H:Half_tree)(n :bool) : RBtree * bool:=
  match n with
  |true => (complete_tree_one s H, true)
  |false =>
  match H with 
  |(pb, pc, p, pv, pt, brother) =>
     match pb with
     |false => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> (CaseTwo_sol s H, false)
                |Empty, Empty => (CaseTwo_sol s H, false)
                |_  ,(T Red _ wrk wrv wrt _ ) => (CaseFour_sol s H, true)
                |(T Red _ _ _ _ _ ), _ => (CaseThree_sol s H, true)
                |_, _ => (complete_tree_one s H, true) 
                         (*empty black,  black empty 不存在*)
                end
             | _ =>(complete_tree_one s H, true)
             end
     |true => match brother with
             |T Black wl wk wv wt wr => 
                match wl, wr with
                |(T Black _ _ _ _ _ ), (T Black _ _ _ _ _ )=> (CaseTwo_sol s H, false)
                |Empty, Empty => (CaseTwo_sol s H, false)
                |(T Red _ _ _ _ _ ) ,_ => (CaseFour_sol s H, true)
                |_, (T Red _ _ _ _ _ ) => (CaseThree_sol s H,true)
                |_, _ => (complete_tree_one s H, true)
                        (*empty black,  black empty 不存在*)
                end
             | _ =>(complete_tree_one s H, true)
             end
     end
  end
  end.

  Definition CaseOne_sol (s:RBtree) (H:Half_tree) (n : bool) : RBtree * bool:=
  match n with
  |true => (complete_tree_one s H, true)
  |false =>
  match H with
  |(pb, pc, p, pv, pt, brother) =>
     match pb with
     |false => match brother with
             |T Red wl wk wv wt wr =>
              (*将w变黑，p变红，以p左旋
                new s: s
                new H: list (false,Red,p,pv,default,tag_tree_t wt wl),
                            (false,Black,wk,f wv wt, pt, tag_tree_t wt wr) *)
                match (CaseTTF_sol s (false,Red,p,pv,default,tag_tree_t wt wl) false) with
                |(s', true) => (complete_tree_one s' (false,Black,wk,f wv wt, pt, tag_tree_t wt wr), true)
                |(s', false) => match s' with
                               |T Red _ _ _ _ _ =>
                                 (complete_tree_one (makeBlack s') (false,Black,wk,f wv wt, pt, tag_tree_t wt wr), true)
                               | _ => CaseTTF_sol s' (false,Black,wk,f wv wt, pt, tag_tree_t wt wr) false
                               end
                end
             | _ => (complete_tree_one s H, true)
             end
     |true => match brother with
             |T Red wl wk wv wt wr =>
              (*将w变黑，p变红，以p左旋
                new s: s
                new H: list (true,Red,p,pv,default,tag_tree_t wt wr),
                            (true,Black,wk,f wv wt, pt, tag_tree_t wt wl) *)
                match (CaseTTF_sol s (true,Red,p,pv,default,tag_tree_t wt wr) false) with
                |(s', true) => (complete_tree_one s' (true,Black,wk,f wv wt, pt, tag_tree_t wt wl), true)
                |(s', false) => match s' with
                               |T Red _ _ _ _ _ => 
                                 (complete_tree_one (makeBlack s') (true,Black,wk,f wv wt, pt, tag_tree_t wt wl), true )
                               |_ =>  CaseTTF_sol s' (true,Black,wk,f wv wt, pt, tag_tree_t wt wl) false
                               end
                end
             | _ => (complete_tree_one s H, true)
             end
     end
  end
  end.


Fixpoint delete_balance (s: RBtree) (h: list Half_tree) (ori_color: color) :
  RBtree * list Half_tree  :=
match ori_color with
(* remove 点为红色 不影响结构*)
|Red => (s,h)
|Black => match h with
         |nil => (s, h)(* 即x为根节点*)
         |(pb, pc, p, pv, pt, brother) :: l' =>
           match s with (* s 根结点有一个extra black*)
           |T Red sl sk sv st sr => (T Black sl sk sv st sr, h)
           |_  => (*双黑*)
              match brother with
              |Empty => (s,h) (*不可能为空*)
              |T Red wl wk wv wt wr => 
                match (CaseOne_sol s (pb, pc, p, pv, pt, brother) false) with
                |(s', true) => (s', l')
                |(s', false) => delete_balance s' l' Black
                end
              |T Black wl wk wv wt wr => 
                match (CaseTTF_sol s (pb, pc, p, pv, pt, brother) false) with
                |(s', true) => (s', l')
                |(s', false) => delete_balance s' l' Black
                end
              end
           end
        end
end.
Definition delete_with_no_balance (x : Key) (s: RBtree): list Half_tree * RBtree * color   := 
    let ( half , base ) := delete_split x default s nil in
         delete_root base half.
Definition delete_into_base_half (x: Key) (s: RBtree) : RBtree * list Half_tree :=
    let '(half, base, co) := delete_with_no_balance x s in
        delete_balance base half co.
Definition delete (x: Key) (s: RBtree) : RBtree :=
    let (base, half) := delete_into_base_half x s in
      makeBlack (complete_tree half base).

(*Lemmas*)
  Lemma delete_split_st :
   forall tree  k l s,
   SearchTree tree -> 
      (l, s) = delete_split k default tree nil ->
        ( exists x  y,  SearchTree_half x l y /\ SearchTree' x s y /\ (k <? y = true /\ x <? k = true) ).
  Proof.
    intros.
    inversion H. subst.
    
    pose proof (Archmedes_l (min_k lo k) ).
    pose proof (Archmedes_R (max_k hi k) ).
    destruct H2. destruct H3.
    assert ( (k <? x0) = true /\ (x <? k) = true ).
    { split. 
    pose proof max_right hi k.
    eapply ltb_lt. tr.
    pose proof min_right lo k.
    eapply ltb_lt. tr. }
    assert ( SearchTree' x tree x0).
    { eapply search_popro2_lte.  eapply search_popro3_lte; try eassumption.
      pose proof min_left lo k. tr.
      pose proof max_left hi k. tr. }
    assert (SearchTree_half x nil x0). 
   { apply ST_nil. eapply search_popro; try eassumption. }
   
   eapply insert_st_pre; try eassumption.
  Qed.
  Lemma delete_relate_split :
   forall tree cts k l r ,
    SearchTree tree -> Abs tree cts -> 
       (l, r) = delete_split k default tree nil -> Abs (complete_tree l r) cts.
  Proof.
    intros.
   inversion H.
   subst.
   assert (Forall P nil).
   { apply Forall_nil. }
   assert (SearchTree_half lo nil hi).
   { apply ST_nil. eapply search_popro; try eassumption. }
   pose proof Abs_nil.
   unfold delete_split in H2.
   pose proof insert_relate_pre _ _ _ _ _ _ _ _ _ _ H2 H0 H3 H4 H5 H1.
   rewrite tag_update_default in H6.
   rewrite combine_default in H6.
   auto.
  Qed.
  Lemma delete_split_tag_default:
    forall tree k l r,
   SearchTree tree ->
     (l, r) = delete_split k default tree nil ->
       Forall P l.
  Proof.
    intros.
    inversion H. subst. clear H.
    assert (Forall P nil).
   { apply Forall_nil. }
   assert (SearchTree_half lo nil hi).
   { apply ST_nil. eapply search_popro; try eassumption. }
   eapply insert_split_tag_default ; try eassumption.
  Qed.
  Lemma delete_in:
   forall k t tag cts h l c0 r1 k1 v0 t1 r2,
    SearchTree t -> Abs t cts -> (l, T c0 r1 k1 v0 t1 r2) =
         delete_split k tag t h -> k = k1.
  Proof.
    intros.
    inversion H. subst. clear H.
    revert k tag cts h l c0 r1 k1 v0 t1 r2 H0 H1.
    unfold delete_split. unfold insert_split.
    induction H2.
    - intros. inversion H1.
    - intros.
      simpl in H1.
      inversion H0. subst.
      remember (k0 <? k ) as m.
      remember (k <? k0 ) as n.
      destruct m.
      + clear IHSearchTree'2.
        eapply IHSearchTree'1 ; try eassumption.
      + destruct n.
        * clear IHSearchTree'1.
        eapply IHSearchTree'2; try eassumption.
        * assert ( k = k0 ).
      {   apply (lt_eq k k0). split. apply ltb_false. auto. apply ltb_false. auto. }
         inversion H1. subst. reflexivity.
  Qed.
  Lemma delete_not_in:
   forall k t tag cts h l b,
    SearchTree t -> Abs t cts -> (l, b) = delete_split k tag t h -> b = Empty -> 
       cts k = None.
  Proof.
    intros. inversion H. subst.
    revert k tag cts h l H0 H1 .
    unfold delete_split. unfold insert_split.
    induction H3.
    - intros.
      inversion H1.
      reflexivity.
    - intros.
      simpl in H1.
      inversion H0. subst.
      remember (k0 <? k ) as m.
      remember (k <? k0 ) as n.
      destruct m.
      + clear IHSearchTree'2.
        assert (SearchTree l).
        {  eapply ST_intro; try eassumption. }
        pose proof (IHSearchTree'1 H2 k0 (Optt tag t) a ((false, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) r) :: h) l0 H9 H1).
        assert (Equal_bool k k0 = false). {  rewrite eqb_comm. apply lt_eqb_false. symmetry in Heqm.
    pose proof ltb_lt k0 k. rewrite <- H4 in Heqm. auto. }
        unfold tag_update.
        unfold v_update.
        rewrite H4.
        unfold combine. rewrite H3.
        assert (b k0 = None).
        { pose proof (search_relate k0 r b k hi H3_0 H10).
          destruct (b k0); [ | reflexivity ].
          assert (Some v0 <> None). { unfold not.  intros.  inversion H6. }
           apply H5 in H6. 
           destruct H6. 
           symmetry in Heqm. apply (ltb_lt k0 k ) in Heqm. 
           apply Total_Asymmetric in Heqm. apply Heqm in H6. 
           inversion H6. }
        rewrite H5; reflexivity.
      + destruct n.
        * clear IHSearchTree'1.
          assert (SearchTree r).
        {  eapply ST_intro; try eassumption. }
         pose proof (IHSearchTree'2 H2 k0 (Optt tag t) b ((true, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) l) :: h) l0 H10 H1).
        assert (Equal_bool k k0 = false). {   apply lt_eqb_false. symmetry in Heqn.
    pose proof ltb_lt  k k0. rewrite <- H4 in Heqn. auto. }
        unfold tag_update.
        unfold v_update.
        rewrite H4.
        unfold combine. rewrite H3.
        assert (a k0 = None).
        { pose proof (search_relate k0 l a lo k H3_ H9).
          destruct (a k0); [ | reflexivity ].
          assert (Some v0 <> None). { unfold not.  intros.  inversion H6. }
           apply H5 in H6. 
           destruct H6. 
           symmetry in Heqn. apply (ltb_lt k k0) in Heqn. 
           apply Total_Asymmetric in Heqn. apply Heqn in H7.
           inversion H7. }
        rewrite H5; reflexivity.
       * inversion H1.
  Qed.
  Lemma delete_split_rb_co :
 forall tree  k l s,
 tree <> Empty ->
 is_redblack_color tree Red ->
    (l, s) = delete_split k default tree nil ->
     ( is_redblack_color s Black /\ is_redblack_color_half l Black ) /\
      (Red_tree s /\ fst_black' l \/ Black_tree s \/ (s = Empty /\ ~ l =nil)).
  Proof.
    intros.
    eapply general_split_RB_co; try eassumption.
    eapply insert_lb_rb.
    eapply isr_isb ; try eassumption.
    apply IsRB_co_nil.
    inversion H0.
    - subst. unfold not in H. contradiction.
    - subst. right. left.
      reflexivity.
  Qed.


  (*minimum split Lemmas*)
  Lemma minimum_split_equi :
   forall lo hi tree t0 h,
    SearchTree' lo tree hi ->
     general_split (fun _ : Key => true) (fun _ : Key => false) t0 tree h =
      general_split (fun x: Key => lo <? x) (fun x : Key => x <=? lo ) t0 tree h.
  Proof.
    intros.
    revert t0 h.
    induction H.
    - intros. simpl. reflexivity.
    - intros. assert (lo <? k = true).
      { apply search_popro in H.
        (* apply lteb_lte. *) tr. }
      simpl.
      rewrite H1.
      pose proof IHSearchTree'1 (Optt t0 t)((false, c, k, f (f v t) t0, default,
     tag_tree_t (Optt t0 t) r) :: h) .
     rewrite H2.
     reflexivity.
  Qed.
  Lemma minimum_split_empty :
   forall  tree t0 h l r,
    (l, r) =  general_split (fun _ : Key => true) (fun _ : Key => false) t0 tree h ->
      r = Empty.
  Proof.
    intro.
    induction tree.
    - intros.
      simpl in H.
      inversion H.
      reflexivity.
    - intros.
      eapply IHtree1; try eassumption.
  Qed.
  Lemma minimum_split_notnil :
   forall  tree t0 h l,
    l = minimum_split  t0 tree h ->
      l <> nil  \/ (tree = Empty /\ h = nil ).
  Proof.
    intros.
    unfold minimum_split in H.
    remember  (general_split (fun _ : Key => true) 
           (fun _ : Key => false) t0 tree h).
    destruct p. simpl in H. subst.
    revert t0 h l0 r Heqp.
    induction tree.
    - intros.
      destruct h.
      right. split. reflexivity. reflexivity.
      left. simpl in Heqp. inversion Heqp. subst.
      unfold not. intros.
      inversion H.
    - intros.
      left.
      simpl in Heqp.
      pose proof IHtree1 _ _ _ _ Heqp.
      destruct H.
      auto.
      destruct H. inversion H0.
  Qed.
  Lemma minimum_split_ST :
   forall lo hi tree h t l,
    SearchTree' lo tree hi -> SearchTree_half lo h hi -> l = minimum_split t tree h ->
     ( exists x  y,  SearchTree_half x l y  /\ SearchTree' x Empty y /\
                        ( (fun x: Key => lo <? x) y = true /\ (fun x : Key => x <=? lo ) x = true) ).
  Proof.
    intros.
    unfold minimum_split in H1.
    remember (general_split
            (fun _ : Key => true)
            (fun _ : Key => false) t tree
            h).
    destruct p.
    simpl in H1.
    pose proof minimum_split_empty _ _ _ _ _ Heqp.
    erewrite minimum_split_equi in Heqp; try eassumption.
    subst.
    eapply general_split_ST; try eassumption.
    apply search_popro in H.
    - intros.
      left.
      remember (lo <? Rb).
      remember (Rb <=? lo).
      destruct b.
      + symmetry in Heqb.
       destruct b0.
       * symmetry in Heqb0. solve_order.
       * reflexivity.
      + symmetry in Heqb.
       destruct b0.
       * reflexivity.
       * symmetry in Heqb0. solve_order.
    - split.
      apply search_popro in H.
      tr.
      apply lteb_lte.
      tr.
  Qed.
  Lemma minimum_split_ST_out :
    forall lo hi tree h t l olo ohi,
    SearchTree' lo tree hi -> SearchTree_half lo h hi ->
     SearchTree_half_out olo h ohi ->
      l = minimum_split t tree h ->
        SearchTree_half_out (min_k lo olo) l (max_k hi ohi).
  Proof.
    intros.
    unfold minimum_split in H2.
    remember (general_split
            (fun _ : Key => true)
            (fun _ : Key => false) t tree
            h).
    destruct p.
    simpl in H2.
    pose proof minimum_split_empty _ _ _ _ _ Heqp.
    erewrite minimum_split_equi in Heqp; try eassumption.
    subst.
    eapply general_split_ST_out; try eassumption.
    apply search_popro in H.
    - intros.
      left.
      remember (lo <? Rb).
      remember (Rb <=? lo).
      destruct b.
      + symmetry in Heqb.
       destruct b0.
       * symmetry in Heqb0. solve_order.
       * reflexivity.
      + symmetry in Heqb.
       destruct b0.
       * reflexivity.
       * symmetry in Heqb0. solve_order.
  Qed.
  Lemma minimum_split_abs :
   forall lo hi tree tmap l,
    SearchTree' lo tree hi -> Abs tree tmap ->
     l = minimum_split default tree nil ->
      Abs (complete_tree l Empty) tmap.
  Proof.
    intros.
    unfold minimum_split in H1.
    remember (general_split (fun _ : Key => true)
            (fun _ : Key => false) default tree nil).
    destruct p.
    simpl in H1. subst.
    pose proof minimum_split_empty _ _ _ _ _ Heqp.
    subst.
    rewrite <- combine_default.
    rewrite <- (tag_update_default tmap).
    eapply general_split_abs; try eassumption.
    intros.
    left. reflexivity.
    apply Forall_nil.
    apply ST_nil. eapply search_popro; try eassumption.
    apply Abs_nil.
  Qed.
  Lemma minimum_split_tag_default :
   forall lo hi tree l,
    SearchTree' lo tree hi -> 
     l = minimum_split default tree nil ->
      Forall P l.
  Proof.
    intros.
    unfold minimum_split in H0.
    remember (general_split (fun _ : Key => true)
            (fun _ : Key => false) default tree nil).
    destruct p.
    simpl in H0. subst.
    eapply general_split_tag_default; try eassumption.
    intros.
    left. reflexivity.
    eapply ST_nil. eapply search_popro; try eassumption.
    apply Forall_nil.
  Qed.
  Lemma up_split_pro :
   forall tree h l b tag ,
    ( tree <> Empty \/ h <> nil) -> Forall fst_false h ->
     (l, b) = Up_split (minimum_split tag tree h) -> 
        (exists c k v t ri, b = T c Empty k v t ri).
  Proof.
    intro.
    induction tree.
    - intros.
      unfold minimum_split in H1.
      simpl in H1.
      destruct h.
      + destruct H. contradiction. contradiction.
      + destruct h. repeat destruct p.
        destruct b0.
        inversion H0. subst.
        contradiction.
        simpl in H1.
        inversion H1.
        exists c,k,v,t,r.
        reflexivity.
    - intros.
      unfold minimum_split in H1.
      simpl in H1.
      pose proof IHtree1 ((false, c, k, f (f v t) tag,
                default,
                tag_tree_t (Optt tag t) tree2)
                :: h) l b  (Optt tag t) .
      apply H2.
      right.
      unfold not; intro. inversion H3.
      eapply Forall_cons; try eassumption.
      reflexivity.
      auto.
  Qed.
  Definition match_tree_key  (t: RBtree) k : Prop :=
  match t with 
  |Empty => False
  |T _ _ x _ _ _ => x = k
  end.
  Lemma minimum_split_res_k : forall le c x v t ri h l b k tag lo hi,
   (le <> Empty) ->  SearchTree' lo (T c le x v t ri) hi -> SearchTree_half lo h hi ->
   (l, b) = Up_split  (minimum_split tag (T c le x v t ri) h) ->
     match_tree_key b k -> k <? x = true.
  Proof.
    intro.
    induction le.
    - intros.
      contradiction.
    - intros.
      inversion H0.  subst.
      inversion H12 . subst.
      destruct le1.
      + clear IHle1 IHle2.
        unfold minimum_split in H2.
        simpl in H2.
        inversion H2. subst.
        inversion H3. subst.
        eapply ltb_lt.
        eapply search_popro; try eassumption.
      + clear IHle2.
        assert (
        minimum_split tag
             (T c0 (T c (T c1 le1_1 k1 v1 t1 le1_2) k v t le2) x v0 t0 ri) h =
        minimum_split (Optt tag t0)
              (T c (T c1 le1_1 k1 v1 t1 le1_2) k v t le2) ((false, c0, x, f (f v0 t0) tag, default,tag_tree_t (Optt tag t0) ri) :: h) ).
       { unfold minimum_split. simpl. reflexivity. }
       rewrite H4 in H2.
       clear H4.
       assert (k0 <? k = true). {
       eapply IHle1.
       4: apply H2.
       discriminate.
       apply H12.
       eapply ST_cons_false.
       apply H1.
       eapply search_popro; try eassumption.
       eapply search_tag_tree_t; try eassumption.
       right. reflexivity.
       eapply search_popro; try eassumption.
       auto. }
       pose proof search_popro _ _ _ H15.
       eapply ltb_lt. TR 5.
  Qed.
  Lemma up_mini_equi :
  forall t l b k tag h lo hi,
   (t <> Empty ) -> SearchTree' lo  t hi -> SearchTree_half lo h hi ->
   (l, b) = Up_split  (minimum_split tag t h) ->
     match_tree_key b k ->
       (l, b) = insert_split k tag t h.
  Proof.
     intro.
     destruct t.
     - intros.
       contradiction.
     - revert c k v t2 t3.
       induction t1.
       + intros.
         unfold minimum_split in H2. simpl in H2.
         inversion H2. subst.
         inversion H3. subst.
         unfold insert_split. simpl.
         assert (k0 <? k0 = false).
         { apply ltb_false. apply lt_refl. }
         rewrite H4.
         rewrite f_tag.
         reflexivity.
       + intros.
         inversion H0.
         inversion H12. subst.
         clear IHt1_2.
         assert (k1 <? k0 = true ). { eapply minimum_split_res_k.
         4: apply H2. discriminate.
         apply H0.
         auto.
         auto. }
         unfold minimum_split in H2.
         assert (general_split (fun _ : Key => true) 
               (fun _ : Key => false) tag
               (T c0 (T c t1_1 k v t t1_2) k0 v0 t2 t3) h = 
                 general_split (fun _ : Key => true) 
               (fun _ : Key => false) (Optt tag t2)
               (T c t1_1 k v t t1_2) ((false, c0, k0, f (f v0 t2) tag, default,tag_tree_t (Optt tag t2) t3) :: h) ).
        { simpl. reflexivity. }
        rewrite H5 in H2.
        clear H5.
        assert (insert_split k1 tag  (T c0 (T c t1_1 k v t t1_2) k0 v0 t2 t3) h = 
                insert_split k1 (Optt tag t2)
               (T c t1_1 k v t t1_2) ((false, c0, k0, f (f v0 t2) tag, default,tag_tree_t (Optt tag t2) t3) :: h) ).
        { unfold insert_split. simpl.
          rewrite H4. reflexivity. }
        rewrite H5.
        eapply IHt1_1; try eassumption.
        discriminate.
        eapply ST_cons_false; try eassumption.
        eapply search_popro; try eassumption.
        eapply search_tag_tree_t; try eassumption.
        right. reflexivity.
        eapply search_popro; try eassumption.
  Qed.
  Lemma minimum_up_halftree : forall s lo hi k tag h l b,
    Forall (fun x: Half_tree =>  k < snd ( fst (fst (fst x)))) h->
    SearchTree' lo s hi -> SearchTree_half lo h hi ->
   (l, b) = Up_split  (minimum_split tag s h) ->
     match_tree_key b k ->
      Forall (fun x: Half_tree =>  k < snd ( fst (fst (fst x)))) l.
  Proof.
    intro.
    induction s.
    - intros.
      unfold minimum_split in H2. simpl in H2.
      destruct h.
      *
      inversion H2; subst.
      simpl in H3.
      contradiction.
      *
      destruct h. repeat destruct p.
      inversion H; subst.
      destruct b0.
      + inversion H2; subst. auto.
      + inversion H2; subst. auto.
    - intros.
      destruct s1.
      * simpl in H2.
        inversion H2; subst. auto.
      *
      assert (k0 <? k  = true).
      { eapply minimum_split_res_k; try eassumption.
        discriminate. }
      unfold minimum_split in H2.
      simpl in H2.
      inversion H0; subst.
      assert (SearchTree_half lo ((false, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) s2) :: h) k).
      { eapply ST_cons_false; try eassumption.
         eapply search_popro; try eassumption.
         eapply search_tag_tree_t; try eassumption.
         right. auto.
         eapply search_popro; try eassumption. }
      assert ( Forall (fun x : Half_tree => k0 < snd (fst (fst (fst x)))) ((false, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) s2) :: h)).
      { eapply Forall_cons; try eassumption.
        simpl.
        tr.
       }
      apply (IHs1 _ _ _ _ _ _ _ H6 H13 H5 H2 H3).
  Qed.
  Lemma minimum_up_halftree_false : forall s lo hi tag h l b,
    Forall fst_false h->
    SearchTree' lo s hi -> SearchTree_half lo h hi ->
   (l, b) = Up_split  (minimum_split tag s h) ->
      Forall fst_false l.
  Proof.
    intro.
    induction s.
    - intros.
      unfold minimum_split in H2. simpl in H2.
      destruct h.
      *
      inversion H2; subst.
      apply Forall_nil.
      *
      destruct h. repeat destruct p.
      inversion H; subst.
      simpl in  H5.
      destruct b0.
      + contradiction.
      + inversion H2; subst. auto.
    - intros.
      unfold minimum_split in H2.
      simpl in H2.
      inversion H0; subst.
      assert (SearchTree_half lo ((false, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) s2) :: h) k).
      { eapply ST_cons_false; try eassumption.
         eapply search_popro; try eassumption.
         eapply search_tag_tree_t; try eassumption.
         right. auto.
         eapply search_popro; try eassumption. }
      assert ( Forall fst_false ((false, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) s2) :: h)).
      { eapply Forall_cons; try eassumption.
        simpl.
        auto.
       }
      eapply IHs1; try eassumption.
  Qed.
  Lemma minimum_split_ht_false : forall s lo hi tag h l ,
    Forall fst_false h->
    SearchTree' lo s hi -> SearchTree_half lo h hi ->
   l = minimum_split tag s h ->
      Forall fst_false l.
  Proof.
    intro.
    induction s.
    - intros.
      unfold minimum_split in H2. simpl in H2.
      destruct h.
      *
      inversion H2; subst.
      apply Forall_nil.
      *
      destruct h. repeat destruct p.
      inversion H; subst.
      simpl in  H5.
      destruct b.
      + contradiction.
      + inversion H; subst. auto.
    - intros.
      inversion H0; subst.
      remember ( minimum_split tag (T c s1 k v t s2) h).
      unfold minimum_split in Heql.
      simpl in Heql.
      assert (SearchTree_half lo ((false, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) s2) :: h) k).
      { eapply ST_cons_false; try eassumption.
         eapply search_popro; try eassumption.
         eapply search_tag_tree_t; try eassumption.
         right. auto.
         eapply search_popro; try eassumption. }
      assert ( Forall fst_false ((false, c, k, f (f v t) tag, default,
          tag_tree_t (Optt tag t) s2) :: h)).
      { eapply Forall_cons; try eassumption.
        simpl.
        auto.
       }
      eapply IHs1; try eassumption.
  Qed.
  Lemma minimum_split_lastBlack :
   forall  tree t0 h l,
    (Black_tree tree /\ h =nil \/ last_black h) ->
    l = minimum_split  t0 tree h ->
       last_black l.
  Proof.
    intros.
    unfold minimum_split in H0.
    remember  (general_split (fun _ : Key => true) 
           (fun _ : Key => false) t0 tree h).
    destruct p. simpl in H0. subst.
    revert t0 h l0 r H Heqp.
    induction tree.
    - intros.
      super_destruct H.
      + inversion H.
      + simpl in Heqp.
        inversion Heqp;subst.
        auto.
    - intros.
      simpl in Heqp.
      eapply IHtree1. 2: apply Heqp.
      right.
      
      super_destruct H.
      subst. simpl.
      simpl in H. auto.
      simpl.
      destruct h.
      inversion H.
      auto.
  Qed.
  Lemma caseTTF_notempty : 
    forall s h  n b,
     (b , n ) = CaseTTF_sol s h false ->
      b <> Empty.
  Proof.
    intros.
    destruct h. repeat destruct p.
    unfold CaseTTF_sol in H.
    repeat (
      match goal with
      | H : _ = (if ?x then _ else _) |- _ => destruct x
      | H: _ = (match ?t with 
         |Empty  => _ | T _ _ _ _ _ _ => _ 
         end) |- _  => destruct t
      | H0: _ = (complete_tree_one _ _, _ ) |- _ => simpl;simpl in H;inversion H0; subst
      | H0:  ( _ , _) =
       (CaseTwo_sol ?s ?h, _ ) |- _ => inversion H0;subst b
      | H0:  ( _ , _) =
       (CaseThree_sol ?s ?h, _ ) |- _ => inversion H0;subst b
      | H0:  ( _ , _) =
       (CaseFour_sol ?s ?h, _ ) |- _ => inversion H0;subst b
      | |- T _ _ _ _ _ _ <> Empty => discriminate
      end
    ).
  Qed.
  Lemma delete_split_rb_dep :
   forall tree  k l s n,
    is_redblack_dep tree n ->
      (l, s) = delete_split k default tree nil ->
      (exists n' ,  is_redblack_dep s n' /\  is_redblack_dep_half l n n' ).
  Proof.
    intros.
    eapply general_split_RB_dep_enhance; try eassumption.
    eapply insert_lb_rb.
    apply IsRB_dep_nil.
  Qed.
  Lemma up_split_notempty : forall  l b c ll k v t rr,
    (l, b) = Up_split (minimum_split default (T c ll k v t rr) nil) ->
      b<>Empty.
  Proof.
    intros.
    assert (exists (c : color) (k : Key) (v : Value) (t : Tag) (ri : RBtree),
      b = T c Empty k v t ri).
    eapply up_split_pro;try eassumption.
    
    left;discriminate.
    apply Forall_nil.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    subst. discriminate.
  Qed.
  Lemma up_split_leftempty : forall l0 c4 le k3 v3 t3 r2 c3 r2_1 k2 v2 t2 r2_2,
  (l0, T c4 le k3 v3 t3 r2) =
         Up_split (minimum_split default (T c3 r2_1 k2 v2 t2 r2_2) nil) ->
          le = Empty.
  Proof.
    intros.
    assert (exists (c : color) (k : Key) (v : Value) (t : Tag) (ri : RBtree),
      T c4 le k3 v3 t3 r2 = T c Empty k v t ri).
    eapply up_split_pro;try eassumption.
    
    left;discriminate.
    apply Forall_nil.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    inversion H0;subst.
    auto.
  Qed.
  Lemma up_split_dep_Red : forall l  k3 v3 t3 r2 c3 r2_1 k2 v2 t2 r2_2 n lo hi,
   is_redblack_dep (T c3 r2_1 k2 v2 t2 r2_2) n ->
    SearchTree' lo (T c3 r2_1 k2 v2 t2 r2_2) hi->
    (l, T Red Empty k3 v3 t3 r2) =
         Up_split (minimum_split default (T c3 r2_1 k2 v2 t2 r2_2) nil) ->
       is_redblack_dep r2 0 /\ is_redblack_dep_half l n 0.
  Proof.
    intros.
    assert ( (l, T Red Empty k3 v3 t3 r2) =  insert_split k3 default (T c3 r2_1 k2 v2 t2 r2_2) nil).
    eapply up_mini_equi;try eassumption.
    discriminate.
    apply ST_nil. eapply search_popro;try eassumption.
    reflexivity.
    
    assert (exists n' ,  is_redblack_dep (T Red Empty k3 v3 t3 r2) n' /\ is_redblack_dep_half l n n' ).
    eapply general_split_RB_dep_enhance;try eassumption.
    eapply insert_lb_rb.
    apply IsRB_dep_nil.
    
    destruct H3.
    destruct H3.
    inversion H3;subst.
    inversion H11;subst.
    split; auto.
  Qed.
  Lemma up_split_dep_Black : forall l  k3 v3 t3 r2 c3 r2_1 k2 v2 t2 r2_2 n lo hi,
   is_redblack_dep (T c3 r2_1 k2 v2 t2 r2_2) n ->
    SearchTree' lo (T c3 r2_1 k2 v2 t2 r2_2) hi->
    (l, T Black Empty k3 v3 t3 r2) =
         Up_split (minimum_split default (T c3 r2_1 k2 v2 t2 r2_2) nil) ->
       is_redblack_dep r2 0 /\ is_redblack_dep_half l n 1.
  Proof.
    intros.
    assert ( (l, T Black Empty k3 v3 t3 r2) =  insert_split k3 default (T c3 r2_1 k2 v2 t2 r2_2) nil).
    eapply up_mini_equi;try eassumption.
    discriminate.
    apply ST_nil. eapply search_popro;try eassumption.
    reflexivity.
    
    assert (exists n' ,  is_redblack_dep (T Black Empty k3 v3 t3 r2) n' /\ is_redblack_dep_half l n n' ).
    eapply general_split_RB_dep_enhance;try eassumption.
    eapply insert_lb_rb.
    apply IsRB_dep_nil.
    
    destruct H3.
    destruct H3.
    inversion H3;subst.
    inversion H11;subst.
    split; auto.
  Qed.


(*Delete SearchTree*)
Lemma delete_with_no_balance_st:
  forall k t b h co ,
   SearchTree t -> 
   (h, b, co) = delete_with_no_balance k t ->
    (exists x y, SearchTree' x b y /\ SearchTree_half x h y).
Proof.
  intros.
  unfold delete_with_no_balance in H0.
  remember ( delete_split k default t nil) . destruct p.
  pose proof delete_split_st _ _ _ _ H Heqp.
  destruct H1. destruct H1. super_destruct H1.
  assert (k < x0). { tr. }
  assert (x < k). { tr. }
  destruct r.
  - inversion H0. exists x, x0.
    split.
    eapply ST_E; tr.
    auto.
  - inversion H2;subst.
    inversion H0.
    destruct r1.
    + destruct r2.
       inversion H8. exists x, x0. split. eapply ST_E; tr. auto.
       inversion H8. exists x, x0. split. 2: auto.
       inversion H16;subst.
       pose proof search_popro _ _ _ H15.
       eapply ST_T; try eassumption.
       eapply search_popro3; try eassumption.
    + destruct r2.
      * inversion H8. subst.
        inversion H15;subst.
        pose proof search_popro _ _ _ H16.
        exists x,x0. split. 2: auto.
        eapply ST_T; try eassumption.
        eapply search_popro2; try eassumption.
      *
        remember ( Up_split (minimum_split default (T c1 r2_1 k2 v1 t2 r2_2) nil)).
        destruct p.
        assert ( exists c k v t ri, r = T c Empty k v t ri) .
        { eapply up_split_pro; try eassumption.
          left.
          unfold not; intro. inversion H7.
          apply Forall_nil. }
        destruct H7. destruct H7. destruct H7. destruct H7. destruct H7.
        subst.
        inversion H8 ;subst.
        inversion H2. subst.
        inversion H19; subst.
        remember (T c0 r1_1 k1 v0 t1 r1_2) as delete_left.
        
        pose proof search_popro _ _ _ H15.
        pose proof search_popro _ _ _ H20.
        pose proof search_popro _ _ _ H21.
        
        assert (SearchTree_half k0 nil x0).
        {
         eapply ST_nil; tr.
        }
        assert ((l0, T x1 Empty x2 x3 x4 x5) = insert_split x2  default (T c1 r2_1 k2 v1 t2 r2_2) nil ).
          { eapply up_mini_equi;
            try eassumption.
            discriminate.
            reflexivity. }
        assert ((x2 <? x0) = true /\ (k0 <? x2) = true).
        { eapply insert_k_st; try eassumption.
          discriminate.
           }
        assert (Forall fst_false l0 ).
        { eapply (minimum_up_halftree_false (T c1 r2_1 k2 v1 t2 r2_2) ); try eassumption.
          apply Forall_nil. }
        
        pose proof insert_st_pro k0 x0 _ _ _ _ _ _ H19 H11 H12.
        destruct H17. destruct H17. super_destruct H17.
        inversion H22. subst.
        
        exists x2, x7. split. auto.
        assert (SearchTree_half_out (min_k k0 k0) l0 (max_k x0 x0)).
          { eapply insert_st_out; try eassumption.
            eapply ST_out_nil; tr. }
        rewrite min_self in H25.
        rewrite max_self in H25.
        
        pose proof min_lte _ _ H24.
        rewrite <- H26.
        destruct H13.
        assert (x2 < x0). {tr. }
        assert (k0 < x2). {tr. }
        pose proof search_popro _ _ _ H34.
        eapply  false_ht_true_app_st; try eassumption.
        eapply search_popro2; try eassumption.
Qed.
Lemma caseTwo_st :
  forall s h lo hi  b,
   SearchTree' lo (complete_tree_one s h) hi ->
     b = CaseTwo_sol s h ->
      SearchTree' lo b hi.
Proof.
  intros.
  unfold CaseTwo_sol in H0.
  destruct h.
  repeat destruct p.
  repeat (
   match goal with
   | H : _ = (if ?x then _ else _ ) |- _ => destruct x
   | H: _ = (match ?t with 
       |Empty  => _ | T _ _ _ _ _ _ => _ 
       end) |- _  => destruct t
   | H0: _ = complete_tree_one _ _ |- _ => simpl;simpl in H, H0; subst;auto
   | H: SearchTree' _ (complete_tree_one _ _) _ |- _ => simpl;simpl in H;inversion H;subst;try (eapply ST_T; try eassumption)
   | H: SearchTree' ?x (T _ ?l ?k ?v ?t ?r) ?y 
           |-  SearchTree' ?x (T _ ?l ?k ?v ?t ?r) ?y 
               => inversion H;subst;try (eapply ST_T; try eassumption)
   end
  ).
Qed.
Lemma caseFour_st :
  forall s h lo hi  b,
   SearchTree' lo (complete_tree_one s h) hi ->
     b = CaseFour_sol s h ->
      SearchTree' lo b hi.
Proof.
  intros.
  destruct h. repeat destruct p.
  unfold CaseFour_sol in H0.
  destruct b0.
  - destruct r.
      subst. auto.
    destruct c0.
      subst. auto.
    destruct r1.
      subst. auto.
    destruct c0.
    + simpl in H, H0. inversion H; subst. inversion H9; subst. inversion H8; subst.
      eapply ST_T; try eassumption.
      eapply ST_T; try eassumption.
      eapply ST_T; try eassumption.
      eapply search_tag_tree_t; try eassumption.
    + subst. auto.
  - destruct r.
      subst. auto.
    destruct c0.
      subst. auto.
    destruct r2.
      subst. auto.
    destruct c0.
    + simpl in H, H0. inversion H; subst. inversion H10; subst. inversion H11; subst.
      eapply ST_T; try eassumption.
      eapply ST_T; try eassumption.
      eapply search_tag_tree_t; try eassumption.
      eapply ST_T; try eassumption.
    + subst. auto.
Qed.
Lemma caseThree_st :
  forall s h lo hi  b,
   SearchTree' lo (complete_tree_one s h) hi ->
     b = CaseThree_sol s h ->
      SearchTree' lo b hi.
Proof.
  intros.
  destruct h. repeat destruct p.
  unfold CaseThree_sol in H0.
  repeat (
   match goal with
   | H : _ = (if ?x then _ else _ ) |- _ => destruct x
   | H: _ = (match ?t with 
       |Empty  => _ | T _ _ _ _ _ _ => _ 
       end) |- _  => destruct t
   | H0: _ = complete_tree_one _ _ |- _ => simpl;simpl in H, H0; subst;auto
   | H: SearchTree' _ (complete_tree_one _ _) _ |- _ => simpl;simpl in H;inversion H;subst;
                                                        try (inversion H9;subst);try(inversion H10;subst);
                                                        try(inversion H11;subst);try(inversion H12;subst);
                                                        try (eapply ST_T; try eassumption)
   | |- SearchTree' _ (tag_tree_t _ _) _ => eapply search_tag_tree_t
   | |- SearchTree' _ (makeBlack _) _ => simpl
   end;
   try (eapply ST_T; try eassumption);eauto
   ).
Qed.

Lemma caseTTF_st :
  forall s h lo hi n b,
   SearchTree' lo (complete_tree_one s h) hi ->
     (b, n ) = CaseTTF_sol s h false->
      SearchTree' lo b hi.
Proof.
  intros.
  destruct h.
  repeat destruct p.
  unfold CaseTTF_sol in H0.
  repeat (
    match goal with
    | H : _ = (if ?x then _ else _) |- _ => destruct x
    | H: _ = (match ?t with 
       |Empty  => _ | T _ _ _ _ _ _ => _ 
       end) |- _  => destruct t
    | H0: _ = (complete_tree_one _ _, _ ) |- _ => simpl;simpl in H;inversion H0; subst;auto
    | H0:  ( _ , _) =
     (CaseTwo_sol ?s ?h, _ ) |- _ => inversion H0;subst b; eapply caseTwo_st; try eassumption; eauto
    | H0:  ( _ , _) =
     (CaseThree_sol ?s ?h, _ ) |- _ => inversion H0;subst b; eapply caseThree_st; try eassumption; eauto
    | H0:  ( _ , _) =
     (CaseFour_sol ?s ?h, _ ) |- _ => inversion H0;subst b; eapply caseFour_st; try eassumption; eauto
    end
  ).
Qed.
Lemma caseOne_st :
  forall s h lo hi n b,
   SearchTree' lo (complete_tree_one s h) hi ->
     (b, n ) = CaseOne_sol s h false->
      SearchTree' lo b hi.
Proof. 
  intros.
  destruct h. repeat destruct p.
  unfold CaseOne_sol in H0.
  repeat (match goal with
    | H : _ = (if ?x then _ else _) |- _ => destruct x
    | H: _ = (match ?t with 
       |Empty  => _ | T _ _ _ _ _ _ => _ 
       end) |- _  => destruct t
    | H0: _ = (complete_tree_one _ _, _ ), H: SearchTree' _ (complete_tree_one _ _) _
               |- _ => simpl in H;inversion H0; subst;simpl;auto
  end).
  
     - remember  ( CaseTTF_sol s
          (true, Red, k, v, default, tag_tree_t t0 r2) false) as u.
       destruct u.
       repeat (match goal with
        | H0 : (?b, ?n) =  (if ?x then _ else _ ) |- _ => simpl in H;inversion H; subst;
                                                         try (inversion H9;subst);
                                                          destruct x
        | H: _ = (complete_tree_one ?r ?h, true),
          H1: (?r, true) = CaseTTF_sol _ _ false |- _ => inversion H;subst;eapply ST_T;try eassumption
        | |- SearchTree' _ (tag_tree_t _ _ ) _  =>  eapply search_tag_tree_t;assumption
        | H1: (?r, _ ) = CaseTTF_sol ?s ?h false |-  SearchTree' _ ?r _ 
                                                    => eapply caseTTF_st; try eassumption
        | H: _ = match ?r with 
                |Empty => _ | T _ _ _ _ _ _ => _  
                end |- _  => destruct r 
        | H: (Empty, _) = CaseTTF_sol _ _ _ |- _ => pose proof caseTTF_notempty _ _ _ _ H;contradiction 
        | H: (?b, _) = (complete_tree_one (makeBlack _) _ , _) 
                             |- SearchTree' _ ?b _  => inversion H;subst;eapply ST_T;try eassumption
        | H: (T Red ?l ?k ?v ?t ?r, false) = CaseTTF_sol ?s _ _ 
                             |- SearchTree' _ (T Black ?l ?k ?v ?t ?r) _  
                         => eapply st_color;eapply (caseTTF_st s);try eassumption
        | |- SearchTree' _ (complete_tree_one _ _) _ => simpl;eapply ST_T;try eassumption
        end).
    -  remember (CaseTTF_sol s
          (false, Red, k, v, default, tag_tree_t t0 r1) false) as u.
      destruct u.
      repeat (match goal with
        | H0 : (?b, ?n) =  (if ?x then _ else _ ) |- _ => simpl in H;inversion H; subst;
                                                          inversion H10;subst;
                                                          destruct x
        | H: _ = (complete_tree_one ?r ?h, true),
          H1: (?r, true) = CaseTTF_sol _ _ false |- _ => inversion H;subst;eapply ST_T;try eassumption
        | |- SearchTree' _ (tag_tree_t _ _ ) _  =>  eapply search_tag_tree_t;assumption
        | H1: (?r, _ ) = CaseTTF_sol ?s ?h false |-  SearchTree' _ ?r _ 
                                                    => eapply caseTTF_st; try eassumption
        | H: _ = match ?r with 
                |Empty => _ | T _ _ _ _ _ _ => _  
                end |- _  => destruct r 
        
        | H: (?b, _) = (complete_tree_one (makeBlack _) _ , _) 
                             |- SearchTree' _ ?b _  => inversion H;subst;eapply ST_T;try eassumption
        | H: (T Red ?l ?k ?v ?t ?r, false) = CaseTTF_sol ?s _ _ 
                             |- SearchTree' _ (T Black ?l ?k ?v ?t ?r) _  
                         => eapply st_color;eapply (caseTTF_st s);try eassumption
        | |- SearchTree' _ (complete_tree_one _ _) _ => simpl;eapply ST_T;try eassumption 
        end).
Qed.

  Lemma complete_st_makeblack:forall l lo hi tree,
      SearchTree_half lo l hi -> SearchTree' lo tree hi -> 
      (exists x y,  SearchTree' x (makeBlack(complete_tree l tree)) y).
  Proof.
    intros.
    pose proof complete_st_pre _ _ _ _ H H0.
    inversion H1. subst.
    exists lo0, hi0.
    eapply makeBlack_st;try eassumption.
  Qed.
  Lemma delete_st_balance_Red : forall r l lo hi h b ,
   SearchTree' lo r hi -> SearchTree_half lo l hi ->
      (b, h) = delete_balance r l Red ->
        (exists x y,  SearchTree' x (makeBlack(complete_tree h b)) y).
  Proof.
    intros.
    destruct l.
    -  inversion H1. subst. simpl. exists lo, hi.
        eapply makeBlack_st;try eassumption.
    - inversion H1. subst.
      eapply complete_st_makeblack; try eassumption.
  Qed.
  Lemma delete_st_balance_Black : forall  l r lo hi h b ,
   SearchTree' lo r hi -> SearchTree_half lo l hi ->
      (b, h) = delete_balance r l Black ->
        (exists x y,  SearchTree' x (makeBlack(complete_tree h b)) y).
  Proof.
    intro.
    induction l.
    - intros. inversion H1. subst. simpl. exists lo, hi.
        eapply makeBlack_st;try eassumption.
    - intros.
      destruct a. repeat destruct p.
      unfold delete_balance in H1. fold delete_balance in H1.
      
      repeat (
      match goal with
      | H : (b, h) = match ?r with | Empty => _ | _ => _ end |- _ =>destruct r
      | H : (b, h) = match ?c with | Red  => _ | Black  => _ end |- _ =>destruct c
      | H: (_ , h) = (let (s', b) := 
         CaseOne_sol ?s (?bb, ?cc, ?kk, ?vv, ?tt, ?bbb) false in _ ) |- _ 
         => remember (CaseOne_sol s (bb, cc, kk, vv, tt, bbb) false) as u;destruct u
      | H: (_ , h) = (let (s', b) := 
         CaseTTF_sol ?s (?bb, ?cc, ?kk, ?vv, ?tt, ?bbb) false in _ ) |- _ 
         => remember (CaseTTF_sol s (bb, cc, kk, vv, tt, bbb) false) as w;destruct w
      | H: (b, h) = (if ?x then _ else _ )|-_ => destruct x
      | H: (b, h) = (?bb, ?hh) |- _ => inversion H;subst 
      | H: SearchTree_half ?lo ?l ?hi
        |- (exists x y , SearchTree' x (makeBlack (complete_tree ?l ?r)) y ) 
        => eapply (complete_st_makeblack l lo hi); try eassumption
      | H: SearchTree_half _ (_ :: l) _ |- _ =>inversion H;subst;clear H
      | H: (?r, ?n) = CaseOne_sol ?s ?h false |- SearchTree' ?lo ?r ?hi 
        => eapply (caseOne_st s h lo hi n r); try eassumption
      | H: (?r, ?n) = CaseTTF_sol ?s ?h false |- SearchTree' ?lo ?r ?hi 
        => eapply (caseTTF_st s h lo hi n r); try eassumption
      | H : (b,h) = delete_balance ?r l Black,
        H1: SearchTree_half ?lo l ?hi
        |- (exists x y : Key, SearchTree' x (makeBlack (complete_tree h b)) y)
        => eapply (IHl r lo hi h b);try eassumption
      | |- SearchTree' _ (complete_tree_one _ _) _ => simpl
      | |- SearchTree' _ (T _ _ _ _ _ _) _ => stt 12
      | |- _ < _ => TR 5
      end).
  Qed.
Theorem delete_st :
 forall k t ,
    SearchTree t -> (SearchTree (delete k t)).
Proof.
  intros.
  unfold delete.
  remember (delete_into_base_half k t).
  destruct p.
  unfold delete_into_base_half in Heqp.
  remember (delete_with_no_balance k t).
  destruct p.
  destruct p.
  assert (exists x y, SearchTree' x r0 y /\ SearchTree_half x l0 y).
  { eapply delete_with_no_balance_st;try eassumption. }
  destruct H0. destruct H0. destruct H0.
  destruct c.
  + assert (exists x y,  SearchTree' x (makeBlack(complete_tree l r)) y).
    eapply delete_st_balance_Red; try eassumption.
    destruct H2. destruct H2.
    eapply ST_intro;try eassumption.
  + assert (exists x y,  SearchTree' x (makeBlack(complete_tree l r)) y).
    eapply delete_st_balance_Black; try eassumption.
    destruct H2. destruct H2.
    eapply ST_intro;try eassumption.
Qed.

(*TODO TODO*)
(*Delete SearchTree with boundary*)
 Lemma search_half_out_app: forall l1 l2 lo hi low high,
       SearchTree_half_out lo l1 hi ->
        SearchTree_half low l1 high ->
         SearchTree_half_out low l2 high ->
          SearchTree_half_out (min_k lo low) (l2 ++ l1) (max_k hi high). 
Proof.
  intros. revert lo hi low high l1 H H0 H1.
  induction l2.
  - intros. simpl.
    eapply search_half_popro2_lte with hi.
    eapply search_half_popro3_lte with lo; eauto.
    TRM 2. TRM 2.
  - intros. 
    simpl.
    destruct a. repeat destruct p.
    inversion H1;subst.
    assert (SearchTree_half_out (min_k low0 lo0) l2 (max_k high0 hi0)).
    {
     apply search_half_popro3_lte with lo0.
     apply search_half_popro2_lte with hi0;eauto.
     TRM 2. TRM 2. }
    pose proof (IHl2 lo hi (min_k low0 lo0) (max_k high0 hi0) l1 H H0 H2).
    eapply search_half_popro3_lte with (min_k low0 (min_k lo (min_k low0 lo0)) ).
    eapply search_half_popro2_lte with (max_k high0 (max_k hi (max_k high0 hi0))).
    apply ST_out_cons; eauto.
    rewrite (max_comm high0 hi0).
    rewrite  <- (max_asso hi _ _ ).
    TRM 5.
    rewrite (min_comm lo _).
    rewrite (min_asso low0).
    TRM 5.
Qed.
Lemma delete_st'_without_b : forall lo hi t k  l s c,
 SearchTree' lo t hi -> 
 (l, s, c) = delete_with_no_balance k t->
   SearchTree_half_out lo l hi /\ 
    (exists x y, SearchTree' x s y /\ SearchTree_half x l y /\ (lo <= x /\ y<= hi)).
Proof.
 intros.
 unfold delete_with_no_balance in H0.
 remember (delete_split k default t nil). destruct p.
 unfold delete_split in Heqp.
 assert (SearchTree_half lo nil hi). { apply ST_nil. eapply search_popro;eauto. }
 pose proof insert_st_pro _ _ _ _ _ _ _ _ H H1 Heqp.
 destruct H2. destruct H2. super_destruct H2.
 assert (SearchTree_half_out lo nil hi). { apply ST_out_nil. eapply search_popro;eauto. } 
 pose proof insert_st_out _ _ _ _ _ _ _ _ _ _  H H1 H6 Heqp.
 rewrite min_self in H7. rewrite max_self in H7.
 
  destruct r.
  - inversion H0. subst. 
     split. auto.
     exists x,x0. tauto.
  - inversion H3;subst.
    simpl in H0.
    destruct r1, r2.
    * inversion H0;subst. 
      split. auto.
      exists x, x0.
      split. stt2 5. tauto.
    * inversion H0;subst. 
      split. auto.
      exists x,x0. inversion H17;subst.
      split. stt2 5.
      tauto.
    * inversion H0;subst. 
      split. auto.
      exists x,x0.
      split. 
       inversion H16;subst. stt2 5.
       tauto.
    * remember ( Up_split (minimum_split default (T c2 r2_1 k2 v1 t2 r2_2) nil)).
      destruct p.
      assert (Forall fst_false nil). { apply Forall_nil. }
      assert (exists (c : color) (k : Key) (v : Value) (t : Tag) (ri : RBtree),
    r = T c Empty k v t ri).
     {  eapply up_split_pro;try eassumption. left. discriminate. }
     do 5 destruct H9.
     subst r.
     assert ( (l1, T x1 Empty x2 x3 x4 x5) = insert_split x2 default (T c2 r2_1 k2 v1 t2 r2_2) nil).
     { eapply up_mini_equi;try eassumption. discriminate.
       apply ST_nil. eapply search_popro;try eassumption.
       reflexivity. }
    inversion H0;subst.
    assert (exists x y : Key,
        SearchTree_half x l1 y /\ SearchTree' x (T x1 Empty x2 x3 x4 x5) y /\ k0 <= x /\ y <= x0).
    { eapply insert_st_pro; try eassumption. apply ST_nil. TRM 2. }
    do 2 destruct  H10. super_destruct H10.
    inversion H11;subst.
    assert ( x2 <= k2).
    { destruct r2_1.
      ** simpl in Heqp0. inversion Heqp0;subst. right. auto.
      ** left. eapply ltb_lt.
      eapply minimum_split_res_k; try eassumption.
      discriminate. 
      apply ST_nil. TRM 1.
      reflexivity. }
    assert (Forall fst_false l1).
    { eapply (minimum_up_halftree_false (T c2 r2_1 k2 v1 t2 r2_2)) ; try eassumption.
      apply ST_nil; TRM 2. }
    assert ( Forall (fun x : Half_tree => x2 < snd (fst (fst (fst x)))) l1).
    { eapply  (minimum_up_halftree  (T c2 r2_1 k2 v1 t2 r2_2));try eassumption.
      apply Forall_nil.
      apply ST_nil;TRM 2.
      reflexivity. }
     assert (SearchTree_half_out (min_k k0 k0) l1 (max_k x0 x0)).
     { eapply insert_st_out;try eassumption.
       apply ST_nil. TRM 2.
       apply ST_out_nil. TRM 2. }
     rewrite min_self in H19. rewrite max_self in H19.
    
     assert (SearchTree_half_out x2 l1 x0).
     { eapply (halftree_false_key_st l1 k0 x0);eauto. TRM 2. }
     clear H19.
     split.
     + 
       assert (SearchTree_half x2 ((true, c0, x2, x3, t0, T c1 r1_1 k1 v0 t1 r1_2) :: l0) x0).
      { eapply ST_cons_true; eauto. TRM 2.
        stt2 4. TRM 1. TRM 2. }
      assert (SearchTree_half_out (min_k lo lo) ((true, c0, x2, x3, t0, T c1 r1_1 k1 v0 t1 r1_2) :: l0) (max_k hi hi)).
      { eapply ST_out_cons; eauto.
        constructor.
        stt2 10. TRM 5. }
      rewrite min_self in H21. rewrite max_self in H21.
      pose proof search_half_out_app ((true, c0, x2, x3, t0, T c1 r1_1 k1 v0 t1 r1_2) :: l0) l1 lo hi x2 x0 H21 H19 H20.
      erewrite min_lte in H22.
      rewrite max_comm in H22.
      erewrite max_lte in H22.
      auto.
      TRM 5.
      TRM 10.
     + exists x2 ,x7.
       split; eauto.
       split; try (TRM 10).
       assert (SearchTree' x (T c1 r1_1 k1 v0 t1 r1_2) x2).
       { stt2 10. }
      
       assert (x2 < x0). { TRM 10. }
       assert (x2 < x7). { TRM 10. }
       pose proof false_ht_true_app_st l1 c0 x2 x3 t0 _ l0  x6 x7 x x0 _ H15 H10 H19 H2 H21 H22 H20.
       eapply search_h_popro2; eauto.
       TRM 4.
Qed.
Lemma delete_st'_b_Black : forall l r b h lo hi x y,
    SearchTree_half_out lo l hi ->
     SearchTree' x r y ->
      SearchTree_half x l y ->
       lo <= x -> y<= hi ->
        (b, h) = delete_balance r l Black ->
          SearchTree' lo (complete_tree h b) hi.
Proof.
  intro.
  induction l.
  - intros. inversion H4;subst.
    simpl.
    stt2 10.
  - intros.
    destruct a. repeat destruct p.
    unfold delete_balance in H4. fold delete_balance in H4.
    repeat (match goal with
    | H : (b, h) = match ?r with | Empty => _ | _ => _ end |- _ =>destruct r
      | H : (b, h) = match ?c with | Red  => _ | Black  => _ end |- _ =>destruct c
      | H: (_ , h) = (let (s', b) := 
         CaseOne_sol ?s (?bb, ?cc, ?kk, ?vv, ?tt, ?bbb) false in _ ) |- _ 
         => remember (CaseOne_sol s (bb, cc, kk, vv, tt, bbb) false) as u;destruct u
      | H: (_ , h) = (let (s', b) := 
         CaseTTF_sol ?s (?bb, ?cc, ?kk, ?vv, ?tt, ?bbb) false in _ ) |- _ 
         => remember (CaseTTF_sol s (bb, cc, kk, vv, tt, bbb) false) as w;destruct w
      | H: (b, h) = (if ?x then _ else _ )|-_ => destruct x
      | H: (b, h) = (?bb, ?hh) |- _ => inversion H;subst 
      |  H: SearchTree_half_out ?lo ?l ?hi,
       H1: SearchTree_half ?x ?l ?y
       |- SearchTree' _ (complete_tree ?l Empty ) _
       =>  eapply search_complete;eauto
     | H: SearchTree_half_out ?lo ?l ?hi,
       H1: SearchTree_half ?x ?l ?y
       |- SearchTree' _ (complete_tree ?l Empty ) (max_k y hi)
       =>  eapply search_popro3_lte with (min_k x lo)
     | H: SearchTree_half_out ?lo ?l ?hi,
       H1: SearchTree_half ?x ?l ?y
       |- SearchTree' _ (complete_tree ?l Empty ) _
       =>  eapply search_popro2_lte with (max_k y hi)
     |  H: SearchTree_half_out ?lo ?l ?hi,
       H1: SearchTree_half ?x ?l ?y
       |- SearchTree' _ (complete_tree ?l (T _ _ _ _ _ _)) _
       =>  eapply search_complete;eauto
     | H: SearchTree_half_out ?lo ?l ?hi,
       H1: SearchTree_half ?x ?l ?y
       |- SearchTree' _ (complete_tree ?l (T _ _ _ _ _ _) ) (max_k y hi)
       =>  eapply search_popro3_lte with (min_k x lo)
     | H: SearchTree_half_out ?lo ?l ?hi,
       H1: SearchTree_half ?x ?l ?y
       |- SearchTree' _ (complete_tree ?l(T _ _ _ _ _ _)) _
       =>  eapply search_popro2_lte with (max_k y hi)
     | |- _ <= _ => TRM 10
     | |- _ /\ _ => TRM 10
     | |- SearchTree' _ (complete_tree_one _ _ ) _ => simpl
     | |- SearchTree' _ (T _ _ _ _ _ _) _ => stt2 10
     | |- SearchTree_half (max_k _ _ ) _ _ => eapply search_h_popro3;eauto 
     | |- SearchTree_half _ _ (min_k _ _ ) => eapply search_h_popro2;eauto 
     | H: SearchTree_half_out ?lo ?l ?hi
      |- SearchTree_half_out _ ?l ?hi => eapply search_half_popro3_lte with lo;eauto
     | H: SearchTree_half_out ?lo ?l ?hi
      |- SearchTree_half_out _ ?l _ => eapply search_half_popro2_lte with hi
     | H: SearchTree_half_out _ ((_,_,_,_,_,_)::_) _ 
      |- _ => inversion H;subst;clear H
     | H: SearchTree_half _ ((_,_,_,_,_,_)::_) _ 
      |- _ => inversion H;subst;clear H
     | H: SearchTree_half_tree _ _ _ 
      |- _ => inversion H;subst;clear H
     | H: (?r, _ )= CaseOne_sol ?s ?h false
      |- SearchTree' _ ?r _ => eapply caseOne_st;eauto
     | H: (?r, _ )= CaseTTF_sol ?s ?h false
      |- SearchTree' _ ?r _ => eapply caseTTF_st;eauto
     | H: (?b, ?h) = delete_balance ?r ?l Black,
      H1: SearchTree' ?lo (T _ _ _ _ _ _ ) ?k,
      H2: SearchTree' ?low (T _ _ _ _ _ _ ) ?k,
      H3: SearchTree_half ?lo ?l ?y 
     |- SearchTree' _ (complete_tree ?h ?b) _  
     => eapply (IHl r b h _ _ (max_k lo low) y);eauto
     | H: (?b, ?h) = delete_balance ?r ?l Black,
      H1: SearchTree' ?k (T _ _ _ _ _ _ ) ?hi,
      H2: SearchTree' ?k (T _ _ _ _ _ _ ) ?high,
      H3: SearchTree_half ?x ?l ?hi 
     |- SearchTree' _ (complete_tree ?h ?b) _  
     => eapply (IHl r b h _ _ x (min_k hi high));eauto
     | H: SearchTree_half_out ?lo0 ?l ?hi0,
      H1: SearchTree' ?lo (T _ _ _ _ _ _ ) ?k,
      H2: SearchTree' ?low (T _ _ _ _ _ _ ) ?k,
      H3: SearchTree_half ?lo ?l ?y 
     |- SearchTree' (min_k (max_k ?lo ?low) ?lo0) (complete_tree ?l ?r) (max_k ?y ?hi0) 
     => eapply search_complete;eauto
    |  H: SearchTree_half_out ?lo0 ?l ?hi0,
      H1: SearchTree' ?lo (T _ _ _ _ _ _ ) ?k,
      H2: SearchTree' ?low (T _ _ _ _ _ _ ) ?k,
      H3: SearchTree_half ?lo ?l ?y 
     |- SearchTree' _ (complete_tree ?l ?r) (max_k ?y ?hi0) 
     => eapply search_popro3_lte with (min_k (max_k lo low) lo0)
    |  H: SearchTree_half_out ?lo0 ?l ?hi0,
      H1: SearchTree' ?lo (T _ _ _ _ _ _ ) ?k,
      H2: SearchTree' ?low (T _ _ _ _ _ _ ) ?k,
      H3: SearchTree_half ?lo ?l ?y 
     |- SearchTree' _ (complete_tree ?l ?r) _  
     => eapply search_popro2_lte with (max_k y hi0)
    | H: SearchTree_half_out ?lo0 ?l ?hi0,
      H1: SearchTree' ?k (T _ _ _ _ _ _ ) ?hi,
      H2: SearchTree' ?k (T _ _ _ _ _ _ ) ?high,
      H3: SearchTree_half ?x ?l ?hi 
     |- SearchTree' (min_k ?x ?lo0) (complete_tree ?l ?r) (max_k (min_k ?hi ?high) ?hi0) 
     => eapply search_complete;eauto
    |  H: SearchTree_half_out ?lo0 ?l ?hi0,
      H1: SearchTree' ?k (T _ _ _ _ _ _ ) ?hi,
      H2: SearchTree' ?k (T _ _ _ _ _ _ ) ?high,
      H3: SearchTree_half ?x ?l ?hi 
     |- SearchTree' (min_k ?x ?lo0)  (complete_tree ?l ?r) _
     => eapply search_popro2_lte with  (max_k (min_k hi high) hi0) 
    |  H: SearchTree_half_out ?lo0 ?l ?hi0,
      H1: SearchTree' ?k (T _ _ _ _ _ _ ) ?hi,
      H2: SearchTree' ?k (T _ _ _ _ _ _ ) ?high,
      H3: SearchTree_half ?x ?l ?hi 
     |- SearchTree' _ (complete_tree ?l ?r) _  
     => eapply search_popro3_lte with (min_k x lo0)
     | |- min_k ?low ?lo0 <= min_k (max_k ?lo ?low) ?lo0 => eapply min_xz
     | |- max_k (min_k ?hi ?high) ?hi0 <= max_k ?high ?hi0 => eapply max_xz
     | |- min_k ?low ?lo0 <= max_k ?lo ?low=> eapply lte_trans with low
     | |- min_k ?hi ?high <= max_k ?high ?hi0 => eapply lte_trans with high
     end).
Qed.

Theorem delete_st':
forall lo hi k t,
 SearchTree' lo t hi -> SearchTree' lo (delete k t) hi.
Proof.
  intros.
  unfold delete.
  remember (delete_into_base_half k t ).
  destruct p.
  unfold delete_into_base_half in Heqp.
  remember (delete_with_no_balance k t).
  destruct p. destruct p.
  pose proof delete_st'_without_b _ _ _ _ _ _ _ H Heqp0.
  destruct H0.
  do 2 destruct H1. super_destruct H1.
  destruct c.
  +  destruct  l0.
    - simpl in Heqp. inversion Heqp;subst.
      apply makeBlack_st.
      simpl. stt2 10.
    - destruct h. repeat destruct p.
      simpl in Heqp. inversion Heqp;subst.
      apply makeBlack_st.
      eapply search_popro2_lte with (max_k x0 hi).
      eapply search_popro3_lte with (min_k x lo).
      eapply search_complete;eauto.
      TRM 2.
      TRM 2.
  +  apply makeBlack_st.
    eapply delete_st'_b_Black;eauto.
Qed.



(*Delete Abs*)

   Lemma complete_relate_lemma : 
    forall h lo hi tree tmap hmap cts,
     Forall P h ->
     SearchTree_half lo h hi ->
     SearchTree' lo tree hi ->
     Abs tree tmap -> Abs_half h hmap ->  (combine tmap hmap) =cts ->
      Abs  (complete_tree h tree) cts.
   Proof.
     intros.
     assert (Abs (complete_tree h tree) (combine tmap hmap)).
     { eapply complete_relate_pre; try eassumption. }
     rewrite H4 in H5.
     auto.
   Qed.
Lemma delete_relate_with_no_balance:
  forall k t cts b h co ,
   SearchTree t -> 
   Abs t cts -> (h, b, co) = delete_with_no_balance k t ->
            Abs  (complete_tree h b) (k_delete k cts).
Proof.
  intros.
  pose proof delete_with_no_balance_st  _ _ _ _ _ H  H1  as hbST.
  unfold delete_with_no_balance in H1.
  remember ( delete_split k default t nil) . destruct p.
  pose proof delete_relate_split _ _ _ _ _ H H0 Heqp.
  pose proof delete_split_st _ _ _ _ H Heqp.
  assert (exists x y, Abs r x /\ Abs_half l y ).
  { pose proof Abs_exist r. pose proof Abs_exist_h l.
    destruct H4, H5.
    exists x, x0. auto. }
  pose proof delete_split_tag_default _ _ _ _ H Heqp.
  destruct H3. destruct H3. super_destruct H3.
  destruct H4. destruct H4. destruct H4.
  assert (Abs (complete_tree l r) (combine x1 x2)).
 { eapply complete_relate_pre; try eassumption. }
  assert (k < x0). { tr. } clear H7.
  assert (x < k).  { tr. } clear H8.
  assert(cts = combine x1 x2).
        { eapply Abs_unique; try eassumption. }
  subst cts.
  
  unfold delete_root in H1.
  repeat (match goal with
    | H: (_ ) = match ?r with |Empty => _ | T _ _ _ _ _ _ => _ end
                       |- _ => destruct r
    | H: (h, b, co) = (_, _ ,_ ) |- _ => inversion H;subst
    | H: Abs Empty ?x  |- _ => inversion H;subst x 
    | H: (?l, Empty) = delete_split k default t nil |- _ => erewrite k_delete_not_in;try eassumption;
                                                           eapply delete_not_in;try eassumption;auto
    | H: SearchTree ?t, H1: Abs ?t ?cts, 
      H2: (?l, T _ _ ?k1 _ _ _ ) = 
      delete_split ?k _ _ _ |-  _ 
          => pose proof delete_in _ _ _ _ _ _ _ _ _ _ _ _ H H1 H2;subst k1;clear H2
    | H: Abs (T _ _ ?k _ _ _ ) _ |- Abs (complete_tree _ _ ) (k_delete ?k _ ) =>inversion H;subst;clear H
    | H: Forall P ?h,
       H1: SearchTree_half ?lo ?h ?hi,
       H2: Abs ?tree ?tmap,
       H3: Abs_half ?h ?hmap
       |- Abs (complete_tree ?h ?tree) ?cts 
       => eapply (complete_relate_lemma h lo hi tree tmap hmap cts);try eassumption; inversion H6;subst
    | H: Abs (T ?c ?l ?k ?v ?t ?r) ?cts
    |- Abs (complete_tree _ (T ?c ?l ?k ?v (Optt ?tag ?t) ?r)) _ 
    => pose proof tag_tree_abs (T c l k v t r) tag cts H as Htree; simpl in Htree
    | H: Abs (T ?c ?l ?k ?v (Optt ?tag ?t) ?r) (tag_update ?tag ?x),
       H1: SearchTree' ?lo (T ?c ?l ?k ?v ?t ?r) ?hi
       |- combine (tag_update ?tag ?x) ?y = 
            k_delete ?kk (combine (tag_update ?tag (v_update ?kk _ ?x)) ?y)
            => pose proof search_tag_tree_t lo (T c l k v t r) hi tag H1 as STH; simpl in STH;erewrite tag_v_update
    | |- combine _ ?y  = k_delete _ (combine _ ?y) => erewrite k_delete_combine
    | |- ?m =  k_delete ?k (v_update ?k ?v ?m) => symmetry; eapply k_delete_update
    | |- restriction _ _ => res_simpl
    | |- (forall _, _ -> _ -> False ) => res_intros
    | |- add_one _ _ _ => unfold add_one;eauto
    | |- ~ _ _ => res_intro
    | |- combine ?x ?z = combine ?y ?z => eapply combine_xyz
    | |- context [ combine _ relate_default] => rewrite combine_default
    | |- context [ combine relate_default ?m] => rewrite (combine_comm relate_default m);rewrite combine_default
    | |- context [tag_update _ relate_default] => erewrite tag_update_defaultmap
    | |- context [tag_update _ (v_update _ _ _ )] => erewrite tag_v_update
    | |- SearchTree' _ _ _ => stt 10
    | H:  SearchTree' _ (T _ ?l ?k _ _ ?r) _
     |- SearchTree' _ (T _ ?l ?k _ _ ?r) _ => inversion H;subst
    | |- _ < _ => tr 
  end).
  remember ( Up_split (minimum_split default (T c1 r2_1 k2 v1 t2 r2_2) nil)). destruct p.
  assert (exists c k v t ri, r = T c Empty k v t ri).
  { eapply up_split_pro; try eassumption.
   left; discriminate. apply Forall_nil. } 
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. subst .
  inversion H6;subst.
   assert ((l0, T x1 Empty x3 x4 x5 x6) = insert_split x3 default (T c1 r2_1 k2 v1 t2 r2_2) nil).
    { eapply up_mini_equi; try eassumption. discriminate. apply ST_nil; tr. reflexivity. }
  assert ( (x3 <? x0) = true /\ (k <? x3) = true).
  { eapply insert_k_st;try eassumption. apply ST_nil; tr. discriminate. }
  assert (exists x y : Key,
        SearchTree_half x l0 y /\ SearchTree' x ( T x1 Empty x3 x4 x5 x6) y /\ k <= x /\ y <= x0).
    { eapply insert_st_pro; try eassumption. apply ST_nil; tr. }
   destruct H12. destruct H12. destruct H12. super_destruct H13.
  assert (SearchTree' x3 (complete_tree l0 x6) x0).
  { 
    assert (SearchTree_half_out (min_k k k) l0 (max_k x0 x0)).
    { eapply insert_st_out; try eassumption. apply ST_nil; tr. apply ST_out_nil; tr. }
    rewrite min_self in H16. rewrite max_self in H16.
    inversion H13;subst.
    assert (Forall (fun x: Half_tree =>  x3 < snd ( fst (fst (fst x)))) l0).
    { eapply (minimum_up_halftree (T c1 r2_1 k2 v1 t2 r2_2)) ; try eassumption.
      apply Forall_nil. apply ST_nil; tr. reflexivity. }
    assert (SearchTree_half_out x3 l0 x0).
    { eapply halftree_false_key_st; try eassumption.
      eapply (minimum_up_halftree_false (T c1 r2_1 k2 v1 t2 r2_2)); try eassumption.
      apply Forall_nil.  apply ST_nil; tr. destruct H8;tr. }
    clear H17.
    assert (SearchTree_half x3 l0 x8).
    { pose proof search_popro _ _ _ H29.
      pose proof search_popro _ _ _ H30.
      eapply search_h_popro3; try eassumption. split; tr. }
    clear H12.
    assert (max_k x8 x0 = x0).
    { eapply max_lte;try eassumption. }
    rewrite <- H12.
    pose proof min_self x3.
    rewrite <- H23.
    eapply search_complete; try eassumption. }
  destruct H8.
  inversion H1;subst.
  rewrite complete_tree_app.
  rewrite complete_tree_true.
  pose proof Abs_T _ _ _ _ k v t0 c H18 H19.
  rewrite <- tag_v_update.
  erewrite k_delete_combine; [ | res_simpl| res_simpl| res_intros| split; tr| res_intro].
  eapply complete_relate_pre; try eassumption.
  eapply ST_T;try eassumption.  stt 3.
  erewrite k_delete_tag_update.
  erewrite k_delete_update; [ | res_simpl | res_intro].
  pose proof Abs_exist (T x1 Empty x3 x4 x5 x6). destruct H23.
  pose proof Abs_exist_h l0. destruct H24.
  assert ( Abs (complete_tree l0 (T x1 Empty x3 x4 x5 x6)) 
   (combine (tag_update default b0) relate_default)).
  { eapply (insert_relate_pre k x0 _ nil b0) ; try eassumption.
    apply Forall_nil. eapply ST_nil;tr. apply Abs_nil. }
  assert (Forall P l0).
  { eapply (insert_split_tag_default k x0 _ nil); try eassumption. apply Forall_nil.
    eapply ST_nil;tr. }
  assert (Abs (complete_tree l0 (T x1 Empty x3 x4 x5 x6)) (combine x9 x10)).
  { eapply (complete_relate_pre l0 x7 x8 (T x1 Empty x3 x4 x5 x6) x9 x10); try eassumption.
 }
  rewrite tag_update_default in H25. rewrite combine_default in H25.
  assert (b0 = (combine x9 x10)).
  { eapply Abs_unique; try eassumption. }
  subst b0. inversion H23;subst. inversion H35;subst.
   assert (x5 = default).
  { pose proof insert_split_tag_default_tree.
    assert (default_tag_tree (T x1 Empty x3 x4 x5 x6) \/ (T x1 Empty x3 x4 x5 x6)= Empty ).
    { eapply ( insert_split_tag_default_tree k x0); try eassumption. eapply ST_nil;tr. }
    destruct H29.
    simpl in H29. auto.
    discriminate. }
  subst x5. rewrite tag_update_default.
  rewrite (combine_comm  _ b). rewrite combine_default.
  inversion H13;subst. pose proof search_popro _ _ _ H38;clear H38.
  pose proof search_popro _ _ _ H39.
  rewrite (combine_comm _ x10).
  erewrite v_update_combine by first [ res_simpl | res_intros | res_intro ].
  assert (Abs (complete_tree l0 x6) (combine b x10)).
  { eapply complete_relate_pre; try eassumption. stt 3. }
  rewrite (combine_comm  x10 b).
  erewrite v_update_combine; [ | res_simpl | res_simpl | res_intros| res_intro].
  eapply Abs_T; try eassumption.
Qed.
Lemma caseTwo_abs :
  forall s h lo hi b l cts,
   SearchTree' lo (complete_tree_one s h) hi -> SearchTree_half lo l hi ->
     b = CaseTwo_sol s h ->
      Abs (complete_tree l (complete_tree_one s h)) cts ->
       Abs (complete_tree l b) cts.
Proof.
  intros.
  destruct h.
  repeat destruct p.
  unfold CaseTwo_sol in H1.
  destruct b0.
  - destruct r.
      subst. auto.
    destruct c0.
      subst. auto.
    destruct r1, r2.
    + subst. auto. simpl in  H2.
      eapply comple_equi_strong.
      apply H0.
      4 : apply H2.
      eapply caseTwo_st; try eassumption. reflexivity.
      apply H.
      eapply equiv_left.
      apply equiv_color.
    + subst. auto.
    + destruct c0.
       subst; auto.
       subst;auto.
    + destruct c0.
       subst; auto.
      destruct c1.
       subst; auto.
      subst. simpl in H2.
      eapply comple_equi_strong.
      apply H0.
      4: apply H2.
      eapply caseTwo_st; try eassumption. reflexivity.
      apply H.
      eapply equiv_left.
      apply equiv_color.
  - destruct r.
      subst; auto.
    destruct c0.
      subst; auto.
    destruct r1, r2.
    + subst. simpl in H2.
      eapply comple_equi_strong.
      apply H0.
      4: apply H2.
      eapply caseTwo_st; try eassumption. reflexivity.
      apply H.
      eapply equiv_right.
      apply equiv_color.
    + subst; auto.
    + destruct c0.
        subst; auto.
        subst; auto.
    + destruct c0.
        subst; auto.
      destruct c1.
        subst; auto.
      subst. simpl in H2.
      eapply comple_equi_strong.
      apply H0.
      4: apply H2.
      eapply caseTwo_st; try eassumption. reflexivity.
      apply H.
      eapply equiv_right.
      apply equiv_color.
Qed.
Lemma caseFour_abs :
  forall s h lo hi b l cts,
   SearchTree' lo (complete_tree_one s h) hi -> SearchTree_half lo l hi ->
     b = CaseFour_sol s h ->
      Abs (complete_tree l (complete_tree_one s h)) cts ->
       Abs (complete_tree l b) cts.
Proof.
  intros.
  unfold CaseFour_sol in H1.
  destruct h. repeat destruct p.
  destruct b0.
  - destruct r.
      subst; auto.
    destruct c0.
      subst; auto.
    destruct r1.
      subst; auto.
    destruct c0.
    + simpl in H2.
      eapply comple_equi_strong.
      apply H0.
      4: apply H2.
      eapply caseFour_st; try eassumption.
      apply H.
      subst.
      simpl in H.
      apply Rb_equiv_symm.
      eapply Rb_equiv_trans.
      eapply equiv_right_rotate; try eassumption.
      eapply Rb_equiv_trans with 
      (T Black (tag_tree_t t0 (makeBlack(T Red r1_1 k1 v1 t1 r1_2) )) k0
  (f v0 t0) t (T c (tag_tree_t t0 r2) k v default s)).
      eapply equiv_left. simpl. eapply equiv_color.
      eapply Rb_equiv_trans with 
      (T Black (tag_tree_t t0 (makeBlack (T Red r1_1 k1 v1 t1 r1_2))) k0
  (f v0 t0) t (T Black (tag_tree_t t0 r2) k v default s) ).
      eapply equiv_right. eapply equiv_color.
      eapply equiv_color.
    + subst; auto.
 - destruct r.
      subst; auto.
    destruct c0.
      subst; auto.
    destruct r2.
      subst; auto.
    destruct c0.
    + simpl in H2.
      eapply comple_equi_strong.
      apply H0.
      4: apply H2.
      eapply caseFour_st; try eassumption.
      apply H.
      subst.
      simpl in H.
      apply Rb_equiv_symm.
      eapply Rb_equiv_trans.
      eapply equiv_left_rotate; try eassumption.
      eapply Rb_equiv_trans with 
      (T Black (T Black s k v default (tag_tree_t t0 r1)) k0 
  (f v0 t0) t (tag_tree_t t0 (T Red r2_1 k1 v1 t1 r2_2))).
      eapply equiv_left.  eapply equiv_color.
      eapply Rb_equiv_trans with 
      (T Black (T Black s k v default (tag_tree_t t0 r1)) k0 
  (f v0 t0) t (tag_tree_t t0 (makeBlack (T Red r2_1 k1 v1 t1 r2_2))) ).
      eapply equiv_right. eapply equiv_color.
      eapply equiv_color.
    + subst; auto.
Qed.
Lemma caseThree_abs :
  forall s h lo hi b l cts,
   SearchTree' lo (complete_tree_one s h) hi -> SearchTree_half lo l hi ->
     b = CaseThree_sol s h ->
      Abs (complete_tree l (complete_tree_one s h)) cts ->
       Abs (complete_tree l b) cts.
Proof.
  intros.
  unfold CaseThree_sol in H1.
  destruct h. repeat destruct p.
  destruct b0.
  - destruct r.
      subst;auto.
    destruct c0.
      subst;auto.
    destruct r2.
      subst;auto.
    destruct c0.
     +  assert (SearchTree' lo
        (complete_tree_one s
           (true, c, k, v, t,
        T Black (T Red r1 k0 v0 default (tag_tree_t t1 r2_1)) k1 
         (f v1 t1) t0 (tag_tree_t t1 r2_2))) hi).
        { simpl in H. inversion H; subst. inversion H11 ;subst. inversion H13 ;subst.
          simpl.  eapply ST_T; try eassumption.
          eapply ST_T; try eassumption.
          eapply ST_T; try eassumption.
          eapply search_tag_tree_t; try eassumption.
          eapply search_tag_tree_t; try eassumption.
        }
        eapply (caseFour_abs s (true, c, k, v, t,
       T Black (T Red r1 k0 v0 default (tag_tree_t t1 r2_1)) k1 
         (f v1 t1) t0 (tag_tree_t t1 r2_2))); try eassumption.
        simpl. simpl in H2.
        eapply comple_equi_strong.
        apply H0.
        4: apply H2.
        auto.
        auto.
        eapply equiv_left.
        eapply Rb_equiv_symm.
        simpl in H.
        inversion H; subst.
        pose proof (equiv_left_rotate _ _ _ _ _ _ _ _ _ _ _ _ _ H12).
        eapply Rb_equiv_trans.
        apply H1.
        eapply Rb_equiv_trans with (T Black (T Black r1 k0 v0 default (tag_tree_t t1 r2_1)) k1 
  (f v1 t1) t0 (tag_tree_t t1 r2_2)) .
        eapply equiv_color.
        eapply equiv_left.
        eapply equiv_color.
    + subst;auto.
  - destruct r.
      subst;auto.
    destruct c0.
      subst;auto.
    destruct r1.
      subst;auto.
    destruct c0.
    +  assert ( SearchTree' lo
        (complete_tree_one s  (false, c, k, v, t,
       T Black (tag_tree_t t1 r1_1) k1 (f v1 t1) t0
         (T Red (tag_tree_t t1 r1_2) k0 v0 default r2))) hi).
       { simpl in H. inversion H; subst. inversion H12; subst. inversion H10;subst.
         eapply ST_T; try eassumption.
         eapply ST_T; try eassumption.
         eapply search_tag_tree_t; try eassumption.
         eapply ST_T; try eassumption.
         eapply search_tag_tree_t; try eassumption. }
       eapply caseFour_abs.
       apply H3. apply H0. apply H1.
       simpl.
       eapply comple_equi_strong.
       apply H0. 4: apply H2. apply H3. apply H.
       simpl.
       apply Rb_equiv_symm.
       apply equiv_right.
       simpl in H; inversion H; subst.
       eapply Rb_equiv_trans.
       eapply equiv_right_rotate; try eassumption.
       eapply Rb_equiv_trans with (T Black (tag_tree_t t1 r1_1) k1 (f v1 t1) t0
  (T Black (tag_tree_t t1 r1_2) k0 v0 default r2)).
       apply equiv_color.
       eapply equiv_right.
       apply equiv_color.
    +  subst; auto.
Qed.
Lemma caseTTF_abs :
  forall s h lo hi n b l cts,
   SearchTree' lo (complete_tree_one s h) hi -> SearchTree_half lo l hi ->
     (b, n ) = CaseTTF_sol s h false ->
      Abs (complete_tree l (complete_tree_one s h)) cts ->
       Abs (complete_tree l b) cts.
Proof.
  intros.
  destruct h.
  repeat destruct p.
  destruct b0.
  + destruct r.
     simpl in H1. inversion H1. subst. simpl in H2. auto.
    destruct c0.
     simpl in H1. inversion H1. subst. simpl in H2. auto.
    destruct r1, r2.
    - (*Case 2*)
      unfold CaseTTF_sol in H1.
      remember (CaseTwo_sol s  (true, c, k, v, t, T Black Empty k0 v0 t0 Empty)).
      inversion H1.
      pose proof caseTwo_st _ _ _ _ _ H Heqr.
      eapply caseTwo_abs; try eassumption.
    - destruct c0.
      * (*Case 3*)
        unfold CaseTTF_sol in H1.
        remember  (CaseThree_sol s
        (true, c, k, v, t, T Black Empty k0 v0 t0 (T Red r2_1 k1 v1 t1 r2_2))).
        inversion H1.
        pose proof caseThree_st _ _ _ _ _ H Heqr.
        eapply caseThree_abs; try eassumption.
      *
        simpl in H1. inversion H1. subst. simpl in H2. auto.
    - destruct c0.
      * (*Case 4*)
        unfold CaseTTF_sol in H1.
        remember (CaseFour_sol s
        (true, c, k, v, t, T Black (T Red r1_1 k1 v1 t1 r1_2) k0 v0 t0 Empty)).
        inversion H1.
        pose proof caseFour_st _ _ _ _ _ H Heqr.
        eapply caseFour_abs; try eassumption.
      * simpl in H1. inversion H1. subst.  auto.
    - destruct c0.
        (*Case 4*)
        unfold CaseTTF_sol in H1.
        remember (CaseFour_sol s
        (true, c, k, v, t,
        T Black (T Red r1_1 k1 v1 t1 r1_2) k0 v0 t0 (T c1 r2_1 k2 v2 t2 r2_2))).
        inversion H1.
        pose proof caseFour_st _ _ _ _ _ H Heqr.
        eapply caseFour_abs; try eassumption.
      destruct c1.
      * (*Case 3*)
        unfold CaseTTF_sol in H1.
        remember (CaseThree_sol s
        (true, c, k, v, t,
        T Black (T Black r1_1 k1 v1 t1 r1_2) k0 v0 t0
          (T Red r2_1 k2 v2 t2 r2_2))).
        inversion H1.
        pose proof caseThree_st _ _ _ _ _ H Heqr.
        eapply caseThree_abs; try eassumption.
      * (*Case 2*)
        unfold CaseTTF_sol in H1.
        remember (CaseTwo_sol s
        (true, c, k, v, t,
        T Black (T Black r1_1 k1 v1 t1 r1_2) k0 v0 t0
          (T Black r2_1 k2 v2 t2 r2_2))).
        inversion H1.
        pose proof caseTwo_st _ _ _ _ _ H Heqr.
        eapply caseTwo_abs; try eassumption.
  + destruct r.
     simpl in H1. inversion H1. subst. auto.
    destruct c0.
     simpl in H1. inversion H1. subst. auto.
    destruct r1, r2.
    - (*Case 2*)
      unfold CaseTTF_sol in H1.
      remember (CaseTwo_sol s (false, c, k, v, t, T Black Empty k0 v0 t0 Empty)).
      inversion H1.
      pose proof caseTwo_st _ _ _ _ _ H Heqr.
      eapply caseTwo_abs; try eassumption.
    - destruct c0.
      * (*Case 4*)
        unfold CaseTTF_sol in H1.
        remember (CaseFour_sol s
        (false, c, k, v, t,
        T Black Empty k0 v0 t0 (T Red r2_1 k1 v1 t1 r2_2))).
        inversion H1.
        pose proof caseFour_st _ _ _ _ _ H Heqr.
        eapply caseFour_abs; try eassumption.
      *
        simpl in H1. inversion H1. subst. auto.
    - destruct c0.
      * (*Case 3*)
        unfold CaseTTF_sol in H1.
        remember (CaseThree_sol s
        (false, c, k, v, t,
        T Black (T Red r1_1 k1 v1 t1 r1_2) k0 v0 t0 Empty)).
        inversion H1.
        pose proof caseThree_st _ _ _ _ _ H Heqr.
        eapply caseThree_abs; try eassumption.
      * simpl in H1. inversion H1. subst. auto.
    - destruct c1.
        (*Case 4*)
        { unfold CaseTTF_sol in H1.
        remember (CaseFour_sol s
            (false, c, k, v, t,
            T Black (T c0 r1_1 k1 v1 t1 r1_2) k0 v0 t0
              (T Red r2_1 k2 v2 t2 r2_2))).
        destruct c0.
         inversion H1.
        pose proof caseFour_st _ _ _ _ _ H Heqr.
        eapply caseFour_abs; try eassumption.
         inversion H1.
        pose proof caseFour_st _ _ _ _ _ H Heqr.
        eapply caseFour_abs; try eassumption. }
      destruct c0.
      * (*Case 3*)
        unfold CaseTTF_sol in H1.
        remember (CaseThree_sol s
        (false, c, k, v, t,
        T Black (T Red r1_1 k1 v1 t1 r1_2) k0 v0 t0
          (T Black r2_1 k2 v2 t2 r2_2))).
        inversion H1.
        pose proof caseThree_st _ _ _ _ _ H Heqr.
        eapply caseThree_abs; try eassumption.
      * (*Case 2*)
        unfold CaseTTF_sol in H1.
        remember (CaseTwo_sol s
        (false, c, k, v, t,
        T Black (T Black r1_1 k1 v1 t1 r1_2) k0 v0 t0
          (T Black r2_1 k2 v2 t2 r2_2))).
        inversion H1.
        pose proof caseTwo_st _ _ _ _ _ H Heqr.
        eapply caseTwo_abs; try eassumption.
Qed.
Lemma caseOne_abs :
  forall s h lo hi n b l cts,
   SearchTree' lo (complete_tree_one s h) hi -> SearchTree_half lo l hi ->
     (b, n ) = CaseOne_sol s h false ->
      Abs (complete_tree l (complete_tree_one s h)) cts ->
       Abs (complete_tree l b) cts.
Proof.
  intros.
  pose proof caseOne_st _ _ _ _ _ _ H H1.
  unfold CaseOne_sol in H1.
  destruct h. repeat destruct p.
  destruct b0.
  - destruct r.
      simpl in H1. inversion H1. subst. auto.
    destruct c0.
    + remember ( CaseTTF_sol s (true, Red, k, v, default, tag_tree_t t0 r2) false ).
      destruct p.
      destruct b0.
      * simpl in H. inversion H; subst. inversion H12; subst.
        pose proof search_popro _ _ _ H13.
        pose proof search_popro _ _ _ H14.
        pose proof search_popro _ _ _ H15.
        inversion H1.
        assert (SearchTree'  k0 (complete_tree_one s (true, Red, k, v, default, tag_tree_t t0 r2))
  hi).
        { eapply ST_T; try eassumption.
          eapply search_tag_tree_t; try eassumption. }
        assert (Abs  (complete_tree ((true, Black, k0, f v0 t0, t, tag_tree_t t0 r1) ::l) r) cts).
        { eapply caseTTF_abs; try eassumption.
          eapply ST_cons_true; try eassumption.
          tr. eapply search_tag_tree_t; try eassumption.
          right. reflexivity. tr.
          simpl. simpl in H2.
          eapply comple_equi_strong. apply H0. 4: apply H2.
          eapply ST_T; try eassumption.
          eapply search_tag_tree_t; try eassumption.
          auto.
          eapply Rb_equiv_symm.
          eapply Rb_equiv_trans.
          eapply equiv_right_rotate; try eassumption.
          eapply Rb_equiv_trans with (T Red (tag_tree_t t0 r1) k0 (f v0 t0) t
  (T Red (tag_tree_t t0 r2) k v default s)).
          eapply equiv_right. eapply equiv_color.
          apply equiv_color. }
        simpl in H10.
        auto.
     * 
       destruct r.
           pose proof caseTTF_notempty _ _ _ _ Heqp.
           contradiction.
          destruct c0.
            simpl in H. inversion H; subst. inversion H12; subst.
            pose proof search_popro _ _ _ H13.
            pose proof search_popro _ _ _ H14.
            pose proof search_popro _ _ _ H15.
            inversion H1.
            assert (SearchTree'  k0 (complete_tree_one s (true, Red, k, v, default, tag_tree_t t0 r2))
      hi).
            { eapply ST_T; try eassumption.
              eapply search_tag_tree_t; try eassumption. }
            remember  (T Red r3 k1 v1 t1 r4) as r.
            assert (Abs  (complete_tree ((true, Black, k0, f v0 t0, t, tag_tree_t t0 r1) ::l) r) cts).
            { 
              eapply caseTTF_abs; try eassumption.
              eapply ST_cons_true; try eassumption.
              tr. eapply search_tag_tree_t; try eassumption.
              right. reflexivity. tr.
              simpl. simpl in H2.
              eapply comple_equi_strong. apply H0. 4: apply H2.
              eapply ST_T; try eassumption.
              eapply search_tag_tree_t; try eassumption.
              auto.
              eapply Rb_equiv_symm.
              eapply Rb_equiv_trans.
              eapply equiv_right_rotate; try eassumption.
              eapply Rb_equiv_trans with (T Red (tag_tree_t t0 r1) k0 (f v0 t0) t
      (T Red (tag_tree_t t0 r2) k v default s)).
              eapply equiv_right. eapply equiv_color.
              apply equiv_color. }
            simpl in H10.
            subst r.
            assert (SearchTree' k0 (T Red r3 k1 v1 t1 r4) hi).
            { eapply caseTTF_st; [| apply Heqp].  auto. }
            eapply comple_equi_strong. apply H0. 4: apply H10.
            eapply ST_T; try eassumption.
            eapply search_tag_tree_t; try eassumption.
            assert (T Black  r3 k1 v1 t1 r4  = makeBlack (T Red r3 k1 v1 t1 r4)).
            reflexivity.
            rewrite H16.
            eapply makeBlack_st;try eassumption.
            eapply ST_T; try eassumption.
            eapply search_tag_tree_t; try eassumption.
            eapply equiv_right.
            apply equiv_color.
          
          simpl in H. inversion H; subst. inversion H12; subst.
          pose proof search_popro _ _ _ H13.
          pose proof search_popro _ _ _ H14.
          pose proof search_popro _ _ _ H15.
          
          assert (SearchTree'  k0 (complete_tree_one s (true, Red, k, v, default, tag_tree_t t0 r2))
    hi).
          { eapply ST_T; try eassumption.
            eapply search_tag_tree_t; try eassumption. }
          assert (Abs  (complete_tree ((true, Black, k0, f v0 t0, t, tag_tree_t t0 r1) ::l) (T Black r3 k1 v1 t1 r4)) cts).
          { eapply caseTTF_abs; try eassumption.
            eapply ST_cons_true; try eassumption.
            tr. eapply search_tag_tree_t; try eassumption.
            right. reflexivity. tr.
            simpl. simpl in H2.
            eapply comple_equi_strong. apply H0. 4: apply H2.
            eapply ST_T; try eassumption.
            eapply search_tag_tree_t; try eassumption.
            auto.
            eapply Rb_equiv_symm.
            eapply Rb_equiv_trans.
            eapply equiv_right_rotate; try eassumption.
            eapply Rb_equiv_trans with (T Red (tag_tree_t t0 r1) k0 (f v0 t0) t
    (T Red (tag_tree_t t0 r2) k v default s)).
            eapply equiv_right. eapply equiv_color.
            apply equiv_color. }
          simpl in H8.
          assert (complete_tree_one (T Black r3 k1 v1 t1 r4)  (true, Black, k0, f v0 t0, t, tag_tree_t t0 r1) =  (T Black (tag_tree_t t0 r1) k0 (f v0 t0) t (T Black r3 k1 v1 t1 r4))).
          reflexivity.
          rewrite <- H9 in H8.
          eapply caseTTF_abs.
          4: apply H8.
          2: apply H0.
          2: apply H1.
          simpl.
          eapply ST_T; try eassumption.
          eapply search_tag_tree_t ; try eassumption.
          eapply caseTTF_st; [ | apply Heqp].
          simpl.
          eapply ST_T; try eassumption.
          eapply search_tag_tree_t ; try eassumption.
    + simpl in H1. inversion H1. subst. auto.
 -
   destruct r.
     simpl in H1. inversion H1. subst. auto.
   destruct c0.
   + remember ( CaseTTF_sol s (false, Red, k, v, default, tag_tree_t t0 r1) false).
     destruct p.
     destruct b0.
     * simpl in H. inversion H; subst. inversion H13; subst.
        pose proof search_popro _ _ _ H12.
        pose proof search_popro _ _ _ H14.
        pose proof search_popro _ _ _ H15.
        inversion H1.
        assert (SearchTree'  lo (complete_tree_one s (false, Red, k, v, default, tag_tree_t t0 r1))
  k0).
        { eapply ST_T; try eassumption.
          eapply search_tag_tree_t; try eassumption. }
        assert (Abs  (complete_tree ((false, Black, k0, f v0 t0, t, tag_tree_t t0 r2) ::l) r) cts).
        { eapply caseTTF_abs; try eassumption.
          eapply ST_cons_false; try eassumption.
          eapply search_tag_tree_t; try eassumption.
          right. reflexivity. tr.
          simpl. simpl in H2.
          eapply comple_equi_strong. apply H0. 4: apply H2.
          eapply ST_T; try eassumption.
          eapply search_tag_tree_t; try eassumption.
          auto.
          eapply Rb_equiv_symm.
          eapply Rb_equiv_trans.
          eapply equiv_left_rotate; try eassumption.
          eapply Rb_equiv_trans with (T Red (T Red s k v default (tag_tree_t t0 r1)) k0 (f v0 t0) t
  (tag_tree_t t0 r2)).
          eapply equiv_left. eapply equiv_color.
          apply equiv_color. }
        simpl in H10.
        auto.
     * 
        destruct r.
           pose proof caseTTF_notempty _ _ _ _ Heqp.
           contradiction.
         destruct c0.
          simpl in H. inversion H; subst. inversion H13; subst.
          pose proof search_popro _ _ _ H12.
          pose proof search_popro _ _ _ H14.
          pose proof search_popro _ _ _ H15.
          inversion H1.
          assert (SearchTree'  lo (complete_tree_one s (false, Red, k, v, default, tag_tree_t t0 r1))
    k0).
          { eapply ST_T; try eassumption.
            eapply search_tag_tree_t; try eassumption. }
          assert (Abs  (complete_tree ((false, Black, k0, f v0 t0, t, tag_tree_t t0 r2) ::l) (T Red  r3 k1 v1 t1 r4)) cts).
          { eapply caseTTF_abs; try eassumption.
            eapply ST_cons_false; try eassumption.
            eapply search_tag_tree_t; try eassumption.
            right. reflexivity. tr.
            simpl. simpl in H2.
            eapply comple_equi_strong. apply H0. 4: apply H2.
            eapply ST_T; try eassumption.
            eapply search_tag_tree_t; try eassumption.
            auto.
            eapply Rb_equiv_symm.
            eapply Rb_equiv_trans.
            eapply equiv_left_rotate; try eassumption.
            eapply Rb_equiv_trans with (T Red (T Red s k v default (tag_tree_t t0 r1)) k0 (f v0 t0) t
    (tag_tree_t t0 r2)).
            eapply equiv_left. eapply equiv_color.
            apply equiv_color. }
            simpl in H10.
            assert (SearchTree' lo (T Red  r3 k1 v1 t1 r4) k0).
            { eapply caseTTF_st; [| apply Heqp].  auto. }
            eapply comple_equi_strong. apply H0. 4: apply H10.
            eapply ST_T; try eassumption.
            assert (T Black  r3 k1 v1 t1 r4  = makeBlack (T Red  r3 k1 v1 t1 r4)).
            reflexivity.
            rewrite H16.
            eapply makeBlack_st;try eassumption.
            eapply search_tag_tree_t; try eassumption.
            eapply ST_T; try eassumption.
            eapply search_tag_tree_t; try eassumption.
            eapply equiv_left.
            apply equiv_color.
          
        simpl in H. inversion H; subst. inversion H13; subst.
        pose proof search_popro _ _ _ H12.
        pose proof search_popro _ _ _ H14.
        pose proof search_popro _ _ _ H15.
        
        assert (SearchTree'  lo (complete_tree_one s (false, Red, k, v, default, tag_tree_t t0 r1))
  k0).
        { eapply ST_T; try eassumption.
          eapply search_tag_tree_t; try eassumption. }
        assert (Abs  (complete_tree ((false, Black, k0, f v0 t0, t, tag_tree_t t0 r2) ::l) (T Black  r3 k1 v1 t1 r4)) cts).
        { eapply caseTTF_abs; try eassumption.
          eapply ST_cons_false; try eassumption.
          eapply search_tag_tree_t; try eassumption.
          right. reflexivity. tr.
          simpl. simpl in H2.
          eapply comple_equi_strong. apply H0. 4: apply H2.
          eapply ST_T; try eassumption.
          eapply search_tag_tree_t; try eassumption.
          auto.
          eapply Rb_equiv_symm.
          eapply Rb_equiv_trans.
          eapply equiv_left_rotate; try eassumption.
          eapply Rb_equiv_trans with (T Red (T Red s k v default (tag_tree_t t0 r1)) k0 (f v0 t0) t
  (tag_tree_t t0 r2)).
          eapply equiv_left. eapply equiv_color.
          apply equiv_color. }
        simpl in H8.
        assert (complete_tree_one (T Black  r3 k1 v1 t1 r4) (false, Black, k0, f v0 t0, t, tag_tree_t t0 r2) =  (T Black (T Black r3 k1 v1 t1 r4) k0 (f v0 t0) t (tag_tree_t t0 r2)) ).
        reflexivity.
        rewrite <- H9 in H8.
        eapply caseTTF_abs.
        4: apply H8.
        2: apply H0.
        2: apply H1.
        simpl.
        eapply ST_T; try eassumption.
        2:  eapply search_tag_tree_t ; try eassumption.
        eapply caseTTF_st; [ | apply Heqp].
        simpl.
        eapply ST_T; try eassumption.
        eapply search_tag_tree_t ; try eassumption.
   + simpl in H1. inversion H1. subst. auto.
Qed.
Lemma delete_relate_balance :
 forall  l r c0 b h lo hi cts,
 SearchTree' lo r hi -> SearchTree_half lo l hi ->
  (b, h) = delete_balance r l c0  ->
     Abs (complete_tree l r) cts -> Abs (complete_tree h b) cts.
Proof.
  induction l.
  { intros.
    simpl in H2.
    destruct c0.
     simpl in H1. inversion H1; subst. simpl. auto.
     simpl in H1. inversion H1; subst. simpl. auto.
     }
  { intros.
    destruct a. repeat destruct p.
    destruct c0.
     simpl in H1. inversion H1;subst. auto.

       destruct r.
       + (*r是Empty*)
         destruct r0.
           { (*brother Empty*)
              unfold delete_balance in H1.
              inversion H1; subst.
              auto. }
           { destruct c0.
             { (*Case One*)
              unfold delete_balance in H1 at 1.
              remember ( CaseOne_sol Empty
          (b0, c, k, v, t, T Red r0_1 k0 v0 t0 r0_2) false ).
              destruct p.
              inversion H0; subst.
              
              
              assert (SearchTree' lo0 (complete_tree_one Empty
         (true, c, k, v, t, T Red r0_1 k0 v0 t0 r0_2) ) hi).
              { eapply ST_T; try eassumption.
                eapply ST_E; tr. }
              assert (Abs (complete_tree l (complete_tree_one Empty
         (true,  c, k, v, t, T Red r0_1 k0 v0 t0 r0_2))) cts).
              { simpl. simpl in H2. auto.
               }
              assert (SearchTree' lo0 r hi).
                 { eapply caseOne_st; try eassumption.
                  }
              assert (Abs (complete_tree l r) cts).
                 { eapply caseOne_abs; try eassumption.
                  }
              destruct b1.
               inversion H1. subst. auto.
               eapply IHl; try eassumption.
              
              assert (SearchTree' lo (complete_tree_one Empty
         (false, c, k, v, t, T Red r0_1 k0 v0 t0 r0_2) ) hi0).
                { eapply ST_T; try eassumption.
                  eapply ST_E; tr. }
                assert (Abs (complete_tree l (complete_tree_one  Empty
         (false,  c, k, v, t, T Red r0_1 k0 v0 t0 r0_2))) cts).
                { simpl.
                  simpl in H2.
                  auto. }
                assert (SearchTree' lo r hi0).
                 { eapply caseOne_st; try eassumption.
                  }
                assert (Abs (complete_tree l r) cts).
                 { eapply caseOne_abs; try eassumption.
                  }
                destruct b1.
                 inversion H1. subst. auto.
                 eapply IHl; try eassumption.
                }
             { (*Case TTF*)
                unfold delete_balance in H1 at 1.
                remember (CaseTTF_sol Empty (b0, c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) false).
                destruct p.
                inversion H0; subst.
                
                assert (SearchTree' lo0 (complete_tree_one Empty (true,  c, k, v, t, T Black r0_1 k0 v0 t0 r0_2)) hi).
                { eapply ST_T; try eassumption.
                  eapply ST_E; tr. }
                assert (Abs (complete_tree l (complete_tree_one Empty (true,  c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) )) cts).
                { simpl.
                  simpl in H2.
                  auto. }
                assert (SearchTree' lo0 r hi).
                 { eapply caseTTF_st; try eassumption.
                  }
                assert (Abs (complete_tree l r) cts).
                 { eapply caseTTF_abs; try eassumption.
                  }
                destruct b1.
                 inversion H1. subst. auto.
                 eapply IHl; try eassumption.
                 
                 assert (SearchTree' lo (complete_tree_one Empty (false,  c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) ) hi0).
                { eapply ST_T; try eassumption.
                  eapply ST_E; tr. }
                assert (Abs (complete_tree l (complete_tree_one Empty (false, c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) )) cts).
                { simpl.
                  simpl in H2.
                  auto. }
                assert (SearchTree' lo r hi0).
                 { eapply caseTTF_st; try eassumption.
                  }
                assert (Abs (complete_tree l r) cts).
                 { eapply caseTTF_abs; try eassumption.
                  }
                destruct b1.
                 inversion H1. subst. auto.
                 eapply IHl; try eassumption.
                  }
              }
       + destruct c0.
         * (*r为红色点  红 + 黑*)
           inversion H1;subst.
           pose proof makeBlack_abs (T Red r1 k0 v0 t0 r2).
           pose proof makeRed_abs (T Black r1 k0 v0 t0 r2).
           assert ((T Black r1  k0 v0 t0 r2) ~~ (T Red r1  k0 v0 t0 r2)).
          { split.
            apply H4.
            apply H3. }
           clear H3 H4.
           pose proof makeBlack_st (T Red r1  k0 v0 t0 r2) _ _ H.
           simpl in H3.
           eapply (comple_equi_strong _ _ _ _ (T Red r1  k0 v0 t0 r2)); try eassumption.
         * (*r为黑色点  黑 + 黑*)
           destruct r0.
           {  (*brother Empty*)
              unfold delete_balance in H1.
              inversion H1; subst.
              auto. }
           { destruct c0.
             { (*Case One*)
               unfold delete_balance in H1 at 1.
               remember ( CaseOne_sol (T Black r1 k0 v0 t0 r2)
          (b0, c, k, v, t, T Red r0_1 k1 v1 t1 r0_2) false ).
               destruct p.
               inversion H0; subst.
                
                assert (SearchTree' lo0 (complete_tree_one  (T Black r1 k0 v0 t0 r2)
          (true, c, k, v, t, T Red r0_1 k1 v1 t1 r0_2)) hi).
                { simpl.
                  eapply ST_T; try eassumption.
                  eapply search_popro3_lte; try eassumption. }
                assert (Abs (complete_tree l (complete_tree_one  (T Black r1 k0 v0 t0 r2)
          (true, c, k, v, t, T Red r0_1 k1 v1 t1 r0_2))) cts ).
                { simpl in H2.
                  simpl.
                  auto. }
                assert (SearchTree' lo0 r hi).
                 { eapply caseOne_st; try eassumption.
                  }
                assert (Abs (complete_tree l r) cts).
                 { eapply caseOne_abs; try eassumption.
                  }
                destruct b1.
                 inversion H1. subst. auto.
                 eapply IHl; try eassumption.
                
                assert (SearchTree' lo (complete_tree_one (T Black r1 k0 v0 t0 r2)
          (false, c, k, v, t, T Red r0_1 k1 v1 t1 r0_2)) hi0).
                { simpl.
                  eapply ST_T; try eassumption.
                  eapply search_popro2_lte; try eassumption. }
                assert (Abs (complete_tree l (complete_tree_one (T Black r1 k0 v0 t0 r2)
          (false, c, k, v, t, T Red r0_1 k1 v1 t1 r0_2))) cts ).
                { simpl in H2.
                  simpl.
                  auto. }
                assert (SearchTree' lo r hi0).
                 { eapply caseOne_st; try eassumption.
                  }
                assert (Abs (complete_tree l r) cts).
                 { eapply caseOne_abs; try eassumption.
                  }
                destruct b1.
                 inversion H1. subst. auto.
                 eapply IHl; try eassumption.
                  }
             { (*Case TTF*)
                unfold delete_balance in H1 at 1.
                remember ( CaseTTF_sol (T Black r1 k0 v0 t0 r2)
          (b0, c, k, v, t, T Black r0_1 k1 v1 t1 r0_2) false).
                destruct p.
                inversion H0; subst.
                
                assert (SearchTree' lo0 (complete_tree_one (T Black r1 k0 v0 t0 r2)
          (true, c, k, v, t, T Black r0_1 k1 v1 t1 r0_2)) hi).
                { simpl.
                  eapply ST_T; try eassumption.
                  eapply search_popro3_lte; try eassumption. }
                assert (Abs (complete_tree l (complete_tree_one (T Black r1 k0 v0 t0 r2)
          (true, c, k, v, t, T Black r0_1 k1 v1 t1 r0_2))) cts ).
                { simpl in H2.
                  simpl.
                  auto. }
                assert (SearchTree' lo0 r hi).
                 { eapply caseTTF_st; try eassumption.
                  }
                assert (Abs (complete_tree l r) cts).
                 { eapply caseTTF_abs; try eassumption.
                  }
                destruct b1.
                 inversion H1. subst. auto.
                 eapply IHl; try eassumption.
                
                assert (SearchTree' lo (complete_tree_one (T Black r1 k0 v0 t0 r2)
          (false, c, k, v, t, T Black r0_1 k1 v1 t1 r0_2)) hi0).
                { simpl.
                  eapply ST_T; try eassumption.
                  eapply search_popro2_lte; try eassumption. }
                assert (Abs (complete_tree l (complete_tree_one (T Black r1 k0 v0 t0 r2)
          (false, c, k, v, t, T Black r0_1 k1 v1 t1 r0_2))) cts ).
                { simpl in H2.
                  simpl.
                  auto. }
                assert (SearchTree' lo r hi0).
                 { eapply caseTTF_st; try eassumption.
                  }
                assert (Abs (complete_tree l r) cts).
                 { eapply caseTTF_abs; try eassumption.
                  }
                destruct b1.
                 inversion H1. subst. auto.
                 eapply IHl; try eassumption.
                  }
              }
}
Qed.

Lemma delete_relate_without_complete :
 forall k t cts b h,
   SearchTree t -> Abs t cts ->
    (b,h) = delete_into_base_half k t ->
            Abs  (complete_tree h b) (k_delete k cts).
Proof.
  intros.
  unfold delete_into_base_half in H1.
  remember (delete_with_no_balance k t).
  destruct p. destruct p.
  assert (Abs (complete_tree l r) (k_delete k cts)).
  { eapply (delete_relate_with_no_balance k t); try eassumption. }
  pose proof delete_with_no_balance_st _ _ _ _ _ H Heqp.
  destruct H3. destruct H3. destruct H3.
  eapply ( delete_relate_balance l r); try eassumption.
Qed.
Theorem delete_relate :
 forall k t cts,
    SearchTree t -> Abs t cts -> Abs  (delete k t) (k_delete k cts).
Proof.
  intros.
  unfold delete.
  remember (delete_into_base_half k t). destruct p.
  eapply makeBlack_abs; try eassumption.
  eapply delete_relate_without_complete; try eassumption.
Qed.


(*Delete RedBlack -------------------------------*)
  Lemma delete_root_rb_co_lemma1 : forall l l0 k v kt tl k0 v0 t0 tr,
  last_black l0 ->
    is_redblack_color_half l0 Black ->
      is_redblack_color tl Black ->
        is_redblack_color tr Black ->
        fst_black' l ->
         is_redblack_color_half l Black ->
           is_redblack_color_half
            (l0 ++ (true, Red, k, v, kt, T Black tl k0 v0 t0 tr)::l) Black.
  Proof.
    intros.
    revert l k v kt tl k0 v0 t0 tr H0 H H1 H2 H3 H4.
    induction l0.
    - intros.
      inversion H.
    - intros.
      simpl.
      inversion H0. 
      + subst.
        eapply IsRB_co_r_cons; try eassumption.
        inversion H7. subst.
        eapply isb_isr_half.
        discriminate.
        2: reflexivity.
        eapply IHl0; try eassumption.
        eapply isr_isb_half; try eassumption.
      + subst.
        eapply IsRB_co_b_cons; try eassumption.
        destruct l0.
        simpl.
        eapply IsRB_co_r_cons; try eassumption.
        destruct H3. eapply isb_isr_half; try eassumption.
        eapply IsRB_co_b; try eassumption.
        eapply IHl0; try eassumption.
  Qed.
  Lemma delete_root_rb_co_lemma2 : forall l l0 k v kt b,
    is_redblack_color_half_loose l0 Black ->
      is_redblack_color b Black ->
         is_redblack_color_half l Black ->
           is_redblack_color_half
            (l0 ++ (true, Black, k, v, kt, b)::l) Black.
  Proof.
    intros.
    revert l k v kt b H0 H H1.
    induction l0.
    - intros.
      simpl.
      eapply IsRB_co_b_cons; try eassumption.
    - intros.
      simpl.
      inversion H.
      + subst.
        eapply IsRB_co_r_cons; try eassumption.
        inversion H4. 
        * subst.
          simpl. eapply IsRB_co_b_cons; try eassumption.
        * subst.
          eapply isb_isr_half; [discriminate | | reflexivity].
          eapply IHl0; try eassumption.
          eapply isr_isb_half_loose; try eassumption.
      + subst.
        eapply IsRB_co_b_cons;  try eassumption.
        eapply IHl0; try eassumption.
  Qed.
Theorem delete_root_rb_co : forall lo hi r l h b c ,
 SearchTree' lo r hi -> SearchTree_half lo l hi ->
 is_redblack_color r Black -> is_redblack_color_half l Black ->
    (Red_tree r /\ fst_black' l \/ Black_tree r \/ r = Empty /\ l <> nil) ->
       (h, b, c) = delete_root r l ->
        (is_redblack_color b Black /\
            is_redblack_color_half h Black)  /\ (
            ( c = Red /\ (Red_tree b /\ fst_black' h \/ Black_tree b \/ b = Empty ) )\/
            ( c = Black  )).
Proof.
  intros.
  inversion H1.
  -  subst. simpl in H4. inversion H4; subst.
     split.
      split. apply IsRB_co_leaf. auto.
      left. split. reflexivity. right. right.
      super_destruct H3; [ inversion H3| inversion H3| auto].
  - subst.
    destruct tl , tr.
    + simpl in H4. inversion H4. subst.
      split.
      split. apply IsRB_co_leaf. auto.
      left. split. reflexivity. right. right.
      auto.
    + simpl in H4. inversion H4; subst.
      inversion H6. subst.
      split.
      split.  apply IsRB_co_b; try eassumption. auto.
      left. split. reflexivity. right. left.
      reflexivity.
    + simpl in H4. inversion H4. subst.
      inversion H5; subst.
      split.
      split.
      eapply IsRB_co_b; try eassumption.
      auto.
      left.  split. reflexivity. right. left.
      reflexivity.
    + simpl in H4.
      inversion H5. subst.
      inversion H6. subst.
      remember (  Up_split (minimum_split default (T Black tr1 k1 v0 t0 tr2) nil)).
      destruct p.
      
      remember (minimum_split default (T Black tr1 k1 v0 t0 tr2) nil) as l1.
      assert (last_black l1).
      { 
        eapply minimum_split_lastBlack; try eassumption. 
        left.
        split.
        reflexivity.
        auto. }
      destruct l1.
        contradiction.
      destruct h0. repeat destruct p.
      assert (b0 = false).
      { assert (Forall fst_false ((b0, c0, k2, v1, t1, r0) :: l1)).
        { inversion H; subst.
          eapply (minimum_split_ht_false (T Black tr1 k1 v0 t0 tr2) _ _ _ nil); try eassumption.
          apply Forall_nil.
          apply ST_nil.
          eapply search_popro; try eassumption.
         }
         inversion H8.
         simpl in H11.
         destruct b0.
          contradiction.
          reflexivity.
      }
      subst b0.
      simpl in Heqp. inversion Heqp. subst r. subst l0.
      unfold minimum_split in Heql1.
       remember  (general_split (fun _ : Key => true) (fun _ : Key => false) default
             (T Black tr1 k1 v0 t0 tr2) nil).
        destruct p. simpl in Heql1. subst l0.
      assert (r  = Empty).
      { eapply minimum_split_empty; try eassumption.
      }
      subst r.
      assert( ( is_redblack_color Empty Black /\ 
      is_redblack_color_half ((false, c0, k2, v1, t1, r0) :: l1) Black )
      /\
      (Red_tree Empty/\ fst_black' ((false, c0, k2, v1, t1, r0) :: l1)
         \/ Black_tree Empty
         \/ (Empty = Empty /\ ~ (( false, c0, k2, v1, t1, r0) :: l1) =nil))).
      { 
        eapply general_split_RB_co. 5: apply Heqp0.
        
        left. reflexivity.
        eapply isr_isb. apply H6.
        apply IsRB_co_nil.
        right. left. reflexivity . }
      destruct H8. destruct H8.
      destruct c0.
     * inversion H4.
      inversion H10; subst.
      super_destruct H3; [| inversion H3 | inversion H3].
      destruct l1.
          simpl in H7. inversion H7.
        assert (  last_black (h ::l1)).
        { destruct h. repeat destruct p.
          destruct c.
            simpl. simpl in H7. auto.
          simpl. simpl in H7. auto. }
        clear H7.
        remember (h::l1) as l0.
        split. split. eapply isr_isb; try eassumption.
        
        eapply delete_root_rb_co_lemma1; try eassumption.
        eapply isr_isb_half; try eassumption.
        
        left. split. auto. right.
        inversion H25.
         right. auto.
         left. reflexivity.
     * inversion H4.
       inversion H10; subst.
       super_destruct H3; [| inversion H3 | inversion H3].
         split. split.
           auto.
         destruct l1.
            simpl. unfold fst_black' in H11. destruct H11.
            eapply IsRB_co_r_cons; try eassumption. eapply isb_isr_half; try eassumption.
         
         assert (  last_black (h ::l1)).
        { destruct h. repeat destruct p.
          destruct c.
            simpl. simpl in H7. auto.
          simpl. simpl in H7. auto. }
        remember (h::l1) as l0.
        eapply delete_root_rb_co_lemma1; try eassumption.
        
        right. auto.
  - subst.
    destruct tl, tr.
    + simpl in H4. inversion H4. subst.
      split.
      split.
      apply IsRB_co_leaf.
      auto.
      right. auto.
    + simpl in H4. inversion H4; subst.
      split. 2: right; auto.
      inversion H6.
      *   subst. split.
      eapply IsRB_co_r; try eassumption.
      auto.
      *   subst. split.
      eapply IsRB_co_b; try eassumption.
      auto.
    + simpl in H4. inversion H4. subst.
      split. 2: right; auto.
      inversion H5.
      *   subst. split.
      eapply IsRB_co_r; try eassumption.
      auto.
      *   subst. split.
      eapply IsRB_co_b; try eassumption.
      auto.
    + simpl in H4.
    
      remember ( Up_split (minimum_split default (T c1 tr1 k1 v0 t0 tr2) nil) ).
      destruct p.
      
      remember (minimum_split default (T c1 tr1 k1 v0 t0 tr2) nil) as l1.
      
     assert (l1 <> nil).
      { pose proof minimum_split_notnil _ _ _ _ Heql1 as H8.
        destruct H8 as [ H8| [H8 H9] ].
        auto.
        inversion H8. }
      destruct l1.
        contradiction.
      destruct h0. repeat destruct p.
      assert (b0 = false).
      { assert (Forall fst_false ((b0, c2, k2, v1, t1, r0) :: l1)).
        { inversion H; subst.
          eapply (minimum_split_ht_false (T c1 tr1 k1 v0 t0 tr2) _ _ _ nil); try eassumption.
          apply Forall_nil.
          apply ST_nil.
          eapply search_popro; try eassumption.
         }
         inversion H8.
         simpl in H11.
         destruct b0.
          contradiction.
          reflexivity.
       }
      subst b0.
      simpl in Heqp. inversion Heqp. subst r. subst l0.
      unfold minimum_split in Heql1.
       remember  (general_split (fun _ : Key => true) (fun _ : Key => false) default
             (T c1 tr1 k1 v0 t0 tr2) nil).
        destruct p. simpl in Heql1. subst l0.
      assert (r  = Empty).
      { eapply minimum_split_empty; try eassumption.
      }
      subst r.
      
      destruct c1.
      * inversion H6;subst.
        assert ( is_redblack_color_half_loose ((false, c2, k2, v1, t1, r0) :: l1) Black).
        {
          assert( ( is_redblack_color Empty Black /\ 
      is_redblack_color_half_loose ((false, c2, k2, v1, t1, r0) :: l1) Black )
      /\
      (Red_tree Empty/\ fst_black ((false, c2, k2, v1, t1, r0) :: l1)
         \/ Black_tree Empty
         \/ (Empty = Empty /\ ~ ((false, c2, k2, v1, t1, r0) :: l1) =nil))).
         { eapply general_split_RB_co_loose. 
            5: apply Heqp0.
        
          left. reflexivity.
          apply H6.
          apply IsRB_co_nil_l.
          left. split. reflexivity . reflexivity.
           }
         destruct H8. destruct H8. auto.
         }
        destruct c2.
        {
          inversion H4. inversion H8;subst.
          split.
          { 
            split.
              eapply isr_isb; try eassumption.
            eapply delete_root_rb_co_lemma2; try eassumption.
            eapply isr_isb_half_loose; try eassumption.
          }
          { left. split. auto.
            right.
            inversion H21.
            right. reflexivity.
            left. reflexivity.
          }
        }
        { 
          inversion H4. inversion H8; subst.
          split.
          { 
            split.
              auto.
            eapply delete_root_rb_co_lemma2; try eassumption.
          }
          { right.  reflexivity.
          }
        }
      *
        inversion H6; subst.
        assert( ( is_redblack_color Empty Black /\ 
        is_redblack_color_half ( (false, c2, k2, v1, t1, r0) :: l1) Black )
        /\
        (Red_tree Empty/\ fst_black' ( (false, c2, k2, v1, t1, r0) :: l1)
           \/ Black_tree Empty
           \/ (Empty = Empty /\ ~ ( (false, c2, k2, v1, t1, r0) :: l1) =nil))).
        { 
          eapply general_split_RB_co. 5: apply Heqp0.
          left. reflexivity.
          apply H6.
          apply IsRB_co_nil.
          right. left. reflexivity . }
        destruct H8. destruct H8.
        destruct c2.
      { 
        inversion H4.
        inversion H10; subst.
        super_destruct H3; [inversion H3 | | inversion H3].
        split. split.
           eapply isr_isb; try eassumption.
        
        eapply delete_root_rb_co_lemma2; try eassumption.
        eapply rb_co_ori2loose; try eassumption.
        eapply isr_isb_half; try eassumption.
        
        left. split. reflexivity. right.
        inversion H23; subst.
         right. reflexivity.
         left. reflexivity.
      }
       { inversion H4.
         inversion H10; subst.
         super_destruct H3; [inversion H3 | | inversion H3].
          split. 2: right; auto.
          split.
          auto.
          
          eapply delete_root_rb_co_lemma2; try eassumption.
          eapply rb_co_ori2loose; try eassumption.
       }
Qed.
 Ltac inversion_co H :=
  match type of H with
  | is_redblack_color (T _ _ _ _ _ _ ) _ => inversion H;subst
  | _ =>idtac
  end.
Definition is_redblack_color_but_root (r : RBtree) : Prop :=
match r with
| Empty => True
| T _ l k v t r => is_redblack_color l Black   /\ is_redblack_color r Black
end.
      Lemma isrb_makeBlack_co: forall  s, 
       is_redblack_color_but_root s -> is_redblack_color (makeBlack s) Red.
      Proof.
        intros.
        destruct s.
        - simpl. apply IsRB_co_leaf.
        - simpl in H. destruct H.
          simpl. eapply IsRB_co_b;try eassumption.
      Qed.
      Lemma isrb_notroot_to_ori: forall s,
       is_redblack_color s Black -> is_redblack_color_but_root s.
      Proof.
        intros.
        inversion H.
        - reflexivity.
        - split. eapply isr_isb;try eassumption.  eapply isr_isb;try eassumption.
        - split. auto. auto.
      Qed.
  Lemma caseTwo_co: forall s b0 c1 k v t tl k1 v1 t1 tr l r ,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,c1,k,v,t, T Black tl k1 v1 t1 tr)::l) Black ->
      r = CaseTwo_sol s (b0,c1,k,v,t, T Black tl k1 v1 t1 tr) ->
       (tl = Empty /\ tr = Empty \/ Black_tree tl /\ Black_tree tr) ->
       (Red_tree r /\ is_redblack_color_but_root r /\ fst_black l) \/ 
       (Black_tree r /\ is_redblack_color r Black).
  Proof.
    intros.
    unfold CaseTwo_sol in H1.
    repeat (
     match goal with
     | H1: _ = (if ?x then _ else _) ,
       H : _ /\  _ \/ _ /\ _ |- _ => destruct x;super_destruct H
     | H : ?t = Empty |- _ => subst t
     | H : r = T ?c _ _ _ _ _, H0: is_redblack_color_half ((_,?c,_,_,_,_)::_) Black 
            |- _ => inversion H0;subst c
     | H: _ = match ?t with
             |Empty => _ | T _ _ _ _ _ _ => _ 
             end |- _  => destruct t
     | H:_ =  match ?c with
             |Red => _ | Black => _ 
             end |- _  => destruct c
     | H: Black_tree Empty |- _  => inversion H
     | H:_ = complete_tree_one _ _ |- _ => simpl in H
     | H: r = T Red _ _ _ _ _ |- _ => subst;left
     | H: r = T Black _ _ _ _ _ |- _ => subst;right
     | |- _ /\ _ /\ _ => split; try (reflexivity)
     | |- _ /\ _  => split; try (reflexivity)
     | |- is_redblack_color_but_root _ => split
     | |- is_redblack_color _ _ => rbco 6
     | H : is_redblack_color_half ?l Red |- fst_black ?l => inversion H;subst;reflexivity
     | H: is_redblack_color_half ((_, Red, _, _, _, _) :: ?l) _ |- fst_black ?l => inversion H;subst
    end
    ).
  Qed.
  Lemma caseFour_co: forall s b0 c1 k v t tl k1 v1 t1 tr l r ,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,c1,k,v,t, T Black tl k1 v1 t1 tr)::l) Black ->
      r = CaseFour_sol s (b0,c1,k,v,t, T Black tl k1 v1 t1 tr) ->
       (b0  = false /\ Red_tree tr \/ b0  = true /\ Red_tree tl) ->
       (Red_tree r /\ is_redblack_color_but_root r /\ fst_black l) \/ 
       (Black_tree r /\ is_redblack_color r Black).
  Proof.
   intros.
   super_destruct H2.
   - subst b0.
     destruct tr. inversion H3.
     inversion H3. subst c.
     simpl in H1.
     inversion H0.
     + subst. left. split. reflexivity. split;[ | inversion H5;subst;reflexivity].
       inversion H11;subst. inversion H10;subst.
       split.  eapply IsRB_co_b;try eassumption. eapply isrb_tagupdate;try eassumption.
       eapply IsRB_co_b;try eassumption. eapply isr_isb;try eassumption. eapply isr_isb;try eassumption.
     + subst. right. split. reflexivity.
       inversion H12;subst. inversion H9;subst.
        eapply IsRB_co_b;try eassumption.  eapply IsRB_co_b;try eassumption. eapply isrb_tagupdate;try eassumption.   eapply IsRB_co_b;try eassumption. eapply isr_isb;try eassumption. eapply isr_isb;try eassumption.
   - subst b0.
     destruct tl. inversion H3.
      inversion H3. subst c.
     simpl in H1.
     inversion H0.
     + subst. left. split. reflexivity. split;[ | inversion H5;subst;reflexivity].
       inversion H11;subst. inversion H9;subst.
       split.  eapply IsRB_co_b;try eassumption. eapply isr_isb;try eassumption. eapply isr_isb;try eassumption. eapply IsRB_co_b;try eassumption.  eapply isrb_tagupdate;try eassumption.
     + subst. right. split. reflexivity.
       inversion H12;subst. inversion H8;subst.
        eapply IsRB_co_b;try eassumption.  eapply IsRB_co_b;try eassumption.
         eapply isr_isb;try eassumption. eapply isr_isb;try eassumption.
        eapply IsRB_co_b;try eassumption. eapply isrb_tagupdate;try eassumption.
  Qed.
  Lemma caseThree_co: forall s b0 c1 k v t tl k1 v1 t1 tr l r ,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,c1,k,v,t, T Black tl k1 v1 t1 tr)::l) Black ->
      r = CaseThree_sol s (b0,c1,k,v,t, T Black tl k1 v1 t1 tr) ->
       (b0  = false /\ Red_tree tl /\ (Black_tree tr \/ tr =Empty) 
       \/ 
       b0  = true /\ Red_tree tr /\ (Black_tree tl \/ tl =Empty  )) ->
       (Red_tree r /\ is_redblack_color_but_root r /\ fst_black l) \/ 
       (Black_tree r /\ is_redblack_color r Black).
  Proof.
    intros.
    unfold CaseThree_sol in H1.
    repeat (
     match goal with
     | H1: _ = (if ?x then _ else _) ,
       H : _ /\  _ /\ (_ \/ _ ) \/ _ /\ _ /\ (_ \/ _ ) |- _ => super_destruct H; subst x
     | H: _ = match ?t with
             |Empty => _ | T _ _ _ _ _ _ => _ 
             end |- _  => destruct t
     | H:_ =  match ?c with
             |Red => _ | Black => _ 
             end |- _  => destruct c
     | H: Red_tree Empty |- _  => inversion H
     | H: Black_tree Empty |- _  => inversion H
     | H: Red_tree (T Black _ _ _ _ _ ) |- _ => inversion H
     | H: Black_tree (T Red _ _ _ _ _ ) |- _ => inversion H
     | H : r = CaseFour_sol ?s (?b, ?c,?k,?v,?t, T Black ?tl ?k1 ?v1 ?t1 ?tr) , 
       H0: is_redblack_color_half ((?b,?c,?k,?v,?t,_)::_) Black 
            |- _ =>   eapply (caseFour_co s b c k v t tl k1 v1 t1 tr);try eassumption;
                      inversion H0;subst;try (inversion_co H12);try (inversion_co H13)
     | |- is_redblack_color_half ((_, Red, _,_,_,_)::_) Black => eapply IsRB_co_r_cons;try eassumption
     | |- is_redblack_color_half ((_, Black, _,_,_,_)::_) _ => eapply IsRB_co_b_cons;try eassumption
     | |- is_redblack_color _ _ => rbco 10
     | |-  false = false /\ _ \/ _ /\ _ => left;split
     | |-  _ /\ _ \/ true = true /\ _ => right;split
    end; eauto
    ).
  Qed.
  Lemma caseTTF_co : forall s b0 c1 k v t tl k1 v1 t1 tr l r b,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,c1,k,v,t, T Black tl k1 v1 t1 tr)::l) Black ->
      (r, b) = CaseTTF_sol s (b0,c1,k,v,t, T Black tl k1 v1 t1 tr) false ->
       (Red_tree r /\ is_redblack_color_but_root r /\ fst_black l) \/ 
       (Black_tree r /\ is_redblack_color r Black).
  Proof.
     intros. 
     unfold CaseTTF_sol in H1.
     repeat (
     match goal with
     | H1: _ = (if ?x then _ else _) |- _ => destruct x
     | H: _ = match ?t with
             |Empty => _ | T _ _ _ _ _ _ => _ 
             end |- _  => destruct t
     | H : (?r, ?b)= (CaseTwo_sol ?s ?h, _ ) |- _ =>  remember (CaseTwo_sol s h);inversion H;subst r;eapply (caseTwo_co s);try eassumption
     | H : (?r, ?b)= (CaseThree_sol ?s ?h, _ ) |- _ =>  remember (CaseThree_sol s h);inversion H;subst r;eapply (caseThree_co s);try eassumption
     | H : (?r, ?b)= (CaseFour_sol ?s ?h, _ ) |- _ =>  remember (CaseFour_sol s h);inversion H;subst r;eapply (caseFour_co s);try eassumption
     | H: (?r, ?n)= (complete_tree_one ?s (?b,?c,?k,?v,?t,_), _ ),
       H0: is_redblack_color_half ((?b,?c,?k,?v,?t,_)::_) Black |- _ => simpl in H;inversion H;subst;inversion H0;subst
     | |- Empty = Empty /\ _ \/ _ /\ _ => left
     | |- (T _ _ _ _ _ _ = Empty)  /\ _ \/ _ /\ _ => right
     | |-  false = false /\ _ \/ _ /\ _ => left;split
     | |-  _ /\ _ \/ true = true /\ _ => right;split
     | |- _ /\ _ => split 
     | |- Black_tree (T Black _ _ _ _ _) \/ _ => left 
     | |- Red_tree (T Red _ _ _ _ _ ) /\ _ /\ _ \/ _ /\ _ => left;split
     | |- _ /\ _ /\ _ \/ Black_tree (T Black _ _ _ _ _ ) /\ _ => right;split
     | |- is_redblack_color_but_root _ => split
     | |- is_redblack_color _ _ => rbco 6
     | H : is_redblack_color_half ?l Red |- fst_black ?l => inversion H;subst
    end ; try (reflexivity); try (eauto) 
    ).
  Qed.
  Lemma caseTTF_co_left : forall s b0 c1 k v t tl k1 v1 t1 tr l r b,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,c1,k,v,t, T Black tl k1 v1 t1 tr)::l) Black ->
      (r, b) = CaseTTF_sol s (b0,c1,k,v,t, T Black tl k1 v1 t1 tr) false ->
       is_redblack_color_but_root r.
  Proof.
    intros.
    assert ((Red_tree r /\ is_redblack_color_but_root r /\ fst_black l) \/ 
       (Black_tree r /\ is_redblack_color r Black)).
    { eapply caseTTF_co;try eassumption. }
    super_destruct H2.
    auto.
    eapply isrb_notroot_to_ori;try eassumption.
  Qed.
  Lemma caseTTF_co_right : forall s b0 c1 k v t tl k1 v1 t1 tr l r b,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,c1,k,v,t, T Black tl k1 v1 t1 tr)::l) Black ->
      (r, b) = CaseTTF_sol s (b0,c1,k,v,t, T Black tl k1 v1 t1 tr) false -> 
       r = Empty \/ Red_tree r /\ fst_black l \/ Black_tree r.
  Proof.
    intros.
    assert ((Red_tree r /\ is_redblack_color_but_root r /\ fst_black l) \/ 
       (Black_tree r /\ is_redblack_color r Black)).
    { eapply caseTTF_co;try eassumption. }
    super_destruct H2.
    auto.
    auto.
  Qed.
  Lemma caseTTF_twice : forall r0 s b  k v t br r n bb kk vv tt bl l,
   (r0, false) = CaseTTF_sol s (b,Red,k,v,t,br) false ->
    Black_tree r0 ->
    (r, n) = CaseTTF_sol r0 (bb,Black,kk,vv,tt,bl) false ->
      is_redblack_color s Black ->
        is_redblack_color_half l Black ->
          is_redblack_color br Red ->
            is_redblack_color bl Red ->
              is_redblack_color r Black /\ Black_tree r.
  Proof.
    intros.
    destruct br.
    destruct b. inversion H. inversion H.
    destruct c.
    inversion H4.
    assert ((Red_tree r0 /\ is_redblack_color_but_root r0 /\ fst_black ((bb,Black,kk,vv,tt,bl)::l)) \/ 
       (Black_tree r0 /\ is_redblack_color r0 Black)).
    { eapply (caseTTF_co s );[apply H2| | apply H].
      eapply IsRB_co_r_cons;try eassumption.
      eapply IsRB_co_b_cons;try eassumption.
      eapply isr_isb;try eassumption. }
    destruct r0.
     super_destruct H6. inversion H6. inversion H6.
    destruct c.
     inversion H0.
    super_destruct H6. inversion H6.
    destruct bl.
    + unfold CaseTTF_sol in H1.
      repeat (
      match goal with
      | H: _ = if ?x then _ else _ |- _ =>destruct x
      | H: _ = (complete_tree_one _ _, true) |- _ => simpl in H; inversion H;subst
      | |- _ /\ _ => split
      | |- Black_tree (T Black _ _ _ _ _) => reflexivity
      | |- is_redblack_color _ _ => rbco 4
      end
    ).
    + destruct c.
      inversion H5.
      assert ((Red_tree r /\ is_redblack_color_but_root r /\ fst_black (l)) \/ 
       (Black_tree r /\ is_redblack_color r Black)).
     { eapply caseTTF_co;[apply H7| | apply H1].
       eapply IsRB_co_b_cons;try eassumption.
       eapply isr_isb;try eassumption. }
      destruct r.
       pose proof caseTTF_notempty _ _ _ _ H1;contradiction.
      destruct c.
      unfold CaseTTF_sol in H1.
      repeat (
      match goal with
      | H: _ = if ?x then _ else _ |- _ =>destruct x
      | H: _ = match ?t with |Empty => _ | T _ _ _ _ _ _ => _ end |- _ => destruct t
      end; try (inversion H1)
    ).
     super_destruct H8.
       inversion H8.
     split. eauto. reflexivity.
  Qed.
  Lemma caseTTF_co_true: forall r s b c k v t br l,
   (r, true) = CaseTTF_sol s (b,c,k,v,t,br) false ->
     s = Empty \/ Black_tree s ->
      is_redblack_color s Black ->
        is_redblack_color_half l Black ->
          is_redblack_color br Red ->
              is_redblack_color r Black.
  Proof.
    intros.
    destruct c.
   +  unfold CaseTTF_sol in H.
    repeat (
      match goal with
      | H: _ = if ?x then _ else _ |- _ =>destruct x
      | H: _ = match ?t with |Empty => _ | T _ _ _ _ _ _ => _ end |- _ => destruct t
      | H: (_, true) = (_ , false) |- _ => inversion H
      | H: is_redblack_color (T Red _ _ _ _ _ ) Red |- _ => inversion H
      | H: (?r, _ ) = (complete_tree_one _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: (?r, _ ) = (CaseTwo_sol _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: (?r, _ ) = (CaseThree_sol _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: (?r, _ ) = (CaseFour_sol _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: _ \/ _ |- _ => destruct H
      | H: ?s = Empty |- _ => subst s 
      | |- is_redblack_color _ _ => rbco 10
      end
    ).
   + unfold CaseTTF_sol in H.
    repeat (
      match goal with
      | H: _ = if ?x then _ else _ |- _ =>destruct x
      | H: _ = match ?t with |Empty => _ | T _ _ _ _ _ _ => _ end |- _ => destruct t
      | H: (_, true) = (_ , false) |- _ => inversion H
      | H: is_redblack_color (T Red _ _ _ _ _ ) Red |- _ => inversion H
      | H: (?r, _ ) = (complete_tree_one _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: (?r, _ ) = (CaseTwo_sol _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: (?r, _ ) = (CaseThree_sol _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: (?r, _ ) = (CaseFour_sol _ _, _) |- _ => simpl in H;inversion H;subst;inversion H3;subst
      | H: _ \/ _ |- _ => destruct H
      | H: ?s = Empty |- _ => subst s 
      | |- is_redblack_color _ _ => rbco 10
      end
    ).
  Qed.
  Lemma caseTTF_co_false: forall rl rk rv rt rr s b c k v t br l,
   (T Red rl rk rv rt rr, false) = CaseTTF_sol s (b,c,k,v,t,br) false ->
     s = Empty \/ Black_tree s ->
      is_redblack_color s Black ->
        is_redblack_color_half l Black ->
          is_redblack_color br Red ->
              is_redblack_color (T Black rl rk rv rt rr) Black.
  Proof.
    intros.
    destruct c.
    + unfold CaseTTF_sol in H.
    repeat (
      match goal with
      | H: _ = if ?x then _ else _ |- _ =>destruct x
      | H: _ = match ?t with |Empty => _ | T _ _ _ _ _ _ => _ end |- _ => destruct t
      | H: (_, true) = (_ , false) |- _ => inversion H
      | H: is_redblack_color (T Red _ _ _ _ _ ) Red |- _ => inversion H
      | H: (?r, _ ) = (complete_tree_one _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: (?r, _ ) = (CaseTwo_sol _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: (?r, _ ) = (CaseThree_sol _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: (?r, _ ) = (CaseFour_sol _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: _ \/ _ |- _ => destruct H
      | H: ?s = Empty |- _ => subst s 
      | |- is_redblack_color _ _ => rbco 10
      end
    ). 
    + unfold CaseTTF_sol in H.
    repeat (
      match goal with
      | H: _ = if ?x then _ else _ |- _ =>destruct x
      | H: _ = match ?t with |Empty => _ | T _ _ _ _ _ _ => _ end |- _ => destruct t
      | H: (_, true) = (_ , false) |- _ => inversion H
      | H: is_redblack_color (T Red _ _ _ _ _ ) Red |- _ => inversion H
      | H: (?r, _ ) = (complete_tree_one _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: (?r, _ ) = (CaseTwo_sol _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: (?r, _ ) = (CaseThree_sol _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: (?r, _ ) = (CaseFour_sol _ _, _) |- _ => simpl in H;inversion H3;subst;inversion H;subst
      | H: _ \/ _ |- _ => destruct H
      | H: ?s = Empty |- _ => subst s 
      | |- is_redblack_color _ _ => rbco 10
      end
    ).
  Qed.
  Lemma caseOne_co : forall s b0 k v t tl k1 v1 t1 tr l r b,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,Black ,k,v,t, T Red tl k1 v1 t1 tr)::l) Black ->
      (r, b) = CaseOne_sol s (b0,Black,k,v,t, T Red tl k1 v1 t1 tr) false ->
       s = Empty \/ Black_tree s ->
        is_redblack_color r Black /\ Black_tree r.
  Proof.
   intros.
   inversion H0. subst.
   inversion H11;subst.
   unfold CaseOne_sol in H1.
   remember (CaseTTF_sol s (true, Red, k, v, default, tag_tree_t t1 tr)
             false).
   remember ( CaseTTF_sol s (false, Red, k, v, default, tag_tree_t t1 tl) false).
   destruct p ,p0.
   repeat (match goal with
    | H : (?r,?n) = if ?x then _ else _ |- _ => destruct x
    | H: (?r, true ) = CaseTTF_sol ?s ?h _,
      H1: (_ , _ )= (complete_tree_one ?r _, _ ) |- _ => simpl in H1;inversion H1; subst
    | H : _ = match ?r with  |Empty => _ | T _ _ _ _ _ _ => _ end
                   |- _ => destruct r
    | H: (Empty, _) = CaseTTF_sol _ _ _ |- _ => 
              pose proof caseTTF_notempty _ _ _ _ H;contradiction 
    | H: (?r, false) = CaseTTF_sol ?s ?h _,
      H1: (_ , _ )= (complete_tree_one (makeBlack ?r) _, _ ) |- _ 
       => unfold complete_tree_one in H1;inversion H1; subst
    | H: is_redblack_color (T Red _ _ _ _ _ ) Red
          |- _ => inversion H
    | H0: (?r0, false) = CaseTTF_sol ?s (?b,Red,?k,?v,?t,tag_tree_t ?tt ?br) false,
      H1: (?r , ?n ) = CaseTTF_sol ?r0 ?h false ,
      H2: is_redblack_color_half ((_,_,?k,?v,_, _ ) :: ?l) _ 
          |- _ => eapply (caseTTF_twice r0 s b k v t (tag_tree_t tt br) r n);try eassumption
    | |- Black_tree (T Black _ _ _ _ _ ) => reflexivity
    | |- _ /\ _ => split
    | |- is_redblack_color (tag_tree_t _ _ ) _ => eapply isrb_tagupdate;try eassumption
    | H: is_redblack_color ?r Red |- is_redblack_color ?r Black 
                                               => eapply isr_isb;try eassumption
    | H: (?r, true) = CaseTTF_sol _ _ _ |- is_redblack_color (T Black _ _ _ _ ?r) _ 
                                                  => eapply IsRB_co_b
    | H: (?r, true) = CaseTTF_sol _ _ _ |- is_redblack_color (T Black ?r _ _ _ _) _ 
                                                  => eapply IsRB_co_b
    | H: (?r, true) = CaseTTF_sol _ _ _ |- is_redblack_color ?r _ => eapply caseTTF_co_true;try eassumption
    | H: ((T Red ?l ?k ?v ?t ?r), false) = CaseTTF_sol _ _ _ 
                      |- is_redblack_color (T Black _ _ _ _ (T Black ?l ?k ?v ?t ?r)) _ 
                                                  => eapply IsRB_co_b
    | H: ((T Red ?l ?k ?v ?t ?r), false) = CaseTTF_sol _ _ _ 
                      |- is_redblack_color (T Black (T Black ?l ?k ?v ?t ?r) _ _ _ _) _ 
                                                  => eapply IsRB_co_b
   | H: ((T Red ?l ?k ?v ?t ?r), false) = CaseTTF_sol _ _ _ 
                      |- is_redblack_color (T Black ?l ?k ?v ?t ?r) _ 
                                                  => eapply caseTTF_co_false;try eassumption  
   end
   ).
  Qed.
  Lemma caseOne_co_left : forall s b0 k v t tl k1 v1 t1 tr l r b,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,Black ,k,v,t, T Red tl k1 v1 t1 tr)::l) Black ->
      (r, b) = CaseOne_sol s (b0,Black,k,v,t, T Red tl k1 v1 t1 tr) false ->
       s = Empty \/ Black_tree s ->
        is_redblack_color r Black.
  Proof.
    intros.
    assert ( is_redblack_color r Black /\ Black_tree r).
    { eapply caseOne_co; try eassumption. }
    destruct H3. auto. 
  Qed.
  Lemma caseOne_co_right : forall s b0 k v t tl k1 v1 t1 tr l r b,
   is_redblack_color s Black ->
     is_redblack_color_half ((b0,Black ,k,v,t, T Red tl k1 v1 t1 tr)::l) Black ->
      (r, b) = CaseOne_sol s (b0,Black,k,v,t, T Red tl k1 v1 t1 tr) false ->
       s = Empty \/ Black_tree s ->
        Black_tree r.
  Proof.
    intros.
    assert ( is_redblack_color r Black /\ Black_tree r).
    { eapply caseOne_co; try eassumption. }
    destruct H3. auto. 
  Qed.
  Theorem delete_rb_balance_Red:
    forall  l s h b ,
    is_redblack_color_half l Black   ->
    is_redblack_color s Black -> 
     (Red_tree s /\ fst_black' l \/ Black_tree s \/ s = Empty) ->
     (b, h) = delete_balance s l Red
     -> is_redblack_color (makeBlack (complete_tree h b)) Red.
  Proof.
     intros.
     unfold delete_balance in H2.
     destruct l.
     - inversion H2;subst.
       simpl.
       eapply isrb_makeBlack_co.
       eapply isrb_notroot_to_ori;try eassumption.
     - inversion H2;subst.
       eapply complete_tree_co; try eassumption.
       super_destruct H1;auto.
       destruct H3.
       auto.
  Qed.
  Theorem delete_rb_balance_Black:
    forall  l s  h b ,
    is_redblack_color_half l Black   ->
    is_redblack_color_but_root s ->
     (b, h) = delete_balance s l Black
     -> is_redblack_color (makeBlack (complete_tree h b)) Red.
  Proof.
    intro.
    induction l.
    - intros.
      inversion H1;subst.
       eapply isrb_makeBlack_co;try eassumption.
    - intros.
      destruct a. repeat destruct p.
      unfold delete_balance in H1.
      remember (CaseOne_sol s (b0, c, k, v, t, r) false) as u.
      remember (CaseTTF_sol s (b0, c, k, v, t, r) false) as w.
      destruct u, w.
      repeat (match goal with 
        | H : _ = match ?r with
               |Empty =>  _ | T _ _ _ _ _ _ => _ end
               |- _ =>destruct r
        | H : _ = match ?c with
               |Red =>  _ | Black => _ end
               |- _ =>destruct c
        | H : (?b, ?h) = (_ , _ ) |- _ => inversion H;clear H;subst b h 
        | H: is_redblack_color_half ?l Black,
          H0 : is_redblack_color_but_root _
           |- is_redblack_color (makeBlack (complete_tree ?l _)) _ => destruct H0;eapply complete_tree_co;try eassumption
        | H: is_redblack_color_half ?l Red,
          H0 : is_redblack_color_but_root _
           |- is_redblack_color (makeBlack (complete_tree ?l _)) _ => destruct H0;eapply complete_tree_co;try eassumption
        | |- Empty = Empty \/ _ /\ _  \/ _ => left;auto
        | |- _  = Empty \/ _ /\ _  \/ Black_tree (T Black _ _ _ _ _ ) => right;right;reflexivity
        | H: _ = if ?x then _ else _ ,
          H1: is_redblack_color_half (_ :: l) Black |- _ => destruct x;inversion H1;subst
        | H: _ = ( fix delete_balance (s : RBtree) (h : list Half_tree) (ori_color : color) {struct h} : RBtree * list Half_tree :=  _ ) ?r l Black,
          H1: is_redblack_color_half l _ 
          |- _ => eapply (IHl r); try eassumption
        | H: (?r0, _ ) =
         CaseOne_sol ?s (?b, Black, ?k, ?v, ?t, T Red ?tl ?k1 ?v1 ?t1 ?tr) false 
          |- is_redblack_color ?r0 Black  => eapply (caseOne_co_left s b k v t tl k1 v1 t1 tr);try eassumption
        | H: (?r0,  _ ) =
         CaseOne_sol ?s (?b, Black, ?k, ?v, ?t, T Red ?tl ?k1 ?v1 ?t1 ?tr) false 
          |- _ \/ _ /\ _ \/ Black_tree ?r0 => right;right;eapply (caseOne_co_right s b k v t tl k1 v1 t1 tr);try eassumption
        | H : (?r0, false) =
         CaseOne_sol ?s (?b, Black, ?k, ?v, ?t, T Red ?tl ?k1 ?v1 ?t1 ?tr) false 
          |- is_redblack_color_but_root ?r0 
              => eapply isrb_notroot_to_ori
        | H:  (?r, true) = CaseTTF_sol ?s (?b,?c,?k,?v,?t,?br) false
            |- is_redblack_color ?r Black
              => eapply (caseTTF_co_true r s b c k v t br l);try eassumption
        | H: (?r, _ ) = CaseTTF_sol ?s (?b,?c,?k,?v,?t, T Black ?tl ?k1 ?v1 ?t1 ?tr) false
         |- is_redblack_color_but_root ?r
           => eapply (caseTTF_co_left s b c k v t tl k1 v1 t1 tr ); try eassumption
        | H: (?r, _ ) = CaseTTF_sol ?s (?b,?c,?k,?v,?t, T Black ?tl ?k1 ?v1 ?t1 ?tr) false
         |- ?r = Empty \/ Red_tree ?r /\ fst_black _ \/ Black_tree ?r 
           => eapply (caseTTF_co_right s b c k v t tl k1 v1 t1 tr ); try eassumption
        | H: is_redblack_color (T Red _ _ _ _ _ ) Red |- _ => inversion H
        | |- _ = Empty \/ Black_tree (T Black _ _ _ _ _ ) => right;reflexivity
        | |- is_redblack_color _ _  => rbco 6
        | |- is_redblack_color_half l Black => eapply isr_isb_half;try eassumption 
        | H: is_redblack_color_but_root (T Black ?s1 ?k1 ?v1 ?t1 ?s2)
          |- is_redblack_color (T Black ?s1 ?k1 ?v1 ?t1 ?s2) Black => destruct H;eapply IsRB_co_b;try eassumption
       end; eauto).
  Qed.
Theorem delete_is_redblack_co : forall k t s,
 SearchTree t -> 
  is_redblack t ->  s = delete k t -> is_redblack_color s Red.
Proof.
  intros.
  inversion H0.
  unfold delete in H1.
  remember (delete_into_base_half k t) .
  destruct p.
  unfold delete_into_base_half in Heqp.
  remember (delete_with_no_balance k t).
  repeat destruct p.
  unfold delete_with_no_balance in Heqp0.
  remember (delete_split k default t nil ).
  destruct p.
  destruct t.
  -  unfold delete_split in Heqp1. unfold insert_split in Heqp1. simpl in Heqp1.
     inversion Heqp1. subst.
     simpl in Heqp0. inversion Heqp0. subst. simpl in Heqp. inversion Heqp. subst.
     simpl. 
     auto.
  - assert ((T c0 t1 k0 v t2 t3)<> Empty).
    { discriminate. }
    pose proof delete_split_rb_co _ _ _ _ H4 H2 Heqp1.
    destruct H5.
    destruct H5.
    assert ( exists x  y,  SearchTree_half x l1 y /\ SearchTree' x r1 y /\ (k <? y = true /\ x <? k = true) ).
    { eapply delete_split_st; try eassumption.
    }
    destruct H8. destruct H8.
    super_destruct H8.
    pose proof delete_root_rb_co  _ _ _ _ _ _ _ H9 H8 H5 H7 H6 Heqp0.
    destruct H12. destruct H12.

    subst s.
    destruct H13.
    + destruct H1;subst c.
      eapply delete_rb_balance_Red; try eassumption.
    + subst c.
      eapply delete_rb_balance_Black;try eassumption.
      eapply isrb_notroot_to_ori;try eassumption.
Qed.
Lemma delete_co_with_nobalance: forall k t  l b,
  SearchTree t ->
    is_redblack t ->
       (l, b, Black) = delete_with_no_balance k t ->
           is_redblack_color_half l Black /\     is_redblack_color_but_root b .
Proof.
   intros.
   unfold delete_with_no_balance in H1.
   remember (delete_split k default t nil ).
   destruct p.
   destruct t.
  -  unfold delete_split in Heqp. unfold insert_split in Heqp. simpl in Heqp.
     inversion Heqp. subst. inversion H1.
  - assert ((T c t1 k0 v t2 t3)<> Empty).
    { discriminate. }
    destruct H0.
    pose proof delete_split_rb_co  _ _ _ _ H2 H0 Heqp.
    destruct H4.
    destruct H4.
    assert ( exists x  y,  SearchTree_half x l0 y /\ SearchTree' x r y /\ (k <? y = true /\ x <? k = true) ).
    { eapply delete_split_st; try eassumption.
    }
    destruct H7. destruct H7.
    super_destruct H7.
    pose proof delete_root_rb_co  _ _ _ _ _ _ _ H8 H7 H4 H6 H5 H1.
    destruct H11. destruct H11.
    split. auto.
    eapply isrb_notroot_to_ori; auto.
Qed.


Theorem delete_root_rb_dep : forall r l n d h b c lo hi,
 is_redblack_dep r n ->
   is_redblack_dep_half l d n ->
   SearchTree' lo r hi->
     (h, b, c) = delete_root r l ->
        (c = Red /\ (exists n',  is_redblack_dep b n' /\  is_redblack_dep_half h d n' )
        \/
        c = Black /\ (exists n',  is_redblack_dep b n' /\  is_redblack_dep_half h d (S n') ) ).
Proof.
  intros.
  unfold delete_root in H2.
  repeat (
  match goal with
  | H: _ = match ?r with 
           |Empty => _ | T _ _ _ _ _ _ => _ end
              |- _ => destruct r
  | H: _ =  ( let (restr, r0) := ?x in  _  )|- _ => remember x as p;destruct p
  | H: _ = (?h, ?b, Red ) ,
    H1: is_redblack_dep ?r ?n ,
    H2: SearchTree' _ ?r _ |- _  
       => inversion H;subst;clear H;inversion H1;subst;inversion H2;subst;left
  | H: _ = (?h, ?b, Black ),
    H1: is_redblack_dep ?r ?n,
    H2: SearchTree' _ ?r _ |- _  
       => inversion H;subst;clear H;inversion H1;subst;inversion H2;subst;right
  | H: _ = (_ , _ , ?c) |- _ => destruct c
  | H: (_ , Empty) = Up_split(minimum_split _ _ _) |- _ 
          =>  pose proof up_split_notempty _ _ _ _ _ _ _ _ H as h;contradiction
  | H: (_ , T _ (T _ _ _ _ _ _ ) _ _ _ _ ) = Up_split(minimum_split _ _ _) |- _ 
          =>  pose proof  up_split_leftempty _ _ _ _ _ _ _ _ _ _ _ _ _  H as h;inversion h
  | |- Red = Red /\ _ => split
  | |- Black = Black /\ _  => split
  | H: is_redblack_dep Empty ?n |- _ =>inversion H;subst n
  | H: is_redblack_dep_half ?l ?d ?n |- 
             (exists n' : nat, is_redblack_dep _ n' /\ is_redblack_dep_half ?l d n')
                => exists n
  | H: is_redblack_dep_half ?l ?d ?n |- 
             (exists n' : nat, is_redblack_dep _ n' /\ is_redblack_dep_half ?l d (S n'))
                => exists (n - 1)
  |H: is_redblack_dep ?r  ?n |- 
             (exists n' : nat, is_redblack_dep ?r n' /\ is_redblack_dep_half _ d _)
                => exists n
  | H: (_ , T Red Empty _ _ _ ?r ) =
       Up_split (minimum_split _ ?tree _ ),
   H0: SearchTree' _ ?tree _ ,
   H1: is_redblack_dep ?tree ?n
       |- (exists n' : nat,
  is_redblack_dep ?r n' /\ is_redblack_dep_half _  d n')
    => pose proof up_split_dep_Red  _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H0 H as h;destruct h
  | H: (_ , T Black Empty _ _ _ ?r ) =
       Up_split (minimum_split _ ?tree _ ),
   H0: SearchTree' _ ?tree _ ,
   H1: is_redblack_dep ?tree ?n
       |- (exists n' : nat,
  is_redblack_dep ?r n' /\ is_redblack_dep_half _  d  (S n'))
    => pose proof up_split_dep_Black  _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H0 H as h;destruct h
  | |- _ /\ _ => split
  | |- is_redblack_dep _ (?n - 1) => rewrite Nat.sub_1_r;simpl
  | H: is_redblack_dep (T ?c ?l _ _ _ ?r) ?n |- is_redblack_dep (T ?c ?l _ _ _ ?r) ?n 
               => eapply isrb_changekvt_dep;try eassumption
  | |- is_redblack_dep_half (?l0 ++ (_, Red, _, _, _, _ ) :: ?l) _ _ => eapply isrb_dep_app_Red;try eassumption
  | |- is_redblack_dep_half (?l0 ++ (_, Black, _, _, _, _ ) :: ?l) _ _ => eapply isrb_dep_app_Black;try eassumption
  end; try (auto)
  ).
Qed.
Lemma delete_balance_dep_Red : forall r l d n b h,
  is_redblack_dep r n ->
    is_redblack_dep_half l d n ->
      (b, h) = delete_balance r l Red ->
        exists n' : nat, is_redblack_dep (makeBlack (complete_tree h b)) n'.
Proof.
  intros.
  assert ((b,h) = (r, l)).
  { rewrite H1.
    destruct l.
      auto.
      auto. }
  inversion H2;subst.
  eapply complete_makeBlack_dep; try eassumption.
Qed.

  Lemma  caseTTF_dep_true_Red : forall s b k v t bl bk bv bt br n r,
   is_redblack_dep s n ->
    is_redblack_dep (T Black bl bk bv bt br) (S n) ->
     (r, true) = CaseTTF_sol s (b,Red, k,v,t,T Black bl bk bv bt br) false ->
      is_redblack_dep r (S n).
  Proof.
    intros.
    unfold CaseTTF_sol in H1.
    repeat (match goal with
    | H : _ = if ?x then _ else _ |- _ => destruct x
    | H : _ = match ?r with
            |Empty => _ | T _ _ _ _ _ _ => _ end
             |- _ => destruct r
    | H : (_ , true) = (_, false) |- _ => inversion H
    | H: (_, _ ) = (complete_tree_one _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst
    | H : is_redblack_dep Empty ?n,
      H1 : is_redblack_dep (T Black _ _ _ _ _) ?n |- _ => inversion H;subst n;inversion H1
    | H: (_, _ ) = (CaseFour_sol _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst
    | H: (_, _ ) = (CaseThree_sol _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst;inversion H4;subst; inversion H9;subst
    | |-  is_redblack_dep (T _ _ _ _ _ _ ) _ => rbdep 6
    end).
  Qed.
  Lemma  caseTTF_dep_true_Black : forall s b k v t bl bk bv bt br n r,
   is_redblack_dep s n ->
    is_redblack_dep (T Black bl bk bv bt br) (S n) ->
     (r, true) = CaseTTF_sol s (b,Black, k,v,t,T Black bl bk bv bt br) false ->
      is_redblack_dep r (S (S n)).
  Proof.
    intros.
    unfold CaseTTF_sol in H1.
    repeat (match goal with
    | H : _ = if ?x then _ else _ |- _ => destruct x
    | H : _ = match ?r with
            |Empty => _ | T _ _ _ _ _ _ => _ end
             |- _ => destruct r
    | H : (_ , true) = (_, false) |- _ => inversion H
    | H: (_, _ ) = (complete_tree_one _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst
    | H : is_redblack_dep Empty ?n,
      H1 : is_redblack_dep (T Black _ _ _ _ _) ?n |- _ => inversion H;subst n;inversion H1
    | H: (_, _ ) = (CaseFour_sol _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst
    | H: (_, _ ) = (CaseThree_sol _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst;inversion H4;subst; inversion H9;subst
    | |-  is_redblack_dep (T _ _ _ _ _ _ ) _ => rbdep 6
    end).
  Qed.
  Lemma  caseTTF_dep_false_Red : forall s b k v t bl bk bv bt br n r,
   is_redblack_dep s n ->
    is_redblack_dep (T Black bl bk bv bt br) (S n) ->
     (r, false) = CaseTTF_sol s (b,Red, k,v,t,T Black bl bk bv bt br) false ->
      is_redblack_dep r n.
  Proof.
    intros.
    unfold CaseTTF_sol in H1.
    repeat (match goal with
    | H : _ = if ?x then _ else _ |- _ => destruct x
    | H : _ = match ?r with
            |Empty => _ | T _ _ _ _ _ _ => _ end
             |- _ => destruct r
    | H : (_ , false) = (_, true) |- _ => inversion H
    | H:  (_, _ ) = (CaseTwo_sol _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst
    | |-  is_redblack_dep (T _ _ _ _ _ _ ) _ => rbdep 6
    end).
  Qed.
  Lemma  caseTTF_dep_false_Black : forall s b k v t bl bk bv bt br n r,
   is_redblack_dep s n ->
    is_redblack_dep (T Black bl bk bv bt br) (S n) ->
     (r, false) = CaseTTF_sol s (b,Black, k,v,t,T Black bl bk bv bt br) false ->
      is_redblack_dep r (S n).
  Proof.
    intros.
    unfold CaseTTF_sol in H1.
    repeat (match goal with
    | H : _ = if ?x then _ else _ |- _ => destruct x
    | H : _ = match ?r with
            |Empty => _ | T _ _ _ _ _ _ => _ end
             |- _ => destruct r
    | H : (_ , false) = (_, true) |- _ => inversion H
    | H:  (_, _ ) = (CaseTwo_sol _ _ , _) |- _ => simpl in H;inversion H;subst;inversion H0;subst
    | |-  is_redblack_dep (T _ _ _ _ _ _ ) _ => rbdep 6
    end).
  Qed.
  Lemma  caseOne_dep_true_Black : forall s b k v t bl bk bv bt br n r,
   is_redblack_dep s n ->
    is_redblack_dep (T Red bl bk bv bt br) (S n) ->
    is_redblack_color (T Red bl bk bv bt br) Black ->
     (r, true) = CaseOne_sol s (b,Black, k,v,t,T Red bl bk bv bt br) false ->
      is_redblack_dep r (S (S n)).
  Proof.
    intros.
    unfold CaseOne_sol in H2.
    destruct br. 
      inversion H0. inversion H10.
    destruct c.
     inversion H1. inversion H9.
    
    destruct bl. 
      inversion H0. inversion H9.
    destruct c.
     inversion H1. inversion H5.
    
    remember ( CaseTTF_sol s
           (true, Red, k, v, default, tag_tree_t bt (T Black br1 k0 v0 t0 br2)) false) as u.
    remember ( CaseTTF_sol s
           (false, Red, k, v, default, tag_tree_t bt (T Black bl1 k1 v1 t1 bl2)) false) as w.
    destruct u, w.
    inversion H0;subst.
    
    repeat (match goal with
    | H : _ = if ?x then _ else _ |- _ => destruct x
    | H : _ = match ?r with
            |Empty => _ | T _ _ _ _ _ _ => _ end
             |- _ => destruct r
    | H : (_ , true) = (_, false) |- _ => inversion H
    | H: (_, _ ) = (complete_tree_one _ _ , _) |- _ => simpl in H;inversion H;subst;eapply IsRB_dep_b;try eassumption
    | H : is_redblack_dep Empty ?n,
      H1 : is_redblack_dep (T Black _ _ _ _ _) ?n |- _ => inversion H;subst n;inversion H1
    | H: (Empty, _ ) = CaseTTF_sol _ _ _ |- _ => pose proof caseTTF_notempty _ _ _ _ H;contradiction
    |H:  (?r, _) = CaseTTF_sol _
         (_, _ , _, _, _, tag_tree_t _ (T Black _ _ _ _ _)) false
         |- _  => unfold tag_tree_t in H
    |H:  (?r, true) =
       CaseTTF_sol s
         (?b, Red , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep ?r _ => eapply (caseTTF_dep_true_Red s b k v t bl bk bv bt br); try eassumption
    | H : (T Red ?ll ?kk ?vv ?tt ?rr , false) =
       CaseTTF_sol s
         (?b, Red , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep (T Black ?ll ?kk ?vv ?tt ?rr) _ => eapply isrb_dep_RtoB;eapply (caseTTF_dep_false_Red s b k v t bl bk bv bt br); try eassumption
    | H : (?r, true) =
       CaseTTF_sol ?s
         (?b, Black , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep ?r _ => eapply (caseTTF_dep_true_Black s b k v t bl bk bv bt br); try eassumption
    |H:  (?r, false) =
       CaseTTF_sol s
         (?b, Red , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep ?r _ => eapply (caseTTF_dep_false_Red s b k v t bl bk bv bt br); try eassumption
    | |- is_redblack_dep (T Black _ _ _ _ _ ) _  => rbdep 2 
    end).
    Qed.
    Lemma  caseOne_dep_false_Black : forall s b k v t bl bk bv bt br n r,
   is_redblack_dep s n ->
    is_redblack_dep (T Red bl bk bv bt br) (S n) ->
    is_redblack_color (T Red bl bk bv bt br) Black ->
     (r, false) = CaseOne_sol s (b,Black, k,v,t,T Red bl bk bv bt br) false ->
      is_redblack_dep r  (S n).
  Proof.
    intros.
    unfold CaseOne_sol in H2.
    destruct br. 
      inversion H0. inversion H10.
    destruct c.
     inversion H1. inversion H9.
    
    destruct bl. 
      inversion H0. inversion H9.
    destruct c.
     inversion H1. inversion H5.
    
    remember ( CaseTTF_sol s
           (true, Red, k, v, default, tag_tree_t bt (T Black br1 k0 v0 t0 br2)) false) as u.
    remember (  CaseTTF_sol s
           (false, Red, k, v, default, tag_tree_t bt (T Black bl1 k1 v1 t1 bl2)) false) as w.
    destruct u, w.
    inversion H0;subst.
    
    repeat (match goal with
    | H : _ = if ?x then _ else _ |- _ => destruct x
    | H : _ = match ?r with
            |Empty => _ | T _ _ _ _ _ _ => _ end
             |- _ => destruct r
    | H : (_ , false) = (_, true) |- _ => inversion H
    | H: (_, _ ) = (complete_tree_one _ _ , _) |- _ => simpl in H;inversion H;subst;eapply IsRB_dep_b;try eassumption
    | H : is_redblack_dep Empty ?n,
      H1 : is_redblack_dep (T Black _ _ _ _ _) ?n |- _ => inversion H;subst n;inversion H1
    | H: (Empty, _ ) = CaseTTF_sol _ _ _ |- _ => pose proof caseTTF_notempty _ _ _ _ H;contradiction
    |H:  (?r, _) = CaseTTF_sol _
         (_, _ , _, _, _, tag_tree_t _ (T Black _ _ _ _ _)) false
         |- _  => unfold tag_tree_t in H
    |H:  (?r, true) =
       CaseTTF_sol s
         (?b, Red , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep ?r _ => eapply (caseTTF_dep_true_Red s b k v t bl bk bv bt br); try eassumption
    | H : (T Red ?ll ?kk ?vv ?tt ?rr , false) =
       CaseTTF_sol s
         (?b, Red , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep (T Black ?ll ?kk ?vv ?tt ?rr) _ => eapply isrb_dep_RtoB;eapply (caseTTF_dep_false_Red s b k v t bl bk bv bt br); try eassumption
    | H : (?r, false) =
       CaseTTF_sol ?s
         (?b, Black , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep ?r _ => eapply (caseTTF_dep_false_Black s b k v t bl bk bv bt br); try eassumption
    |H:  (?r, false) =
       CaseTTF_sol s
         (?b, Red , ?k, ?v, ?t, T Black ?bl ?bk ?bv ?bt ?br) false
         |- is_redblack_dep ?r _ => eapply (caseTTF_dep_false_Red s b k v t bl bk bv bt br); try eassumption
    | |- is_redblack_dep (T Black _ _ _ _ _ ) _  => rbdep 2 
    end).
    Qed.
Lemma delete_balance_dep_Black : forall l r d n r0 l0,
  is_redblack_dep r n ->
    is_redblack_dep_half l d (S n) ->
    is_redblack_color_half l Black -> 
      (r0, l0) = delete_balance r l Black ->
        exists n' : nat, is_redblack_dep (makeBlack (complete_tree l0 r0)) n'.
Proof.
  intro.
  induction l.
  - intros.
    unfold delete_balance in H2. inversion H2;subst.
     pose proof IsRB_dep_nil  n; clear H0.
     eapply complete_makeBlack_dep ;try eassumption.
  - intros.
    destruct a.
    repeat destruct p.
    unfold delete_balance in H2.
    remember ( CaseOne_sol r (b, c, k, v, t, r1)false) as u.
    destruct u.
    remember (CaseTTF_sol r (b, c, k, v, t, r1)false) as w.
    destruct w.
      repeat (match goal with 
      | H : _ = match ?r with
             |Empty =>  _ | T _ _ _ _ _ _ => _ end
             |- _ =>destruct r
      | H : _ = match ?c with
             |Red =>  _ | Black => _ end
             |- _ =>destruct c
      | H : (?b, ?h) = (_ , _ ) |- _ => inversion H;clear H;subst b h 
      | H : is_redblack_dep Empty (S _) |- _ => inversion H;subst
      | H:  is_redblack_dep_half ((_, _, _, _, _, Empty) :: l) _ (S _) |- _=> inversion H;subst
      | H: _ = if ?x then _ else _ |- _ => destruct x
      | H: is_redblack_color (T Red _ _ _ _ _ ) Red |- _ => inversion H
      |H: is_redblack_color_half ((_,Red,_,_,_, T Red _ _ _ _ _ ) :: ?l ) _
        |- _  => inversion H;subst
      | H: _ = ( fix delete_balance (s : RBtree) (h : list Half_tree) (ori_color : color) {struct h} : RBtree * list Half_tree :=  _ ) ?r ?l Black,
       H1: is_redblack_dep_half (_  :: ?l) _ _
        |- _ => inversion H1;subst;clear H1
      | H: _ = ( fix delete_balance (s : RBtree) (h : list Half_tree) (ori_color : color) {struct h} : RBtree * list Half_tree :=  _ ) ?r l Black,
        H1: is_redblack_dep_half l _ (S _) 
      |- _ => eapply (IHl r); try eassumption
      | H: is_redblack_dep_half (_  :: ?l) _ _ 
        |- exists n' : nat, is_redblack_dep (makeBlack (complete_tree ?l _ )) n' 
          => inversion H;subst;clear H
      |H: is_redblack_dep_half ?l _ _
        |- exists n' : nat, is_redblack_dep (makeBlack (complete_tree ?l _ )) n' 
         =>  eapply (complete_makeBlack_dep l);try eassumption
      | H: is_redblack_dep (T Red ?l _ _ _ ?r) ?n 
        |- is_redblack_dep (T Black ?l _ _ _ ?r) (S ?n)
         => inversion H;subst;eapply IsRB_dep_b;try eassumption
      | H: (?r, true ) = CaseTTF_sol ?s ((_, Red, _,_,_, _ )) false |-  is_redblack_dep ?r _ 
        => eapply caseTTF_dep_true_Red;try eassumption
      | H: (?r, true) = CaseTTF_sol ?s ((_, Black, _,_,_, _ )) false |-  is_redblack_dep ?r _ 
        => eapply caseTTF_dep_true_Black;try eassumption
      | H: (?r, false ) = CaseTTF_sol ?s ((_, Red, _,_,_, _ )) false |-  is_redblack_dep ?r _ 
        => eapply caseTTF_dep_false_Red;try eassumption
      | H: (?r, false) = CaseTTF_sol ?s ((_, Black, _,_,_, _ )) false |- is_redblack_dep ?r _ 
        => eapply caseTTF_dep_false_Black;try eassumption
      | H: (?r, true) = CaseOne_sol ?s ((_, Black, _,_,_, _ )) false |-  is_redblack_dep ?r _ 
        => eapply caseOne_dep_true_Black;try eassumption
      | H: (?r, false) = CaseOne_sol ?s ((_, Black, _,_,_, _ )) false |- is_redblack_dep ?r _ 
        => eapply caseOne_dep_false_Black;try eassumption
      |H: is_redblack_color_half ((_ ) :: ?l ) Black 
        |- is_redblack_color_half ?l Black => inversion H;subst;clear H
      | H : is_redblack_color_half ?l Red |- is_redblack_color_half ?l Black => eapply isr_isb_half
      | H: is_redblack_color_half ((_ , _, _, _, _, ?r) :: l) Black
         |- is_redblack_color ?r Black => inversion H;subst; rbco 2
      end; try (eauto)).
Qed.
Theorem delete_is_redblack_dep : forall k t s,  
 SearchTree t -> 
 is_redblack t -> 
 s = delete k t ->(exists n',  is_redblack_dep s n').
Proof.
  intros.
  unfold delete in H1.
  remember (delete_into_base_half k t ).
  destruct p.
  unfold delete_into_base_half in Heqp.
  remember (delete_with_no_balance k t).
  repeat destruct p.
  unfold delete_with_no_balance in Heqp0.
  remember (delete_split k default t nil).
  destruct p.
  
  destruct H0.
  destruct H2.
  pose proof delete_split_rb_dep _ _ _ _ _ H2 Heqp1.
  destruct H3. destruct H3.

  inversion H;subst.
  assert ( exists x  y,  SearchTree_half x l1 y /\ SearchTree' x r1 y /\ (k <? y = true /\ x <? k = true) ).
    { eapply delete_split_st; try eassumption.
    }
  destruct H1. destruct H1.  super_destruct H1.
  
  assert (c = Red /\ (exists n',  is_redblack_dep r0 n' /\  is_redblack_dep_half l0 x n' )
        \/
        c = Black /\ (exists n',  is_redblack_dep r0 n' /\  is_redblack_dep_half l0 x (S n') ) ).
  { eapply delete_root_rb_dep;try eassumption. }
  
  super_destruct H9.
  - subst c.
    destruct H10. destruct H9.
    eapply delete_balance_dep_Red;try eassumption.
  - subst c.
    destruct H10. destruct H9.
    destruct t.
      inversion Heqp1;subst. inversion Heqp0;subst. 
    assert ((T c t1 k0 v t2 t3) <> Empty).
    { discriminate. }
    pose proof delete_split_rb_co _ _ _ _ H11 H0 Heqp1.
    destruct H12.
    destruct H12.
    
    pose proof delete_root_rb_co  _ _ _ _ _ _ _ H6 H1 H12 H14 H13 Heqp0.
    destruct H15. destruct H15.
    
    eapply delete_balance_dep_Black;try eassumption.
Qed.
Lemma delete_dep_with_nobalance: forall k t  l b,
  SearchTree t ->
    is_redblack t ->
       (l, b, Black) = delete_with_no_balance k t ->
           (exists x n',  is_redblack_dep b n' /\  is_redblack_dep_half l x (S n') ).
Proof.
  intros.
  destruct H0.
  destruct H2.
  
  unfold delete_with_no_balance in H1.
  remember (delete_split k default t nil).
  destruct p.
  
  pose proof delete_split_rb_dep _ _ _ _ _ H2 Heqp.
  destruct H3. destruct H3.
  
  exists x.
  inversion H;subst.
  assert ( exists x  y,  SearchTree_half x l0 y /\ SearchTree' x r y /\ (k <? y = true /\ x <? k = true) ).
    { eapply delete_split_st; try eassumption.
    }
  destruct H6. destruct H6.  super_destruct H6.
  remember Black as c.
  assert (c = Red /\ (exists n',  is_redblack_dep b n' /\  is_redblack_dep_half l x n' )
        \/
        c = Black /\ (exists n',  is_redblack_dep b n' /\  is_redblack_dep_half l x (S n') ) ).
  { eapply delete_root_rb_dep;try eassumption. }
  super_destruct H10.
- subst. inversion H10. 
- auto.
Qed.



Theorem delete_redblack : forall k t finaltree, 
SearchTree t -> is_redblack t ->
  finaltree =  delete k t -> is_redblack finaltree.
Proof.
  intros.
  split.
  eapply delete_is_redblack_co; try eassumption. 
  eapply delete_is_redblack_dep; try eassumption.
Qed.


End Section_Delete.