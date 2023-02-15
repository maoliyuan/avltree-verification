(*goal
1.搞清楚abs的意思以及用途
2.修正abs——half定义
3.is_AVLpartial是否需要改为prop形式
*)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z.

Definition Key: Type := Z.
Definition Value : Type := Z.
Definition Depth : Type := nat.

Record Node := newnode{
  key_of : Key;
  value_of : Value;
  depth_of : Depth
}.

Inductive tree : Type :=
| E: tree
| T : tree -> Node -> tree -> tree.

Inductive LeftOrRight :=
| L: LeftOrRight
| R: LeftOrRight.

Definition half_tree: Type := (LeftOrRight * Node * tree)%type.

Definition partial_tree: Type := list half_tree.

Fixpoint complete_tree  (l: partial_tree ) (b : tree) : tree :=
match l with
|nil => b
|(L, t, brother) :: l' => complete_tree l' (T brother t b) 
|(R, t, brother) :: l' => complete_tree l' (T b t brother)
end.
(*自底向上构建二叉搜索树，L为brother在b树的左侧*)
(* -------------       operations -------------------------------------
insert
delete
look_up *)

Fixpoint general_split_aux (lbool rbool : Node -> bool) (s :tree)  (b: partial_tree): 
 partial_tree * tree :=
 match s with
 |E => (b, E)
 |T l t' r =>
    if (lbool t') then 
        general_split_aux lbool rbool l ((R, t',r)::b)
      else if (rbool t') then 
        general_split_aux lbool rbool r ((L, t',l)::b)
      else 
       (b, s)
end.
(*generalsplit的过程是将一个完整的树拆分成一个partialtree的过程，节点满足左边的条件就继续拆分左子树，右子树挂着*)

(* lbool :  22 <? node.key 
rbool :  node.key         <? 22 *)
(*                                 此处为insert定义                                             *)
Definition general_split_simpl lbool rbool s := general_split_aux lbool rbool s nil.
Definition insert_split (x: Key)(s: tree) (b : partial_tree)  : list half_tree * tree := general_split_aux (fun k => x <? (key_of k)) (fun  k =>  (key_of k) <? x) s b.
(*找到插入的节点x应该处于的位置，x比当前节点小就往左边走，否则往右边走*)
Definition insert_root (x : Key) (v: Value)(s:tree) : tree :=
  match s with
  |E => T E (newnode x v (S O)) E
  |T l (newnode x' v' d) r=> T l (newnode x v d) r
  end.
Definition depth_of_tree s :=
match s with
| E => O
| T _ n _ => depth_of n
end.
Definition root_of_tree s:=
match s with
|E=> None 
|T _ n _=>Some n
end.
Definition LT_AVL a b :=
  match a with
    | None => true
    | Some n => key_of n <? key_of b
  end.
Definition GT_AVL a b :=
  match a with
    | None => true
    | Some n => key_of n >? key_of b
  end.
Definition reversedepth (s:nat*nat):=
match s with
|(a,b)=>(b,a)
end.   
(*需要检查这里的定义--------------------------------------------------------------------------------------------------------------*)
Definition left_rotate a oldroot y :=
 match oldroot with
  | None => E
  | Some oldroot => match y with 
                    |E => E
                    |T b newroot c => T (T a (newnode (key_of oldroot)(value_of oldroot)(S(depth_of_tree a))) b) (newnode (key_of  newroot)(value_of  newroot) (S (S (depth_of_tree a)))) c
                    end
 end. 
Definition right_rotate y oldroot a :=
  match oldroot with
  | None => E
  | Some oldroot =>
    match y with 
    |E => E
    |T b newroot c => T  b (newnode (key_of newroot)(value_of newroot) (S(S(depth_of_tree a)))) (T c (newnode (key_of  oldroot)(value_of  oldroot)(S(depth_of_tree a))) a)
    end 
   end. 
(*新定点高度永远为最外侧没修改的子树的高度+2*)
Definition is_balance_with_n (t1 :tree)(n:nat):=
match Nat.leb (depth_of_tree t1) (S n) with
|true=>match Nat.leb n (S(depth_of_tree t1)) with
        |true=>true
        |false=>false
        end
|false=>false
end.
Inductive isavltree : tree->Prop:=
|avlE : isavltree E
|avlT : forall Ltree n Rtree, isavltree Ltree->isavltree Rtree
            -> Nat.le (depth_of_tree Ltree) (S(depth_of_tree Rtree))->
            Nat.le (depth_of_tree Rtree) (S(depth_of_tree Ltree))->
            LT_AVL (root_of_tree Ltree) n = true ->
            GT_AVL (root_of_tree Rtree) n = true -> 
                isavltree (T Ltree n Rtree).
Fixpoint isavltree_bool (t:tree):bool:=
match t with
|E=>true
|T Lefttree n Righttree=>if Nat.leb (depth_of_tree Lefttree) (S (depth_of_tree Righttree))
                         then if Nat.leb (depth_of_tree Righttree) (S (depth_of_tree Lefttree))
                              then match isavltree_bool Lefttree with
                                   |true=>match isavltree_bool Righttree with
                                          |true=>true
                                          |false=>false
                                          end
                                   |false=>false
                                   end
                              else false
                         else false
end.

(* is_avl_partial中的n是split得到的subtree的高度 *)
Inductive is_avl_partial : partial_tree -> tree -> Prop :=
  | is_avl_partial_nil : forall t , isavltree t -> is_avl_partial nil t
  | is_avl_partial_consL : forall father brother l' t,
     isavltree (T brother father t) ->
     is_avl_partial l' (T brother father t) ->
     is_avl_partial ((L,father,brother) :: l') t
  | is_avl_partial_consR : forall father brother l' t,
     isavltree (T t father brother) ->
     is_avl_partial l' (T t father brother) ->
     is_avl_partial ((R,father,brother) :: l') t.

Definition true_insert_balance (LRf:LeftOrRight)(f:Node)(b st:tree):=
match LRf with
|L=>match st with
    |E=>E
    |T RL Rnode RR =>if Nat.leb(depth_of_tree RL) (depth_of_tree RR)
                     then left_rotate b (Some f) st
                     else left_rotate b (Some f) (right_rotate RL (root_of_tree st) RR)
                     end
|R=>match st with
    |E=>E
    |T LR Lnode LL =>if Nat.leb(depth_of_tree LR) (depth_of_tree LL)
                     then right_rotate st (Some f) b
                     else right_rotate (left_rotate LL (root_of_tree st) LR) (Some f) b
                     end
end.
(*改变高度只在普通的balance操作以及rotate操作进行的时候进行*)
(*修改balance为一层一层的*)
Fixpoint insert_balance  (l: partial_tree) (s: tree) : tree  :=
match l with
(*插入节点为根节点*)
|nil=>s
|(LRfather,father,brother)::l'=>
          if(Nat.leb (depth_of_tree s) (depth_of father))
          then if (Nat.ltb (depth_of_tree s) (depth_of father))
               then 
              match LRfather with
                   |L=>insert_balance l' (T brother father s)
                   |R=>insert_balance l' (T s father brother)
                   end
               else 
              match LRfather with
                   |L=>insert_balance l' (T brother (newnode (key_of father)(value_of father)(S(depth_of father))) s)
                   |R=>insert_balance l' (T s (newnode (key_of father)(value_of father) (S(depth_of father))) brother)
                   end
          else insert_balance l'  ( true_insert_balance LRfather father brother s )
end.
Definition insert' x v s :=let (h,b) := insert_split x s nil in (h, insert_root x v b).
(*没有进行balance操作*) 

Definition insert (k : Key)(v : Value)(t : tree) : tree :=
  let (l,s) := insert' k v t in insert_balance l s.

Definition not_empty (t:tree): bool:=
match t with
|E=>false
|T _ _ _=>true
end.

Definition getltree (t:tree): tree:=
match t with
|E=>E
|T l n r=>l
end.

Definition getrtree (t:tree): tree:=
match t with
|E=>E
|T l n r=>r
end.
(* Lemma split_prop : forall k s l t,t=snd(insert_split k s l)->
(not_empty t=true)->isavltree (T (getltree t) (newnode k (value_of (root_of_tree t)) (depth_of (root_of_tree t))) (getrtree t)).
 *)
Definition fit_tree x sub : Prop :=
  match sub with
    | E => True
    | T Ltree n Rtree => match (root_of_tree Ltree) , (root_of_tree Rtree) with
       | None , None => True
       | None , Some r => key_of r > x
       | Some l , None => key_of l < x
       | Some l , Some r => key_of l < x /\ key_of r > x
       end
end.


Lemma general_split_aux_prop : forall f1 f2 t l1 l2, 
  (fst (general_split_aux f1 f2 t (l1 ++ l2)), snd (general_split_aux f1 f2 t (l1 ++ l2))) =
  (fst (general_split_aux f1 f2 t l1) ++ l2, (snd (general_split_aux f1 f2 t l1))).
Proof.
intros. generalize dependent l1. generalize dependent l2.
induction t. 
- intros. auto.
- intros. destruct (f1 n) eqn:EL. 
+ unfold general_split_aux. rewrite EL. specialize (IHt1 l2 ((R, n, t2) :: l1) ). fold general_split_aux. apply IHt1.
+ unfold general_split_aux. destruct (f2 n) eqn:ER.
* rewrite EL. specialize (IHt2 l2 ((L, n, t1) :: l1) ). fold general_split_aux. apply IHt2.
* rewrite EL. auto.
Qed. 

Lemma fit_tree_split : forall k t , isavltree t -> fit_tree k (snd (insert_split k t [])).
Proof.
intros.
induction t.
- simpl. exact I.
- inversion H. apply IHt1 in H3. apply IHt2 in H4. unfold insert_split. destruct (k<?key_of n) eqn:EL. 
+ unfold general_split_aux. rewrite EL . pose proof(general_split_aux_prop (fun k0 : Node => k <? key_of k0)(fun k0 : Node => key_of k0 <? k) t1 [] [(R,n,t2)]). inversion H9. fold general_split_aux. (* rewrite H12. rewrite之后直接用insertsplit 是
的结论就好了 *) admit.
+ destruct (key_of n <? k) eqn:ER. 
* admit.
* inversion H. unfold general_split_aux. rewrite EL. rewrite ER. simpl snd. assert(Heq:(key_of n = k)). admit. simpl. destruct (root_of_tree t1) eqn:E1.
** destruct (root_of_tree t2) eqn:E2.
*** inversion H16. inversion H17. rewrite Heq in H19,H20. admit.
*** inversion H16. rewrite Heq in H19. admit. 
** destruct (root_of_tree t2) eqn:E2.
*** inversion H17. rewrite Heq in H19. admit.
*** exact I.
Admitted.

Lemma node_tree_height : forall l r n,isavltree (T l n r)->(Nat.lt(depth_of_tree l)  (depth_of n )) /\(Nat.lt(depth_of_tree r)(depth_of n )).
Proof.
intros.
Admitted.


Lemma insert_balance_prop : forall par sub , is_avl_partial par sub -> isavltree (insert_balance par sub).
Proof.
intros. generalize dependent sub.
induction par. 
- intros. simpl. inversion H. apply H0.
- intros. destruct a. destruct p. inversion H.
+ inversion H5. simpl. apply leb_correct in H12. apply leb_correct in H13. pose proof(node_tree_height t sub n). pose proof H5. apply H16 in H5. destruct H5. pose proof H18. rewrite<- Nat.ltb_lt in H18. pose proof H18. rewrite Nat.ltb_lt in H20. unfold lt in H20. apply le_S in H20. assert(Hle :(Nat.le (S (depth_of_tree sub)) (S (depth_of n)))->(Nat.le(depth_of_tree sub)(depth_of n))). admit. apply Hle in H20.
rewrite<- Nat.leb_le in H20. rewrite H20. rewrite<-Nat.ltb_lt in H19. rewrite H19. specialize (IHpar (T t n sub)). apply IHpar in H6. apply H6.
+ inversion H5. simpl. apply leb_correct in H12. apply leb_correct in H13. pose proof(node_tree_height sub t n). pose proof H5. apply H16 in H5. destruct H5. pose proof H5. rewrite<- Nat.ltb_lt in H5. pose proof H5. rewrite Nat.ltb_lt in H20. unfold lt in H20. apply le_S in H20. assert(Hle :(Nat.le (S (depth_of_tree sub)) (S (depth_of n)))->(Nat.le(depth_of_tree sub)(depth_of n))). admit. apply Hle in H20.
rewrite<- Nat.leb_le in H20. rewrite H20. rewrite<-Nat.ltb_lt in H19. rewrite H19. specialize (IHpar (T sub n t)). apply IHpar in H6. apply H6.
Admitted.

 
Lemma fit_tree_prop_need1 : forall x v d x' v' Ltree Rtree, 
isavltree
  (T Ltree {| key_of := x'; value_of := v'; depth_of := d |} Rtree) ->
fit_tree x (T Ltree {| key_of := x'; value_of := v'; depth_of := d |} Rtree) ->
isavltree
  (T Ltree {| key_of := x; value_of := v; depth_of := d |} Rtree).
Proof.
  intros. inversion H.
  apply avlT ; auto ; clear- H0; simpl in H0 ; destruct (root_of_tree Ltree) , (root_of_tree Rtree) ; simpl in * ; auto;
    try (apply Z.ltb_lt ; apply H0) ; try (apply Z.gtb_lt ; apply Z.gt_lt ; apply H0).
Qed.

Lemma insert_prop_need : forall par sub x v , is_avl_partial par sub -> fit_tree x sub ->
  isavltree (insert_balance par (insert_root x v sub)).
Proof.
  intros.
  destruct sub ; intros.
  - simpl.
  pose proof (insert_balance_prop par E). pose proof H.
   apply H1 in H. induction par.
   + simpl. apply avlT; auto.
   + destruct a. destruct p.
    admit.
  - simpl insert_root. destruct n.
    apply insert_balance_prop.
    inversion H ; subst.
    + apply is_avl_partial_nil. apply (fit_tree_prop_need1 _ _ _ _ _ _ _ H1 H0); auto.
    + apply is_avl_partial_consL ; auto.
      inversion H ; subst.
      * inversion H1 ; subst ; apply avlT ; auto.
        -- apply (fit_tree_prop_need1 _ _ _ _ _ _ _ H9 H0). 
        -- clear - H0. 
           simpl in H0. 
           admit.
      *   
Admitted.

Lemma complete_tree_prop : forall x s, 
  s = complete_tree (fst (insert_split x s nil))  (snd (insert_split x s nil)).
Proof.
intros.
induction s.
- auto.
- unfold insert_split. destruct (x<?key_of n) eqn:E1.
+ unfold general_split_aux. rewrite E1. assert(HR:[(R,n,s2)]=[]++[(R,n,s2)] ). auto. unfold half_tree. rewrite-> HR. fold general_split_aux. (*  rewrite->(general_split_aux_prop (fun k : Node => x <? key_of k) (fun k : Node => key_of k <? x) s1 [] [(R,n,s2)]). *) Admitted.
(* rewrite之后snd部分直接变成IHs1中的snd，第一部分也是这样，但多了一个halftree衔接在后面，直接对completetree进行展开，先替换s1在替换complete回去 *)
Lemma is_avl_partial_add_back : forall par sub par',
  is_avl_partial par sub -> 
  is_avl_partial par' (complete_tree par sub) ->
  is_avl_partial (par ++ par') sub.
Proof. 
intros.
generalize dependent sub.
induction par.
- simpl in *. auto.
- intros. inversion H. 
+ destruct a. destruct p. simpl in H0. specialize (IHpar (T brother father sub)). pose proof( IHpar  H5).  inversion H1.  rewrite<- H8 in H0. rewrite <-H9 in H0. rewrite <-H10 in H0. apply H6 in H0. assert ((((L, n, t0) :: par) ++ par')=((L, n, t0) :: (par ++ par'))). reflexivity. unfold half_tree. rewrite H7. rewrite <-H9. rewrite<- H10. (* inversion H0. 
* apply is_avl_partial_consL. apply H12. rewrite<-H11 in H0. apply H0. 
* apply is_avl_partial_consL. inversion H12.   *)
Admitted.


(* 可以得到性质：insert_balance par (insert_balance Half sub)就直接证完了 *)
Lemma insert_prop_need2 : forall x s , isavltree s -> is_avl_partial  (fst (insert_split x s nil))  (snd (insert_split x s nil)).
Proof.
intros.
induction H.
- simpl. apply is_avl_partial_nil. apply avlE.
- unfold insert_split in *. 
  destruct (x<?key_of n) eqn:C1 ; destruct (key_of n <? x) eqn : C2; 
  simpl ; try rewrite C1 ; try rewrite C2 ; simpl.
  + pose proof (general_split_aux_prop (fun k : Node => x <? key_of k) (fun k : Node => key_of k <? x) Ltree [] [(R,n,Rtree)]).
    unfold partial_tree in H5.
    inversion H5. 
    unfold half_tree at 2 4.
    rewrite -> H7,  H8.
    apply is_avl_partial_add_back ; auto. clear H5 H7 H8.
    
    pose proof (complete_tree_prop x Ltree).
    unfold insert_split in H5.
    rewrite <- H5. clear H5.
    apply is_avl_partial_consR ; auto.
    * apply avlT ; auto.
    * apply is_avl_partial_nil. apply avlT ; auto.
  + pose proof (general_split_aux_prop (fun k : Node => x <? key_of k) (fun k : Node => key_of k <? x) Ltree [] [(R,n,Rtree)]).
    unfold partial_tree in H5.
    inversion H5. 
    unfold half_tree at 2 4.
    rewrite -> H7,  H8.
    apply is_avl_partial_add_back ; auto. clear H5 H7 H8.
    
    pose proof (complete_tree_prop x Ltree).
    unfold insert_split in H5.
    rewrite <- H5. clear H5.
    apply is_avl_partial_consR ; auto.
    * apply avlT ; auto.
    * apply is_avl_partial_nil. apply avlT ; auto.
  + pose proof (general_split_aux_prop (fun k : Node => x <? key_of k) (fun k : Node => key_of k <? x) Rtree [] [(L,n,Ltree)]).
    unfold partial_tree in H5.
    inversion H5. 
    unfold half_tree at 2 4.
    rewrite -> H7,  H8.
    apply is_avl_partial_add_back ; auto. clear H5 H7 H8. 
    pose proof (complete_tree_prop x Rtree).
    unfold insert_split in H5.
    rewrite <- H5. clear H5.
    apply is_avl_partial_consL ; auto.
    * apply avlT ; auto.
    * apply is_avl_partial_nil. apply avlT ; auto.
  + apply is_avl_partial_nil. apply avlT ; auto.
Qed.

Theorem insert_avl_correct :forall t k v,isavltree t->isavltree (insert k v t).
Proof.
intros.
pose proof (insert_prop_need2 k t H).
revert dependent k.
induction H ; unfold insert in *; simpl in * ; intros.
- apply avlT ;  auto ; apply avlE.
- unfold insert' in *.
  rewrite (surjective_pairing (insert_split k (T Ltree n Rtree) [])).   
  simpl.  
  apply insert_prop_need ; auto.
  apply fit_tree_split ; auto.
  apply avlT ; auto.
Qed. 
      
(* Inductive insert (k: Key)(v:Value)(t:tree) : tree->Prop :=
|insert_intro : forall (l : list half_tree) (s : tree) (b : tree),
(l,s)=insert' k v t->b=insert_balance l s->insert k v t b.
 *)
Lemma derived_from_is_avl_partial : forall (a:half_tree)(l:partial_tree)(n:nat),
is_avl_partial (a :: l) (S n) = true->depth_of_tree( snd a )=n\/depth_of_tree( snd a )=S n\/depth_of_tree( snd a )=S(S n).
Proof.
intros. 
simpl in H. destruct a. destruct p. simpl. destruct (is_balance_with_n t (S n)) eqn:H'.
- unfold is_balance_with_n in H'. destruct (depth_of_tree t <=? S (S n))%nat eqn:H''.
+ destruct  (S n <=? S (depth_of_tree t))%nat eqn:H'''. 
* simpl in H'''. Print Nat.leb_le. apply Nat.leb_le in H''. apply Nat.leb_le in H'''.
inversion H''.
** right. right. reflexivity.
** inversion H1. 
*** right. left. reflexivity.
*** inversion H3.
**** left. reflexivity.
**** apply Nat.ltb_ge in H4. assert(~(m1<depth_of_tree t)%nat). apply Nat.ltb_nlt in H4.
apply H4. unfold lt in H6. rewrite H5 in H6. unfold not in H6. apply H6 in H'''. inversion H'''.
* simpl in H'''. inversion H'.
+ inversion H'.
- inversion H.
Qed.
Lemma derived_from_is_avl_partial' : forall (a:half_tree) (l:partial_tree)(n:nat),
is_avl_partial (a::l) n=true->Nat.le (depth_of_tree (snd a)) (S n).
Proof.
intros.
destruct n eqn:E.
- destruct a. destruct p. simpl. simpl in H. destruct (is_balance_with_n t 0) eqn:E'.
+ unfold is_balance_with_n  in E'. destruct (depth_of_tree t <=? 1)%nat eqn:E''. 
* rewrite Nat.leb_le in E''. apply E''.
* inversion E. inversion E'.
+ inversion H.
- pose proof(derived_from_is_avl_partial a l n0). apply H0 in H. destruct H.
+ rewrite H. apply le_S. apply le_S. apply le_n.
+ destruct H. rewrite H. apply le_S. apply le_n. rewrite H. apply le_n.
Qed. 
Lemma length_after_insert : forall (s:tree)(x:Key)(v:Value),
depth_of_tree (insert_root x v s)=depth_of_tree s\/depth_of_tree (insert_root x v s)=S(depth_of_tree s).
Proof.
intros.
destruct s.
- simpl. left. reflexivity.
- destruct n. simpl. left. reflexivity.
Qed.
Lemma is_partial_next : forall (l:partial_tree) (a:half_tree)(n:nat),
is_avl_partial (a::l) n=true->is_avl_partial l (S n)=true.
Proof.
intros.
Admitted.
(*以下证明(* (* (* (* balance操作可以保证在子树中插入节点不会影响整棵树的avl性质 *) *) *) *)*)
Theorem avlpartial_correctness :    forall (l:partial_tree) (s:tree)(s':tree)(x:Key) (v:Value)(n:nat), 
isavltree s->isavltree s'->depth_of_tree s'=n\/depth_of_tree s'=(S n)->depth_of_tree s=n
-> is_avl_partial l n=true->isavltree (insert_balance l s').
Proof.
intros. generalize dependent n. generalize dependent s. generalize dependent s'.
induction  l.
- intros. simpl. apply H0.
- intros. destruct a. destruct p. simpl. destruct (depth_of_tree s' <=? S (depth_of_tree t))%nat eqn:E.
+ destruct l0 eqn:E'. (*不需要平衡下的左右之分*)
* (*左侧*) specialize (IHl (T t n0 s')). assert(H4:isavltree(T t n0 s')).
 pose proof H3 as E4 . simpl in H3. destruct (is_balance_with_n t n) eqn:E1.
** destruct (isavltree_bool t) eqn:E2.
*** pose proof E2. apply isavltree_bool_prop_equal in E2. apply avlT. apply E2. apply H0. 
pose proof (derived_from_is_avl_partial' (L,n0,t),l,n). apply X in E4. simpl in E4. destruct H1.
**** rewrite<- H1 in E4. apply E4.
**** rewrite<- H1 in E4. apply le_S. apply E4.
**** apply Nat.leb_le in E. apply E.
*** inversion H3.
** inversion H3.
** specialize( IHl H4). specialize (IHl (T t n0 s)). assert(H5:isavltree(T t n0 s)).
pose proof H3 as E4 . simpl in H3. destruct (is_balance_with_n t n) eqn:E1.
*** destruct (isavltree_bool t) eqn:E2.
**** pose proof E2. apply isavltree_bool_prop_equal in E2. apply avlT. apply E2. apply H. 
pose proof (derived_from_is_avl_partial' (L,n0,t),l,n). apply X in E4. simpl in E4. destruct H1.
***** rewrite<- H2 in E4. apply E4.
***** rewrite<- H2 in E4. apply E4.
***** destruct H1. rewrite H2. rewrite <-H1. apply Nat.leb_le in E. apply E.
assert(ss': Nat.le (depth_of_tree s)(depth_of_tree s')). rewrite H1. rewrite H2. apply le_S. apply le_n.
apply Nat.leb_le in E. pose proof( Nat.le_trans (depth_of_tree s)(depth_of_tree s')(S (depth_of_tree t))).
apply H6. apply ss'. apply E.
**** inversion H3.
*** inversion H3.
*** specialize(IHl H5). 
specialize(IHl (S n)). 

* (*右侧*)

* admit.


+ (*需要平衡之下的平衡后的情况*)
 
 
(*                            此处为delete定义                               *)                                
Definition delete_split (x:Key) (s:tree ) (b:partial_tree):list half_tree*tree:= insert_split x s b.
Definition minimum_split (s: tree) (b: list half_tree):  list half_tree
:= fst (general_split_aux (fun k - => true) (fun k =>  false) s b).
(*fst作用为取出二元组中的第一个元素*)
(*minimum_split将位置改至最小值左下方的空树*)
Definition Up_split (b: list half_tree) : list half_tree * tree :=
match b with
| nil => (nil , E)
|(L, n, r)::l => (l , T r n E)
|(R ,n, r)::l => (l , T E n r)
end.
(*upsplit的作用是取出右子树最小元素*)
Definition delete_root (s: tree) (h : list half_tree): list half_tree * tree :=
match s with
|E => (h, E)
|T E n E => (h, E)
|T E n (T rightsonL rightson rightsonR) => (h, T rightsonL rightson rightsonR)
|T (T leftsonL leftson leftsonR) n E => (h, T leftsonL leftson leftsonR)
|T l n r => match Up_split (minimum_split r nil) with
                  |(restr, T E successor x) =>
                             ( ( restr ++ ( (L,  (newnode (key_of successor) (value_of successor) (depth_of n))    , l)::h )),x)
                  |(_ , _) => (h, E)
                  end
end.      
Fixpoint delete_balance  (l:partial_tree) (s:tree) : partial_tree*tree:=
match l with 
(*平衡的节点为根节点*)
|nil=>
    match s with
    |E=>(nil,E)
    |T Ltree n Rtree=>if Nat.ltb (S(depth_of_tree Ltree)) (depth_of_tree Rtree)
              then match Rtree with
              |E=>(l,s)
              |(T RL nR RR)=> if leb (depth_of_tree RL) (depth_of_tree  RR)
                              then (nil,left_rotate Ltree n Rtree)
                              else (nil,left_rotate  Ltree n (right_rotate RL nR RR) )
              end
              else if Nat.ltb (S(depth_of_tree Rtree))  (depth_of_tree Ltree)
              then match Ltree with
              |E=>(l,s)
              |(T LL nL LR)=>if leb (depth_of_tree LR) (depth_of_tree LL)
                              then (nil,right_rotate Ltree n Rtree)
                              else (nil,right_rotate  (left_rotate LL nL LR)  n Rtree)
              end
              else (l,s)
    end
(*平衡的节点不是根节点*)
|(LRfather,father,brother)::l'=>
           if leb (depth_of_tree brother) (S(depth_of_tree s))
                      then match LRfather with
                      |L=>delete_balance l' (T brother father s)
                      |R=>delete_balance l' (T s father brother)
                      end
                      else match LRfather with
                        |L=>
                              match brother with 
                              |E=>(l,s)
                              |(T Lofbrother nb Rofbrother) =>
                                      if Nat.ltb (depth_of_tree s)(depth_of_tree Lofbrother)
                                        then delete_balance l' (right_rotate brother father s)
                                        else delete_balance l'(  right_rotate    (left_rotate Lofbrother nb Rofbrother)  (father)(s))
                              end
                        |R=>
                              match brother with
                              |E=>(l,s)
                              |(T Lofbrother nb Rofbrother) =>
                                      if Nat.ltb (depth_of_tree s) (depth_of_tree Rofbrother)
                                        then delete_balance l' (left_rotate s father brother)
                                        else   delete_balance l' ( left_rotate s father  (right_rotate Lofbrother nb Rofbrother) )
                               end
                            end
               
end.           
Definition true_delete (x:Key)(s:tree) := let (h,s):= delete_split x s nil in  (delete_root s h).                                 
(*                              此处为lookup定义                                   *)
Fixpoint lookup (x:Key)(t:tree): option Value:=
match t with
|E=>None
|T lefttree n righttree=>if x<?(key_of n) then
                                          match (lookup x lefttree) with
                                          |None=>None
                                          |Some v'=>(Some  v')
                                          end
                                          else if (key_of n)<?x then
                                          match (lookup x righttree) with
                                          |None=>None
                                          |Some v'=>(Some  v')
                                          end
                                          else (Some (value_of n))
end.
                                        



(* Variable t: Node.
Check (key_of t).
Check (value_of t). *)


(*------------  证明AVL性质 --------------------------------------------
 SearchTree
 depth
 abs*)
Definition relate_map := Key -> option Value .
Definition v_update (k:Key)(v: Value )(m: relate_map):relate_map :=
 fun x =>  if  k =?x then Some v else m x.
(*相当于向原来的map中加入新的匹配，如果是新加入的点就单独考虑他对应的value值，否则按之前的map考虑*)
Definition relate_default : relate_map  := fun  x => None.
Definition combine (m1 m2: relate_map ) : relate_map :=
  fun x => match m1 x , m2 x with 
          |None, Some v => Some v
          |Some v, None => Some v
          |_ ,_ => None
          end.
Inductive Abs : tree -> relate_map -> Prop :=
|Abs_E : Abs E (relate_default)
|Abs_T: forall a b left right n ,
  Abs left a ->
  Abs right b ->
  Abs (T  left n right)  (v_update (key_of n) (value_of n) (combine  a b) ).          
Inductive Abs_half : list half_tree -> relate_map -> Prop :=
|Abs_nil : Abs_half nil relate_default
|Abs_cons : forall l lmap LOR n ktree tmap,
   Abs_half l lmap -> Abs ktree tmap -> Abs_half ((LOR,n,ktree)::l) (combine lmap (v_update (key_of n) (value_of n) tmap)).          
(*有问题*)          
          
(*searchtree *)
Definition optionZ_lt (ok1 ok2: option Key): Prop :=
  match ok1, ok2 with
  | Some k1, Some k2 => k1 < k2
  | _, _ => True
  end.
Inductive SearchTree : option Key -> tree -> option Key -> Prop :=
| ST_E : forall lo hi, optionZ_lt lo hi -> SearchTree lo E hi
| ST_T: forall lo l n r hi,
    SearchTree lo l (Some (key_of n)) ->
    SearchTree (Some (key_of n)) r hi ->
    SearchTree lo (T l n r) hi.
Theorem insert_avl : forall k v t finaltree, isavltree t ->insert k v t finaltree-> isavltree finaltree .
Proof.
intros.
inversion H0. subst.
Admitted.

Inductive SearchTree_half_in:
  option Key -> partial_tree -> option Key -> Prop :=
| ST_in_nil:
    forall lo hi, optionZ_lt lo hi -> SearchTree_half_in lo nil hi
| ST_in_cons_L:
    forall lo hi h l n,
      SearchTree_half_in lo h hi ->
      SearchTree lo l (Some (key_of n)) ->
      SearchTree_half_in (Some (key_of n)) ((L, n, l) :: h) hi
| ST_in_cons_R:
    forall lo hi h r n,
      SearchTree_half_in lo h hi ->
      SearchTree (Some (key_of n)) r hi ->
      SearchTree_half_in lo ((R, n, r) :: h) (Some (key_of n)).
Inductive SearchTree_half_out:
  option Key -> partial_tree -> option Key ->  Prop :=
| ST_out_nil:
    forall lo hi, optionZ_lt lo hi -> SearchTree_half_out lo nil hi 
| ST_out_cons_L:
    forall lo hi h l n,
      SearchTree_half_out lo h hi ->
      SearchTree lo l (Some (key_of n)) ->
      optionZ_lt (Some (key_of n)) hi ->
      SearchTree_half_out lo ((L, n, l) :: h) hi
| ST_out_cons_R:
    forall lo hi h r n,
      SearchTree_half_out lo h hi ->
      SearchTree (Some (key_of n)) r hi ->
      optionZ_lt lo (Some (key_of n)) ->
      SearchTree_half_out lo ((R, n, r) :: h) hi.

(*depth *)

(*abs*)




Definition relate_single (k: Key) (v: Value): relate_map :=
  fun x =>
    if Z.eq_dec x k then Some v else None.

Inductive Abs' : tree -> relate_map -> Prop :=
| Abs_E' : Abs' E relate_default
| Abs_T': forall l n r lm rm,
    Abs' l lm ->
    Abs' r rm ->
    Abs'
      (T l n r)
      (combine lm
         (combine (relate_single (key_of n) (value_of n)) rm)).
Inductive Abs_half : partial_tree -> relate_map -> Prop :=
| Abs_half_nil : Abs_half nil relate_default
| Abs_half_cons: forall LR n t h m1 m2,
    Abs t m1 ->
    Abs_half h m2 ->
    Abs_half
      ((LR, n, t) :: h)
      (combine m1
         (combine (relate_single (key_of n) (value_of n)) m2)).






