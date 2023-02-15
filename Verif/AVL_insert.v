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

Definition LRhalf (h:half_tree):LeftOrRight := fst (fst h).

Definition treeinhalf (h:half_tree) : tree := snd h.

Definition nodeinhalf (h:half_tree) : Node := snd (fst h).

Definition depth_of_tree s :=
match s with
| E => O
| T _ n _ => depth_of n
end.

Definition left_rotate a oldroot y :=
    match y with 
    |E => E
    |T b newroot c => T (T a (newnode (key_of oldroot)(value_of oldroot)(S(depth_of_tree a))) b) (newnode (key_of  newroot)(value_of  newroot) (S (S (depth_of_tree a)))) c
    end. 

Definition right_rotate y oldroot a :=
    match y with 
    |E => E
    |T b newroot c => T  b (newnode (key_of newroot)(value_of newroot) (S(S(depth_of_tree a)))) (T c (newnode (key_of  oldroot)(value_of  oldroot)(S(depth_of_tree a))) a) 
    end. 

Definition root_of_tree s:=
match s with
|E=>newnode (Z.of_nat O) (Z.of_nat O) O
|T _ n _=>n
end.

Definition rotate_balance (h:half_tree) (t:tree):=
match LRhalf h with
|L=>match t with
    |E=>E
    |T RL Rnode RR =>if Nat.leb(depth_of_tree RL) (depth_of_tree RR)
                     then left_rotate (treeinhalf h) (nodeinhalf h) t
                     else left_rotate (treeinhalf h) (nodeinhalf h) (right_rotate RL (root_of_tree t) RR)
                     end
|R=>match t with
    |E=>E
    |T LR Lnode LL =>if Nat.leb(depth_of_tree LR) (depth_of_tree LL)
                     then right_rotate t (nodeinhalf h) (treeinhalf h)
                     else right_rotate (left_rotate LL (root_of_tree t) LR) (nodeinhalf h) (treeinhalf h)
                     end
end.

Definition insert_balance (h:half_tree) (t:tree):=
match (Nat.leb (depth_of_tree (treeinhalf h)) (S(depth_of_tree t))) with
|true=>match (Nat.eqb (depth_of_tree (treeinhalf h)) (depth_of_tree t)) with
       |true=>match LRhalf h with
              |L=>T (treeinhalf h) (nodeinhalf h) t
              |R=>T t (nodeinhalf h) (treeinhalf h)
              end
       |false=>match LRhalf h with
              |L=> (T (treeinhalf h) (newnode (key_of (nodeinhalf h))(value_of (nodeinhalf h)) (S (depth_of (nodeinhalf h)))) t )
              |R=> (T t (newnode (key_of (nodeinhalf h))(value_of (nodeinhalf h)) (S (depth_of (nodeinhalf h)))) (treeinhalf h))
              end
       end
|false=>rotate_balance h t
end.

Inductive is_AVL : tree->Prop:=
|avlE : is_AVL E
|avlT : forall Ltree n Rtree, is_AVL Ltree->is_AVL Rtree
            -> Nat.le (depth_of_tree Ltree) (S(depth_of_tree Rtree))->  Nat.le (depth_of_tree Rtree) (S(depth_of_tree Ltree))
            -> Z.lt (key_of n)(key_of (root_of_tree Rtree))->Z.lt (key_of (root_of_tree Ltree)) (key_of n)
                ->is_AVL (T Ltree n Rtree).
(*isavl包括了searchtree的性质*)                



Fixpoint insert (k:Key)(v:Value)(t:tree):tree:=
match t with
|E=>(T E (newnode k v (S O)) E)
|T ltree n rtree=>match (Z.eqb k (key_of n)) with
                  |true=>T ltree (newnode (key_of n)(v)(depth_of n)) rtree
                  |false=>
                      match (Z.ltb k (key_of n)) with
                      |true=>insert_balance ( R, n, rtree) (insert k v ltree )
                      |false=>insert_balance ( L, n, ltree) (insert k v rtree )
                      end
                  end
end.
Theorem Insert : forall k v t , is_AVL t -> is_AVL (insert k v t).
Proof.
  intros.
  induction H.
  - simpl. admit.
  - 



