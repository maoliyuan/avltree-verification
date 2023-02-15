Class Reb A := {
  Equal_bool :  A -> A -> bool
}.

Class Rlt A := 
{
  lt_prop :  A -> A -> Prop
}.

Class Rltb A := {
  lt_bool :  A -> A -> bool
}.

Class Reflexive A  `{Rlt A}:=
    reflexivity : forall x : A, lt_prop x x.

Class Transitive A `{Rlt A} := 
    transitivity : forall {x y z}, lt_prop x y -> lt_prop y z -> lt_prop x z.

Class Asymmetric A `{Rlt A} := 
    asymmetry : forall {x y}, lt_prop x y -> lt_prop y x -> False.


Class Complete A `{Rlt A}:=
  complete : forall {x y} , lt_prop x y \/ ~ lt_prop x y .

Class TotalOrder A `{Rlt A}:Prop := {
    Total_Transitive :> Transitive  A;
    Total_Asymmetric :> Asymmetric A;
    Total_complement :> Complete A;
}.

Definition  Rb_spec {A : Type }  `{Reb A}: Prop := forall  x y ,
  x = y <-> Equal_bool x y = true.

Definition  Rltb_spec {A : Type } `{Rlt A} `{Rltb A}: Prop := forall  x y ,
  lt_prop x y <-> lt_bool x y = true.

Definition  Rlt_R {A : Type } `{Rlt A}: Prop := forall  x y ,
  (~ lt_prop x y /\ ~ lt_prop y x) <->   x = y.

Definition lte_prop {A : Type } `{Rlt A} x y : Prop := lt_prop x y \/  x = y.
Definition lte_bool {A : Type } `{Reb A}`{Rltb A} x y : bool := if  lt_bool x y then true else Equal_bool x y .

(* TODO: clean this file *)

Class ComputableTotalOrder (Key: Type) := {
  KRb :>  Reb Key;
  LKR :> Rlt Key ;
  LKRb :> Rltb Key;
  TKR :> TotalOrder Key ;
  eqb_eq: @Rb_spec Key KRb;
  ltb_lt: @Rltb_spec Key LKR LKRb;
  lt_eq: @Rlt_R Key LKR;
  lte_complete: forall x y: Key , lte_prop x y \/ lte_prop y x
}.

Existing Instance KRb.
Existing Instance LKR.
Existing Instance LKRb.
Existing Instance TKR.

Notation "x =? y" := (Equal_bool x y) (at level 70).
Notation "x <? y " := (lt_bool x y) (at level 70).
Notation "x < y " := (lt_prop x y) (at level 70).

Notation "x <= y " := (lte_prop  x y) (at level 70).
Notation "x <=? y " := (lte_bool  x y) (at level 70).

