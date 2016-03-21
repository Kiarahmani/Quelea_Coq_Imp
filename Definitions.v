Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Strings.String.


(*=================================Basic Definitions*)
Parameter SessID : Set.
Parameter OperName : Set.
Parameter Value : Set.
Definition SeqNo := nat.
Inductive ConsCls:Type := ec: ConsCls |cc: ConsCls |sc: ConsCls.
Inductive op_cls :Type := mkop_cls: OperName -> ConsCls -> op_cls. 


(*================================ Effects and Soups and Sessions*)

Record  Effect : Set := mkEffect {name:string; sess : SessID; seq : SeqNo; oper : OperName; val:Value}.
Definition Exec_A := (Ensemble Effect).
Parameter Compute: Exec_A -> OperName -> Value. 
Definition session := list op_cls.
Inductive Soup_Ing : Type := |mkSoup_Ing : SessID -> SeqNo -> session -> Soup_Ing.
Definition SessSoup := (Ensemble Soup_Ing).
Inductive op_key : Type:= op_key_cons: SessID->SeqNo->OperName -> op_key.

Notation " '<' s , i , op '>' " := (op_key_cons s i op) (at level 0, op at level 20).
Notation " '<<' A ',' B ',' C  '>>'  " := (mkSoup_Ing A B C)(at level 10).
Notation " S  '|||'  I " :=  ( Union Soup_Ing S  (Singleton Soup_Ing I) ) (at level 80).
(*================================ Stores and Replicas *)  
Inductive ReplID:Type := Rid_cons: nat -> ReplID.
Definition Store := ReplID -> Exec_A.
Parameter dom : Store -> (Ensemble ReplID).
Parameter St_Dom_Error : Exec_A. 
Notation " A '∈' B " := (dom B A) (at level 80).


Definition Rid_to_nat (r:ReplID): nat :=
  match r with
    |Rid_cons n => n
  end.

Definition F_Union (θ:Store)(r:ReplID)(η:Effect) (rcheck:ReplID) :  Exec_A :=  
  if (beq_nat (Rid_to_nat r)(Rid_to_nat rcheck))
  then  (Union Effect (θ r) (Singleton Effect η)) else St_Dom_Error.

Definition Store_Union (Θ:Store) (r:ReplID) (η:Effect) :=
  Union (ReplID -> Exec_A) (Singleton (ReplID -> Exec_A) Θ) (Singleton (ReplID -> Exec_A)(F_Union Θ r η)).  

Definition WF_union (S:SessSoup) (I:Soup_Ing): Prop := ~In Soup_Ing S I. 

(*================================ Relations of Effects *)
Definition Relation := relation Effect.
Parameter  Rel_dom : Relation -> (Ensemble Effect). 
Axiom WF_Relation : forall (r:Relation)(a b:Effect), r a b -> Rel_dom r a /\ Rel_dom r b.

(*Inverse of a relation*)
Inductive rtrn_invs (rel:Relation) (n:Effect) : Ensemble Effect  :=
  first: forall m:Effect, (rel m n) -> (rtrn_invs rel n) m.

Definition Rel_Closure (r:Relation):= clos_trans Effect r.
Definition Rel_Union (r1 r2 :Relation) (a b :Effect):Prop  :=  r1 a b \/ r2 a b.
Definition Rel_Intersect (r1 r2 :Relation) (a b :Effect):Prop  :=  r1 a b /\ r2 a b.

Infix "∩" := Rel_Intersect (at level 40).
Infix "∪" := Rel_Union (at level 50).
(*================================ Executions *)
Inductive Exec : Type :=
|E : Exec_A->  Relation -> Relation -> Relation -> Exec.
Definition return_vis (Ex:Exec): Relation := 
  match Ex with 
    |(E AA rr1 rr2 rr3) => rr1
  end.
Definition return_so (Ex:Exec): Relation := 
  match Ex with 
    |(E AA rr1 rr2 rr3) => rr2
  end.
Definition return_samobj (Ex:Exec): Relation := 
  match Ex with 
    |(E AA rr1 rr2 rr3) => rr3
  end.
Definition return_A (Ex:Exec) :=
  match Ex with
    |(E A vis so sameobj) => A
  end.

Definition hb (Ex:Exec) : Relation := Rel_Closure (Rel_Union (return_vis Ex) (return_so Ex)).
Definition soo (Ex:Exec) : Relation := (Rel_Intersect (return_so Ex) (return_samobj Ex)).
Definition hbo (Ex: Exec) : Relation := (Rel_Closure (Rel_Union (soo Ex) (return_vis Ex))).

Notation "Ex -vis" := (return_vis Ex) (at level 0).
Notation "Ex -so" := (return_so Ex) (at level 0).
Notation "Ex -sameobj" := (return_samobj Ex) (at level 0).
Notation "Ex -A" := (return_A Ex) ( at level 0).
Notation "Ex -soo" := (soo Ex) (at level 0).
Notation "Ex -hb" := (hb Ex) (at level 0).
Notation "Ex -hbo" := (hbo Ex) (at level 0).



(*================================ Well-Formedness of Executions *)
(*!!! This should be changed to a clean inductive definition*)

Parameter WF : Exec -> Prop.

Definition WF1 (Ex:Exec) := forall (a:Effect),     (Ex-A a) -> ~(Ex-hb a a).
Definition WF2 (Ex:Exec) := forall (a b:Effect),   (Ex-A a) -> (Ex-A b) -> (Ex-vis a b)-> (Ex-sameobj a b).
Definition WF3 (Ex:Exec) := forall (a b c:Effect), (Ex-so a b)/\(Ex-so b c) -> (Ex-so a c).
Definition WF4 (Ex:Exec) := forall (a:Effect),     (Ex-A a) -> (Ex-sameobj a a).
Definition WF5 (Ex:Exec) := forall (a b:Effect),   (Ex-A a) -> (Ex-A b) ->(Ex-sameobj a b)-> (Ex-sameobj b a).
Definition WF6 (Ex:Exec) := forall (a b c:Effect), (Ex-A a) -> (Ex-A b) ->(Ex-A c) -> (Ex-sameobj a b)/\(Ex-sameobj b c) -> (Ex-sameobj a c).
Definition WF7 (Ex:Exec) := forall (a b : Effect), (~(Ex-A a))\/(~(Ex-A b)) -> ~(Ex-so a b) /\ ~(Ex-vis a b) /\  ~(Ex-sameobj a b).

