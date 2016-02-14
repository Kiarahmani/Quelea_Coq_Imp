Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Import Config.
Import parameters.
Import Operational_Semantics.


Inductive contract_EffVar : Type := |EffVar_x |EffVar_y |EffVar_η.

Inductive contract_EffType : Type :=
|contract_EffType_cons: OperName -> contract_EffType
|contract_efftype_disjunction: contract_EffType -> contract_EffType -> contract_EffType.

Inductive contract_Relation : Type :=
|contract_vis: contract_Relation
|contract_so: contract_Relation
|contract_sameobj: contract_Relation
|contract_relation_union: contract_Relation -> contract_Relation -> contract_Relation
|contract_relation_intersect: contract_Relation -> contract_Relation -> contract_Relation
|contract_relation_closure: contract_Relation -> contract_Relation.                                             

Inductive contract_Prop : Type :=
|contract_prop_true
|contract_prop_relation: contract_Relation -> contract_EffVar -> contract_EffVar -> contract_Prop
|contract_prop_disjunction: contract_Prop -> contract_Prop -> contract_Prop
|contract_prop_conjunction: contract_Prop -> contract_Prop -> contract_Prop
|contract_prop_implication: contract_Prop -> contract_Prop -> contract_Prop.      
                                                              
Inductive contract_Contract : Type :=
|contract_free_cons: contract_Prop -> contract_Contract
|contract_untyped_cons: contract_EffVar -> contract_Contract -> contract_Contract
|contract_typed_cons: contract_EffVar -> contract_EffType -> contract_Contract -> contract_Contract.





Fixpoint Rel_Evaluation (rel:contract_Relation) (α β: contract_EffType) (Ex:Exec) : bool :=
  match rel with
      |contract_vis => IF





  

Fixpoint Prop_Evaluation (pr:contract_Prop)(Ex:Exec): bool :=
  match pr with
    |contract_prop_true => true
    |contract_prop_relation R1 α β    => Rel_Evaluation R1 α β Ex 
    |contract_prop_conjunction p1 p2  => andb(Prop_Evaluation p1 Ex)       (Prop_Evaluation p2 Ex)
    |contract_prop_disjunction p1 p2  => orb (Prop_Evaluation p1 Ex)       (Prop_Evaluation p2 Ex)
    |contract_prop_implication p1 p2  => orb (negb(Prop_Evaluation p1 Ex)) (Prop_Evaluation p2 Ex)
    |_=>false

  end.























Inductive my_trans (R1:Relation): Relation :=
|my_base (e1 e2:Effect) : R1 e1 e2 -> my_trans R1 e1 e2
|my_step (e1 e2 e3:Effect) : (my_trans R1) e1 e2 -> (my_trans R1) e2 e3 -> my_trans R1 e1 e3.

Inductive my_union (R1 R2:Relation) : Relation :=
|my_uni_first  (e1 e2:Effect) : R1 e1 e2 -> my_union R1 R2 e1 e2
|my_uni_second (e1 e2:Effect) : R2 e1 e2 -> my_union R1 R2 e1 e2.
                                                    
Inductive my_intersect (R1 R2: Relation) : Relation :=
|intersect_cons (e1 e2: Effect) : R1 e1 e2 -> R2 e1 e2 -> (my_intersect R1 R2) e1 e2.



Fixpoint relation_Evaluation (rel : contract_Relation) (Ex:Exec) : Relation :=
  match rel with
    |contract_vis   => Ex-vis
    |contract_so => Ex-so
    |contract_sameobj => Ex-sameobj
    |contract_relation_union R1 R2 => my_union (relation_Evaluation R1 Ex) (relation_Evaluation R2 Ex)
    |contract_relation_intersect R1 R2 => my_intersect (relation_Evaluation R1 Ex)  (relation_Evaluation R2 Ex)
    |contract_relation_closure R1 => (my_trans  (relation_Evaluation R1 Ex))
  end.


Eval compute in (IF True then True else False).


Fixpoint prop_Evaluation (prop: contract_Prop)(Ex:Exec): bool :=
  match prop with
    |contract_prop_true => true
    |contract_prop_relation rel a b  => (relation_Evaluation rel Ex x y)
    |contract_prop_disjunction c1 c2 => (prop_Evaluation c1 Ex x y) \/ (prop_Evaluation c2 Ex x y)
    |contract_prop_conjunction c1 c2 => (prop_Evaluation c1 Ex x y) /\ (prop_Evaluation c2 Ex x y)
    |contract_prop_implication c1 c2 => (prop_Evaluation c1 Ex x y) -> (prop_Evaluation c2 Ex x y)

  end.
                                          
Fixpoint contract_Evaluation (Ctrt: contract_Contract) (Ex:Exec) : Prop :=
  match Ctrt with
    |contract_free_cons π => forall(x y:Effect) prop_Evaluation π Ex x y
    |contract_typed_cons e τ ψ => True
     
    |contract_untyped_cons e ψ => match e with
                                     |EffVar_x =>



     forall(eff:Effect), contract_Evaluation ψ Ex 

          
  end.







Theorem trans_test : forall (R1:Relation)(a b c d: Effect), R1 a b -> R1 b c -> R1 c d -> (my_trans R1) a d.
Proof.
  intros R a b c d.
  intros H1 H2. 
  assert ((my_trans R) a c).
  apply (my_base R) in H2.
  apply (my_base R) in H1.
  apply (my_step R a b c ) in H1.
  exact H1. exact H2.
  intro H3.
  apply (my_base R) in H3.
  apply (my_step R a c d). exact H. exact H3.
Qed.
