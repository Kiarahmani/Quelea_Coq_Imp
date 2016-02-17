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




Module Type ATOM.

  Parameter atom : Set.
  Parameter eq_atom_dec : forall x y : atom, {x = y} + {x <> y}.

End ATOM.





Definition EffVar := Variable String.


Inductive EffVar : Type := |EffVar_x |EffVar_y |EffVar_η. 

Fixpoint Prop_Evaluation (pr:contract_Prop)(Ex:Exec) : Eval_result :=
  match pr with
    |contract_prop_true => result True
    |contract_prop_effeff R1 α β      => result((relation_Evaluation R1 Ex) α β)
    |contract_prop_conjunction p1 p2  => And_result (Prop_Evaluation p1 Ex) (Prop_Evaluation p2 Ex)
    |contract_prop_disjunction p1 p2  => Or_result  (Prop_Evaluation p1 Ex) (Prop_Evaluation p2 Ex)
    |contract_prop_implication p1 p2  => Imp_result (Prop_Evaluation p1 Ex) (Prop_Evaluation p2 Ex)
    |_=> error                                                             
  end.
























Inductive contract_Contract : Type :=
|contract_free_cons: contract_Prop -> contract_Contract
|contract_untyped_cons: Effect -> contract_Contract -> contract_Contract
|contract_typed_cons: Effect -> contract_EffType -> contract_Contract -> contract_Contract.













Fixpoint contract_Evaluation (cont: contract_Contract) (Ex:Exec) :Prop :=
  match cont with
    |contract_free_cons π => Prop_Evaluation π Ex
    |contract_untyped_cons e ψ => 
    |contract_typed_cons e τ ψ => True
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
