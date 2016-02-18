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
Require Import contract_definition.
Require Import Coq.Strings.String.
Require Import contract_subs.
Parameter Eff_name : Effect -> string.
Variable η_hat : EffVar.


Fixpoint relation_Evaluation (rel : contract_Relation) (Ex:Exec) : Relation :=
  match rel with
    |contract_vis   => Ex-vis
    |contract_so => Ex-so
    |contract_sameobj => Ex-sameobj
    |contract_relation_union R1 R2 => my_union (relation_Evaluation R1 Ex) (relation_Evaluation R2 Ex)
    |contract_relation_intersect R1 R2 => my_intersect (relation_Evaluation R1 Ex)  (relation_Evaluation R2 Ex)
    |contract_relation_closure R1 => (my_trans  (relation_Evaluation R1 Ex))
  end.

Inductive Eval_result : Type :=
|result : Prop -> Eval_result
|error : Eval_result.

Definition result_prop (e1:Eval_result) : Prop :=
  match e1 with
    |result T => T
    |_=> False
  end.

Definition And_result (e1 e2: Eval_result): Eval_result:=
  match (e1,e2) with
    |(_,error) => error
    |(error,_) => error
    |(result X1,result X2) => result (X1/\X2)
  end.

Definition Or_result (e1 e2: Eval_result): Eval_result:=
  match (e1,e2) with
    |(_,error) => error
    |(error,_) => error
    |(result X1,result X2) => result (X1\/X2)
  end.

Definition Imp_result (e1 e2: Eval_result): Eval_result:=
  match (e1,e2) with
    |(_,error) => error
    |(error,_) => error
    |(result X1,result X2) => result (X1->X2)
  end.



Fixpoint Prop_Evaluation (pr:contract_Prop)(Ex:Exec) : Prop:=
  match pr with
    |contract_prop_true => True
    |contract_prop_effeff R1 α β      => (relation_Evaluation R1 Ex) α β
    |contract_prop_conjunction p1 p2  =>  (Prop_Evaluation p1 Ex) /\ (Prop_Evaluation p2 Ex)
    |contract_prop_disjunction p1 p2  =>  (Prop_Evaluation p1 Ex) \/  (Prop_Evaluation p2 Ex)
    |contract_prop_implication p1 p2  =>  (Prop_Evaluation p1 Ex) ->  (Prop_Evaluation p2 Ex)
    |_=> False                                                           
  end.

Fixpoint contract_Eval (cont: contract_Contract) (Ex:Exec) (eff : Effect) (n:nat):Prop :=
  match n with
    |O => match cont with
           |contract_free_cons π => Prop_Evaluation (Prop_Subst π eff η_hat) Ex
           |_=> False
         end
           
    |S n' => match cont with
              |contract_typed_cons e τ ψ =>  forall e:Effect,(Ex-A e)-> contract_Eval (contract_Subst ψ e (effvar (Eff_name e))) Ex eff n'
              |_=> False
            end
  end.

                       
Fixpoint contract_free_number (cont:contract_Contract) : nat :=
  match cont with
    |contract_free_cons p => 0
    |contract_untyped_cons e ψ => contract_free_number ψ +1
    |contract_typed_cons e t ψ => contract_free_number ψ +1
  end.


















