Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import parametes_coq.
Require Import config_coq.
Require Import oper_semantic_coq.
Require Import Coq.Strings.String.
Import Config.
Import parameters.
Import Operational_Semantics.
Require Import contract_defintion.
Require Import contract_Eval.


Parameter var_equal : forall x y : EffVar, {x = y} + {x <> y}.
Parameter Eff_name : Effect -> string.

Fixpoint Prop_Evaluation (pr:contract_Prop)(Ex:Exec) : Prop:=
  match pr with
    |contract_prop_true => True
    |contract_prop_effeff R1 α β      => (relation_Evaluation R1 Ex) α β
    |contract_prop_conjunction p1 p2  =>  (Prop_Evaluation p1 Ex) /\ (Prop_Evaluation p2 Ex)
    |contract_prop_disjunction p1 p2  =>  (Prop_Evaluation p1 Ex) \/  (Prop_Evaluation p2 Ex)
    |contract_prop_implication p1 p2  =>  (Prop_Evaluation p1 Ex) ->  (Prop_Evaluation p2 Ex)
    |_=> False                                                           
  end.


Fixpoint Prop_Subst (pr:contract_Prop)(eff:Effect)(v:EffVar) : contract_Prop :=
  match pr with
    |contract_prop_true => contract_prop_true
    |contract_prop_effeff R1 e1 e2 => contract_prop_effeff R1 e1 e2
    |contract_prop_effvar R1 e1 v1 => if (var_equal v v1) then contract_prop_effeff R1 e1 eff else contract_prop_effvar R1 e1 v1
    |contract_prop_vareff R1 v1 e1 => if (var_equal v v1) then contract_prop_effeff R1 eff e1 else contract_prop_vareff R1 v1 e1
    |contract_prop_varvar R1 v1 v2 => if (var_equal v v1)
                                     then (if (var_equal v v2) then contract_prop_effeff R1 eff eff
                                                               else contract_prop_effvar R1 eff v2)
                                     else (if (var_equal v v2) then contract_prop_vareff R1 v1 eff
                                           else contract_prop_varvar R1 v1 v2)
    |contract_prop_disjunction p1 p2 => contract_prop_disjunction (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)
    |contract_prop_conjunction p1 p2 => contract_prop_conjunction (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)
    |contract_prop_implication p1 p2 => contract_prop_implication (Prop_Subst p1 eff v) (Prop_Subst p2 eff v)                             
  end.

Fixpoint contract_Subst (ct:contract_Contract) (eff:Effect)(v:EffVar) : contract_Contract :=
  match ct with
    |contract_free_cons π => contract_free_cons (Prop_Subst π eff v)
    |contract_typed_cons e τ ψ => contract_Subst ψ eff v
  end.
Variable x :EffVar.



Fixpoint contract_Eval (cont: contract_Contract) (Ex:Exec) (n:nat):Prop :=
  match n with
    |O => match cont with
           |contract_free_cons π => Prop_Evaluation π Ex
           |_=> False
         end
           
    |S n' => match cont with
              |contract_typed_cons e τ ψ =>  forall e:Effect,(Ex-A e)-> contract_Eval (contract_Subst ψ e (effvar (Eff_name e))) Ex n'
              |_=>False
            end
  end.

                       
                                                                            

   


