Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.
Require Import oper_semantic_coq.
Import Operational_Semantics.
Require Import contract_definition.
Require Import Coq.Strings.String.
Require Import contract_subs.
Parameter Eff_name : Effect -> string.



Axiom  Eff_Equi_refl : forall a,  Eff_Equi a a.

Definition η'':=effvar "η''".
Fixpoint relation_Evaluation (rel : contract_Relation) (Ex:Exec) : Relation :=
  match rel with
    |contract_equi => Eff_Equi
    |contract_vis   => Ex-vis
    |contract_so => Ex-so
    |contract_sameobj => Ex-sameobj
    |contract_relation_union R1 R2 => Rel_Union (relation_Evaluation R1 Ex) (relation_Evaluation R2 Ex)
    |contract_relation_intersect R1 R2 => Rel_Intersect (relation_Evaluation R1 Ex)  (relation_Evaluation R2 Ex)
    |contract_relation_closure R1 => (Rel_Closure  (relation_Evaluation R1 Ex))
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
           |contract_free_cons π => Prop_Evaluation (Prop_Subst π eff η'') Ex
           |_=> False
         end
          
    |S n' => match cont with
              |contract_typed_cons e τ ψ =>  forall ef:Effect,(Ex-A ef) -> contract_Eval (contract_Subst ψ ef e) Ex eff n'
              |contract_untyped_cons e ψ =>  forall ef:Effect,(Ex-A ef) -> contract_Eval (contract_Subst ψ ef e) Ex eff n' 
              |_=> False
            end
  end.

                       
Fixpoint contract_free_number (cont:contract_Contract) : nat :=
  match cont with
    |contract_free_cons p => 0
    |contract_untyped_cons e ψ => contract_free_number ψ +1
    |contract_typed_cons e t ψ => contract_free_number ψ +1
  end.

















