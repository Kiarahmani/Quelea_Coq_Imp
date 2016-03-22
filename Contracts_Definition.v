Require Import Coq.Strings.String.
Require Import Definitions.

Parameter Eff_name : Effect -> string.

Inductive EffVar : Type :=
|effvar: string -> EffVar.

Definition η'':=effvar "η''".


Inductive contract_EffType : Type :=
|contract_EffType_cons: OperName -> contract_EffType
|contract_efftype_disjunction: contract_EffType -> contract_EffType -> contract_EffType.

Inductive contract_Relation : Type :=
|contract_equi: contract_Relation
|contract_vis: contract_Relation
|contract_so: contract_Relation
|contract_sameobj: contract_Relation
|contract_relation_union: contract_Relation -> contract_Relation -> contract_Relation
|contract_relation_intersect: contract_Relation -> contract_Relation -> contract_Relation
|contract_relation_closure: contract_Relation -> contract_Relation.

Definition Soo : contract_Relation :=
  contract_relation_intersect contract_so contract_sameobj.

Definition Hb : contract_Relation :=
  contract_relation_closure (contract_relation_union contract_so contract_vis).

Definition Hbo:contract_Relation :=
  contract_relation_closure(contract_relation_union Soo contract_vis).

Inductive contract_Prop : Type :=
|contract_prop_true
|contract_prop_effeff : contract_Relation -> Effect -> Effect -> contract_Prop
|contract_prop_effvar : contract_Relation -> Effect -> EffVar -> contract_Prop
|contract_prop_vareff : contract_Relation -> EffVar -> Effect -> contract_Prop
|contract_prop_varvar : contract_Relation -> EffVar -> EffVar -> contract_Prop                                     
|contract_prop_disjunction: contract_Prop -> contract_Prop   -> contract_Prop
|contract_prop_conjunction: contract_Prop -> contract_Prop   -> contract_Prop
|contract_prop_implication: contract_Prop -> contract_Prop   -> contract_Prop.      

Inductive contract_Contract : Type :=
|contract_free_cons: contract_Prop -> contract_Contract
|contract_untyped_cons: EffVar->contract_Contract -> contract_Contract
|contract_typed_cons: EffVar -> contract_EffType -> contract_Contract -> contract_Contract.




Definition m:EffVar := effvar "m".
Definition n:EffVar :=effvar "n".
Infix " '#-->' " := contract_prop_implication (at level 80).
Infix " '#\/#' " := contract_prop_disjunction (at level 70).
Infix " '#/\#' " := contract_prop_conjunction (at level 60).
Notation " 'Sameobj' " := contract_sameobj.
Notation " 'Vis' " := contract_vis.
Notation " 'Equi' " := contract_equi.
Notation " 'PROP:'  ":= contract_prop_varvar (at level 90).
Notation " 'CONTR:'  ":=contract_free_cons (at level 95).
Notation " 'ALL'  ":=(contract_untyped_cons) (at level 96).



(*================================ Store Consistency *)

Definition Store_Contr (τ:ConsCls):contract_Contract:=
  match τ with
    |sc =>ALL  m (CONTR: ((PROP: Sameobj m η'')   #-->
                                                 ((PROP: Vis m η'') #\/# (PROP: Vis η'' m) #\/#
                                                                    (PROP: Equi m η''))))
    |cc => ALL m (CONTR: ((PROP: Hbo m η'') #--> (PROP: Vis m η'')))
    |ec => ALL m (ALL n (CONTR: ((PROP: Hbo m n) #/\# (PROP: Vis n η'') #--> (PROP: Vis m η''))))
  end.

Notation " 'Ψ' " := Store_Contr.












