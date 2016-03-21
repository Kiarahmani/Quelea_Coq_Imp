Require Import List.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Definitions.

Module Operational_Semantics.
  (*Equality between two Ensemble*)
  Definition Set_Equi (A:Type) (E1 E2: Ensemble A) : Prop :=
    (Included A E1 E2)/\(Included A E2 E1).
  

  (*==================================Auxiliary Reduction [OPER]==============================*)
  
  Reserved Notation "'['  Θ '|-' A , C '~' r '~>' B , n ']'" (at level 80,Θ at level 10).
  Inductive Aux_Reduct (Θ:Store) (r: ReplID) : Exec -> op_key -> Exec -> Effect -> Prop :=
    OPER :  forall   (A A': Exec_A) (v: Value) 
                (vis so sameobj vis' so' sameobj' : Relation) 
                (s:SessID)(i:SeqNo) (op:OperName) (η η': Effect),
              r ∈ Θ -> 
              (Compute (Θ r) op)=v -> 
              η.(sess)=s /\ η.(seq)=i /\ η.(val)=v /\ η.(oper)=op  ->
              (forall eff, ((A eff) /\ eff.(sess)=s /\ eff.(seq) = i-1) <-> eff=η' ) ->
              (forall eff,(A eff \/ eff=η )<->(A' eff)) ->
              (forall (eff eff':Effect), (vis' eff eff')<->((((Θ r) eff)/\eff'=η)\/((A eff/\ A eff')/\(vis eff eff')))) ->
              (forall (eff eff':Effect), (so' eff eff') <-> ((((so eff η') \/ (eff=η'))/\(eff'=η)) \/ (so eff eff'))) ->
              (forall eff eff', A' eff-> A' eff'-> (sameobj' eff eff')) ->
              (i>0) 
              ->[ Θ |- (E A vis so sameobj), <s,i,op>   ~r~>  (E A' vis' so' sameobj') ,η]
                 
                 where "'[' Θ |- A , C '~' r '~>' B , n ']'" := (Aux_Reduct Θ r A C B n).





  (*================================== Operational Semantics ==============================*)

  Variable Error_opcls:op_cls. (*Default return value if the session is empty *)
  
  Reserved Notation "'[[' A , B , C '--' τ ',' n '-->' A' , B' , C' ']]'" (at level 0, n at level 200, τ at level 100).
  
  Inductive Progress (η:Effect)(τ:ConsCls) :  Exec->Store->SessSoup ->Exec -> Store -> SessSoup ->Prop :=     

  |EFFVIS: forall (Σ: SessSoup) ( Θ Θ' :Store) (Ex:Exec) (r:ReplID),
             (In (Store) (Store_Union Θ r η)  Θ')->
             (dom Θ' = dom Θ)->
             (r∈ Θ) ->
             (Included Effect (Union Effect (rtrn_invs Ex-vis η) (rtrn_invs Ex-so η)) (Θ r))->
             (Ex-A η)->
             ~((Θ r)η)->                                                                         
             [[Ex,Θ,Σ --τ,η-->  Ex ,Θ' ,Σ ]]

               
  |EC: forall  (Θ:Store)(Σ: SessSoup)(Ex Ex':Exec)(ss:SessID)(ii:SeqNo) 
          (opp:OperName)(r:ReplID) (oplist:session), 
         (τ=ec) -> [Θ |- Ex, <ss,ii,opp> ~r~> Ex', η] ->
         [[Ex,Θ,Σ ||| (mkSoup_Ing ss ii ((mkop_cls opp τ)::oplist))  --τ,η-->  Ex' ,Θ ,Σ ||| (mkSoup_Ing ss (ii+1) oplist ) ]]                 


  |CC: forall (Ex Ex':Exec) (Θ:Store)(Σ: SessSoup)(r:ReplID)
         (ss:SessID)(ii:SeqNo)(opp:OperName)(oplist:session),  
         (τ=cc)->
         (Included Effect (rtrn_invs Ex'-so η) (Θ r))->
         ([ Θ |- Ex, <ss,ii,opp> ~r~> Ex', η]) 
         ->[[Ex,Θ,Σ||| (mkSoup_Ing ss ii ((mkop_cls opp τ)::oplist)) --τ,η-->  Ex' ,Θ ,Σ|||(mkSoup_Ing ss (ii+1) oplist ) ]]


  |SC: forall (Ex Ex':Exec) (Θ Θ':Store)(Σ: SessSoup)(r:ReplID)
         (ss:SessID)(ii:SeqNo)(opp:OperName)(oplist:session),  
         (τ=sc)->
         ([Θ|-Ex, <ss,ii,opp> ~r~> Ex', η])->
         (Included Effect (Ex-A)(Θ r))->
         (Included ReplID (dom Θ) (dom Θ') /\ Included ReplID (dom Θ') (dom Θ)) ->
         (forall r':ReplID, ((dom Θ') r') ->  
                       (Set_Equi Effect (Θ' r') (Union Effect (Θ r')  (Singleton Effect η)))) ->
         ((forall (r':ReplID)(a:Effect), ((dom Θ') r') -> (Ex-A a) -> (Ex'-hbo a η) -> ((Θ' r') a))) 
         ->[[Ex,Θ,Σ||| (mkSoup_Ing ss ii ((mkop_cls opp τ)::oplist)) --τ,η-->  Ex' ,Θ' ,Σ|||(mkSoup_Ing ss (ii+1) oplist ) ]]

            where " '[['  E , Θ , Σ  '--' τ , η '-->'  F , T ,  S ']]' " := (Progress η τ E Θ Σ F T S).







End Operational_Semantics.