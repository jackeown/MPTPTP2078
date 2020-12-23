%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0771+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:05 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   38 (  74 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 207 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),sK1)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),sK1)
      | ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f12])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),sK1)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_3,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_76,plain,
    ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1)))
    | r2_hidden(X0,k3_relat_1(sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_5])).

cnf(c_128,plain,
    ( ~ r2_hidden(X0_36,k3_relat_1(k2_wellord1(sK2,X0_37)))
    | r2_hidden(X0_36,k3_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_76])).

cnf(c_180,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)),k3_relat_1(k2_wellord1(sK2,sK1)))
    | r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)),k3_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_132,plain,
    ( ~ r2_hidden(sK0(X0_37,X1_37),X1_37)
    | r1_tarski(X0_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_173,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)),k3_relat_1(sK2))
    | r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_131,plain,
    ( r2_hidden(sK0(X0_37,X1_37),X0_37)
    | r1_tarski(X0_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_174,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)),k3_relat_1(k2_wellord1(sK2,sK1)))
    | r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_65,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1))) ),
    inference(resolution,[status(thm)],[c_2,c_5])).

cnf(c_129,plain,
    ( r2_hidden(X0_36,X0_37)
    | ~ r2_hidden(X0_36,k3_relat_1(k2_wellord1(sK2,X0_37))) ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_167,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),sK1),k3_relat_1(k2_wellord1(sK2,sK1)))
    | r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_164,plain,
    ( ~ r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),sK1),sK1)
    | r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_161,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(sK2,sK1)),sK1),k3_relat_1(k2_wellord1(sK2,sK1)))
    | r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),k3_relat_1(sK2))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK1)),sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_180,c_173,c_174,c_167,c_164,c_161,c_4])).


%------------------------------------------------------------------------------
