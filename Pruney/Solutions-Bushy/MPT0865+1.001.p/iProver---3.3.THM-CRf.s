%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0865+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:17 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  72 expanded)
%              Number of clauses        :   14 (  21 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 184 expanded)
%              Number of equality atoms :   35 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK0(X1),sK1(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK0(X1),sK1(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK0(X1),sK1(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,X1)
         => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
        & r2_hidden(X0,X1)
        & v1_relat_1(X1) )
   => ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) != sK2
      & r2_hidden(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) != sK2
    & r2_hidden(sK2,sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f12])).

fof(f17,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_resolution,[],[f15])).

fof(f18,plain,(
    k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) != sK2 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_40,plain,
    ( ~ v1_relat_1(X0)
    | k4_tarski(sK0(X1),sK1(X1)) = X1
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_41,plain,
    ( ~ v1_relat_1(sK3)
    | k4_tarski(sK0(sK2),sK1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_40])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_43,plain,
    ( k4_tarski(sK0(sK2),sK1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41,c_4])).

cnf(c_56,plain,
    ( k4_tarski(sK0(sK2),sK1(sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_1,plain,
    ( k4_tarski(k1_mcart_1(k4_tarski(X0,X1)),k2_mcart_1(k4_tarski(X0,X1))) = k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_58,plain,
    ( k4_tarski(k1_mcart_1(k4_tarski(X0_38,X0_39)),k2_mcart_1(k4_tarski(X0_38,X0_39))) = k4_tarski(X0_38,X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_77,plain,
    ( k4_tarski(sK0(sK2),sK1(sK2)) = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(superposition,[status(thm)],[c_56,c_58])).

cnf(c_79,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_77,c_56])).

cnf(c_2,negated_conjecture,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) != sK2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_57,negated_conjecture,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) != sK2 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79,c_57])).


%------------------------------------------------------------------------------
