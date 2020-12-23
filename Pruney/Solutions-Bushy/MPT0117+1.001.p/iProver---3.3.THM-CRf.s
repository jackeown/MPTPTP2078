%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0117+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:31 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   30 (  47 expanded)
%              Number of clauses        :   11 (  13 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 118 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f18,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,plain,(
    ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)),sK1) ),
    inference(definition_unfolding,[],[f18,f13])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_54,plain,
    ( ~ r1_tarski(X0_34,X0_35)
    | r1_tarski(k4_xboole_0(X0_34,X1_34),X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_85,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_82,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK0),sK1)
    | ~ r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_53,plain,
    ( ~ r1_tarski(X0_34,X0_35)
    | ~ r1_tarski(X1_34,X0_35)
    | r1_tarski(k2_xboole_0(X0_34,X1_34),X0_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_79,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)),sK1)
    | ~ r1_tarski(k4_xboole_0(sK2,sK0),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_2,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)),sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_85,c_82,c_79,c_2,c_3,c_4])).


%------------------------------------------------------------------------------
