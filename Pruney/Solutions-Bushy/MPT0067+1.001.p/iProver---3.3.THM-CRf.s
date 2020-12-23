%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0067+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:23 EST 2020

% Result     : Theorem 0.66s
% Output     : CNFRefutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 109 expanded)
%              Number of equality atoms :   29 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) )
   => ( r2_xboole_0(sK1,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( r2_xboole_0(sK1,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f13])).

fof(f16,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_79,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_142,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_143,plain,
    ( sK0 != sK0
    | sK0 = sK1
    | sK1 != sK0 ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_80,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_133,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(sK1,sK0)
    | X1 != sK0
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_135,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ r2_xboole_0(sK1,sK0)
    | sK0 != sK0
    | sK0 != sK1 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_0,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_130,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_78,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_83,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_48,plain,
    ( r2_xboole_0(X0,X1)
    | X1 = X0
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_49,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(unflattening,[status(thm)],[c_48])).

cnf(c_2,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_12,plain,
    ( ~ r2_xboole_0(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,negated_conjecture,
    ( r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143,c_135,c_130,c_83,c_49,c_12,c_4])).


%------------------------------------------------------------------------------
