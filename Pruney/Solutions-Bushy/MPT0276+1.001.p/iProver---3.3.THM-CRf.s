%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0276+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:54 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 200 expanded)
%              Number of clauses        :   38 (  69 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  178 ( 753 expanded)
%              Number of equality atoms :  117 ( 493 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f20])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14])).

fof(f27,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_293,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k1_tarski(X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_292,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_887,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k1_tarski(X2)
    | r2_hidden(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_293,c_292])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_286,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_709,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0)
    | k4_xboole_0(k2_tarski(X0,X2),X1) = k1_xboole_0
    | r2_hidden(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_293,c_286])).

cnf(c_960,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0)
    | k4_xboole_0(k2_tarski(X2,X2),X1) = k1_tarski(X2)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_293,c_709])).

cnf(c_14,negated_conjecture,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1239,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK1),sK2) = k1_tarski(sK1)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k1_tarski(sK0) ),
    inference(superposition,[status(thm)],[c_960,c_14])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_386,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_393,plain,
    ( r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK1,sK1),sK2) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_456,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,X0),sK2) = k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_650,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_1365,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK1),sK2) = k1_tarski(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1239,c_14,c_13,c_386,c_393,c_650])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_290,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_498,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
    | r2_hidden(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_290])).

cnf(c_1373,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_498])).

cnf(c_1397,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),sK2) = k1_tarski(X0)
    | k4_xboole_0(k2_tarski(sK1,X0),sK2) = k1_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_887,c_1373])).

cnf(c_2187,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),sK2) = k1_tarski(X0)
    | k4_xboole_0(k2_tarski(X0,sK1),sK2) = k1_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_0,c_1397])).

cnf(c_2272,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK1)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_531,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK1,sK1),sK2) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_522,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK2) != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_123,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_418,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_124,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_376,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != X0
    | k2_tarski(sK0,sK1) != X0
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_417,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_391,plain,
    ( r2_hidden(X0,sK2)
    | r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(X0,sK1),sK2) = k2_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_407,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_11,negated_conjecture,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2272,c_1365,c_531,c_522,c_418,c_417,c_407,c_11,c_12])).


%------------------------------------------------------------------------------
