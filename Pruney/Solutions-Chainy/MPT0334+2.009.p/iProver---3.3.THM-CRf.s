%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:23 EST 2020

% Result     : Theorem 35.34s
% Output     : CNFRefutation 35.34s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 166 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 ( 305 expanded)
%              Number of equality atoms :   84 ( 187 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f40,f61])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f40,f61,f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),X0)) = k3_tarski(k2_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f60,f40,f40,f60])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))
      & sK1 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))
    & sK1 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f31])).

fof(f58,plain,(
    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f58,f60,f40,f61,f61,f40,f60,f61,f61])).

fof(f57,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3468,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_60983,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_3468])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_641,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK1))))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_22247,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_833,plain,
    ( r2_hidden(sK2,X0)
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),X0)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1161,plain,
    ( r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0))
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_10787,plain,
    ( r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2286,plain,
    ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_tarski(k2_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) = k5_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1337,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
    | k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_240,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_949,plain,
    ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) = k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_241,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_631,plain,
    ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != X0
    | k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) = k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1)))
    | k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) != X0 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_778,plain,
    ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2)))
    | k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) = k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1)))
    | k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) != k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_20,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60983,c_22247,c_10787,c_2286,c_1337,c_949,c_778,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.34/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.34/5.00  
% 35.34/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.34/5.00  
% 35.34/5.00  ------  iProver source info
% 35.34/5.00  
% 35.34/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.34/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.34/5.00  git: non_committed_changes: false
% 35.34/5.00  git: last_make_outside_of_git: false
% 35.34/5.00  
% 35.34/5.00  ------ 
% 35.34/5.00  
% 35.34/5.00  ------ Input Options
% 35.34/5.00  
% 35.34/5.00  --out_options                           all
% 35.34/5.00  --tptp_safe_out                         true
% 35.34/5.00  --problem_path                          ""
% 35.34/5.00  --include_path                          ""
% 35.34/5.00  --clausifier                            res/vclausify_rel
% 35.34/5.00  --clausifier_options                    ""
% 35.34/5.00  --stdin                                 false
% 35.34/5.00  --stats_out                             all
% 35.34/5.00  
% 35.34/5.00  ------ General Options
% 35.34/5.00  
% 35.34/5.00  --fof                                   false
% 35.34/5.00  --time_out_real                         305.
% 35.34/5.00  --time_out_virtual                      -1.
% 35.34/5.00  --symbol_type_check                     false
% 35.34/5.00  --clausify_out                          false
% 35.34/5.00  --sig_cnt_out                           false
% 35.34/5.00  --trig_cnt_out                          false
% 35.34/5.00  --trig_cnt_out_tolerance                1.
% 35.34/5.00  --trig_cnt_out_sk_spl                   false
% 35.34/5.00  --abstr_cl_out                          false
% 35.34/5.00  
% 35.34/5.00  ------ Global Options
% 35.34/5.00  
% 35.34/5.00  --schedule                              default
% 35.34/5.00  --add_important_lit                     false
% 35.34/5.00  --prop_solver_per_cl                    1000
% 35.34/5.00  --min_unsat_core                        false
% 35.34/5.00  --soft_assumptions                      false
% 35.34/5.00  --soft_lemma_size                       3
% 35.34/5.00  --prop_impl_unit_size                   0
% 35.34/5.00  --prop_impl_unit                        []
% 35.34/5.00  --share_sel_clauses                     true
% 35.34/5.00  --reset_solvers                         false
% 35.34/5.00  --bc_imp_inh                            [conj_cone]
% 35.34/5.00  --conj_cone_tolerance                   3.
% 35.34/5.00  --extra_neg_conj                        none
% 35.34/5.00  --large_theory_mode                     true
% 35.34/5.00  --prolific_symb_bound                   200
% 35.34/5.00  --lt_threshold                          2000
% 35.34/5.00  --clause_weak_htbl                      true
% 35.34/5.00  --gc_record_bc_elim                     false
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing Options
% 35.34/5.00  
% 35.34/5.00  --preprocessing_flag                    true
% 35.34/5.00  --time_out_prep_mult                    0.1
% 35.34/5.00  --splitting_mode                        input
% 35.34/5.00  --splitting_grd                         true
% 35.34/5.00  --splitting_cvd                         false
% 35.34/5.00  --splitting_cvd_svl                     false
% 35.34/5.00  --splitting_nvd                         32
% 35.34/5.00  --sub_typing                            true
% 35.34/5.00  --prep_gs_sim                           true
% 35.34/5.00  --prep_unflatten                        true
% 35.34/5.00  --prep_res_sim                          true
% 35.34/5.00  --prep_upred                            true
% 35.34/5.00  --prep_sem_filter                       exhaustive
% 35.34/5.00  --prep_sem_filter_out                   false
% 35.34/5.00  --pred_elim                             true
% 35.34/5.00  --res_sim_input                         true
% 35.34/5.00  --eq_ax_congr_red                       true
% 35.34/5.00  --pure_diseq_elim                       true
% 35.34/5.00  --brand_transform                       false
% 35.34/5.00  --non_eq_to_eq                          false
% 35.34/5.00  --prep_def_merge                        true
% 35.34/5.00  --prep_def_merge_prop_impl              false
% 35.34/5.00  --prep_def_merge_mbd                    true
% 35.34/5.00  --prep_def_merge_tr_red                 false
% 35.34/5.00  --prep_def_merge_tr_cl                  false
% 35.34/5.00  --smt_preprocessing                     true
% 35.34/5.00  --smt_ac_axioms                         fast
% 35.34/5.00  --preprocessed_out                      false
% 35.34/5.00  --preprocessed_stats                    false
% 35.34/5.00  
% 35.34/5.00  ------ Abstraction refinement Options
% 35.34/5.00  
% 35.34/5.00  --abstr_ref                             []
% 35.34/5.00  --abstr_ref_prep                        false
% 35.34/5.00  --abstr_ref_until_sat                   false
% 35.34/5.00  --abstr_ref_sig_restrict                funpre
% 35.34/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.34/5.00  --abstr_ref_under                       []
% 35.34/5.00  
% 35.34/5.00  ------ SAT Options
% 35.34/5.00  
% 35.34/5.00  --sat_mode                              false
% 35.34/5.00  --sat_fm_restart_options                ""
% 35.34/5.00  --sat_gr_def                            false
% 35.34/5.00  --sat_epr_types                         true
% 35.34/5.00  --sat_non_cyclic_types                  false
% 35.34/5.00  --sat_finite_models                     false
% 35.34/5.00  --sat_fm_lemmas                         false
% 35.34/5.00  --sat_fm_prep                           false
% 35.34/5.00  --sat_fm_uc_incr                        true
% 35.34/5.00  --sat_out_model                         small
% 35.34/5.00  --sat_out_clauses                       false
% 35.34/5.00  
% 35.34/5.00  ------ QBF Options
% 35.34/5.00  
% 35.34/5.00  --qbf_mode                              false
% 35.34/5.00  --qbf_elim_univ                         false
% 35.34/5.00  --qbf_dom_inst                          none
% 35.34/5.00  --qbf_dom_pre_inst                      false
% 35.34/5.00  --qbf_sk_in                             false
% 35.34/5.00  --qbf_pred_elim                         true
% 35.34/5.00  --qbf_split                             512
% 35.34/5.00  
% 35.34/5.00  ------ BMC1 Options
% 35.34/5.00  
% 35.34/5.00  --bmc1_incremental                      false
% 35.34/5.00  --bmc1_axioms                           reachable_all
% 35.34/5.00  --bmc1_min_bound                        0
% 35.34/5.00  --bmc1_max_bound                        -1
% 35.34/5.00  --bmc1_max_bound_default                -1
% 35.34/5.00  --bmc1_symbol_reachability              true
% 35.34/5.00  --bmc1_property_lemmas                  false
% 35.34/5.00  --bmc1_k_induction                      false
% 35.34/5.00  --bmc1_non_equiv_states                 false
% 35.34/5.00  --bmc1_deadlock                         false
% 35.34/5.00  --bmc1_ucm                              false
% 35.34/5.00  --bmc1_add_unsat_core                   none
% 35.34/5.00  --bmc1_unsat_core_children              false
% 35.34/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.34/5.00  --bmc1_out_stat                         full
% 35.34/5.00  --bmc1_ground_init                      false
% 35.34/5.00  --bmc1_pre_inst_next_state              false
% 35.34/5.00  --bmc1_pre_inst_state                   false
% 35.34/5.00  --bmc1_pre_inst_reach_state             false
% 35.34/5.00  --bmc1_out_unsat_core                   false
% 35.34/5.00  --bmc1_aig_witness_out                  false
% 35.34/5.00  --bmc1_verbose                          false
% 35.34/5.00  --bmc1_dump_clauses_tptp                false
% 35.34/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.34/5.00  --bmc1_dump_file                        -
% 35.34/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.34/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.34/5.00  --bmc1_ucm_extend_mode                  1
% 35.34/5.00  --bmc1_ucm_init_mode                    2
% 35.34/5.00  --bmc1_ucm_cone_mode                    none
% 35.34/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.34/5.00  --bmc1_ucm_relax_model                  4
% 35.34/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.34/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.34/5.00  --bmc1_ucm_layered_model                none
% 35.34/5.00  --bmc1_ucm_max_lemma_size               10
% 35.34/5.00  
% 35.34/5.00  ------ AIG Options
% 35.34/5.00  
% 35.34/5.00  --aig_mode                              false
% 35.34/5.00  
% 35.34/5.00  ------ Instantiation Options
% 35.34/5.00  
% 35.34/5.00  --instantiation_flag                    true
% 35.34/5.00  --inst_sos_flag                         true
% 35.34/5.00  --inst_sos_phase                        true
% 35.34/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.34/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.34/5.00  --inst_lit_sel_side                     num_symb
% 35.34/5.00  --inst_solver_per_active                1400
% 35.34/5.00  --inst_solver_calls_frac                1.
% 35.34/5.00  --inst_passive_queue_type               priority_queues
% 35.34/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.34/5.00  --inst_passive_queues_freq              [25;2]
% 35.34/5.00  --inst_dismatching                      true
% 35.34/5.00  --inst_eager_unprocessed_to_passive     true
% 35.34/5.00  --inst_prop_sim_given                   true
% 35.34/5.00  --inst_prop_sim_new                     false
% 35.34/5.00  --inst_subs_new                         false
% 35.34/5.00  --inst_eq_res_simp                      false
% 35.34/5.00  --inst_subs_given                       false
% 35.34/5.00  --inst_orphan_elimination               true
% 35.34/5.00  --inst_learning_loop_flag               true
% 35.34/5.00  --inst_learning_start                   3000
% 35.34/5.00  --inst_learning_factor                  2
% 35.34/5.00  --inst_start_prop_sim_after_learn       3
% 35.34/5.00  --inst_sel_renew                        solver
% 35.34/5.00  --inst_lit_activity_flag                true
% 35.34/5.00  --inst_restr_to_given                   false
% 35.34/5.00  --inst_activity_threshold               500
% 35.34/5.00  --inst_out_proof                        true
% 35.34/5.00  
% 35.34/5.00  ------ Resolution Options
% 35.34/5.00  
% 35.34/5.00  --resolution_flag                       true
% 35.34/5.00  --res_lit_sel                           adaptive
% 35.34/5.00  --res_lit_sel_side                      none
% 35.34/5.00  --res_ordering                          kbo
% 35.34/5.00  --res_to_prop_solver                    active
% 35.34/5.00  --res_prop_simpl_new                    false
% 35.34/5.00  --res_prop_simpl_given                  true
% 35.34/5.00  --res_passive_queue_type                priority_queues
% 35.34/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.34/5.00  --res_passive_queues_freq               [15;5]
% 35.34/5.00  --res_forward_subs                      full
% 35.34/5.00  --res_backward_subs                     full
% 35.34/5.00  --res_forward_subs_resolution           true
% 35.34/5.00  --res_backward_subs_resolution          true
% 35.34/5.00  --res_orphan_elimination                true
% 35.34/5.00  --res_time_limit                        2.
% 35.34/5.00  --res_out_proof                         true
% 35.34/5.00  
% 35.34/5.00  ------ Superposition Options
% 35.34/5.00  
% 35.34/5.00  --superposition_flag                    true
% 35.34/5.00  --sup_passive_queue_type                priority_queues
% 35.34/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.34/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.34/5.00  --demod_completeness_check              fast
% 35.34/5.00  --demod_use_ground                      true
% 35.34/5.00  --sup_to_prop_solver                    passive
% 35.34/5.00  --sup_prop_simpl_new                    true
% 35.34/5.00  --sup_prop_simpl_given                  true
% 35.34/5.00  --sup_fun_splitting                     true
% 35.34/5.00  --sup_smt_interval                      50000
% 35.34/5.00  
% 35.34/5.00  ------ Superposition Simplification Setup
% 35.34/5.00  
% 35.34/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.34/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.34/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.34/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.34/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.34/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.34/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.34/5.00  --sup_immed_triv                        [TrivRules]
% 35.34/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.34/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.34/5.00  --sup_immed_bw_main                     []
% 35.34/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.34/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.34/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.34/5.00  --sup_input_bw                          []
% 35.34/5.00  
% 35.34/5.00  ------ Combination Options
% 35.34/5.00  
% 35.34/5.00  --comb_res_mult                         3
% 35.34/5.00  --comb_sup_mult                         2
% 35.34/5.00  --comb_inst_mult                        10
% 35.34/5.00  
% 35.34/5.00  ------ Debug Options
% 35.34/5.00  
% 35.34/5.00  --dbg_backtrace                         false
% 35.34/5.00  --dbg_dump_prop_clauses                 false
% 35.34/5.00  --dbg_dump_prop_clauses_file            -
% 35.34/5.00  --dbg_out_stat                          false
% 35.34/5.00  ------ Parsing...
% 35.34/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  ------ Proving...
% 35.34/5.00  ------ Problem Properties 
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  clauses                                 21
% 35.34/5.00  conjectures                             2
% 35.34/5.00  EPR                                     1
% 35.34/5.00  Horn                                    14
% 35.34/5.00  unary                                   7
% 35.34/5.00  binary                                  9
% 35.34/5.00  lits                                    41
% 35.34/5.00  lits eq                                 16
% 35.34/5.00  fd_pure                                 0
% 35.34/5.00  fd_pseudo                               0
% 35.34/5.00  fd_cond                                 0
% 35.34/5.00  fd_pseudo_cond                          4
% 35.34/5.00  AC symbols                              0
% 35.34/5.00  
% 35.34/5.00  ------ Schedule dynamic 5 is on 
% 35.34/5.00  
% 35.34/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ 
% 35.34/5.00  Current options:
% 35.34/5.00  ------ 
% 35.34/5.00  
% 35.34/5.00  ------ Input Options
% 35.34/5.00  
% 35.34/5.00  --out_options                           all
% 35.34/5.00  --tptp_safe_out                         true
% 35.34/5.00  --problem_path                          ""
% 35.34/5.00  --include_path                          ""
% 35.34/5.00  --clausifier                            res/vclausify_rel
% 35.34/5.00  --clausifier_options                    ""
% 35.34/5.00  --stdin                                 false
% 35.34/5.00  --stats_out                             all
% 35.34/5.00  
% 35.34/5.00  ------ General Options
% 35.34/5.00  
% 35.34/5.00  --fof                                   false
% 35.34/5.00  --time_out_real                         305.
% 35.34/5.00  --time_out_virtual                      -1.
% 35.34/5.00  --symbol_type_check                     false
% 35.34/5.00  --clausify_out                          false
% 35.34/5.00  --sig_cnt_out                           false
% 35.34/5.00  --trig_cnt_out                          false
% 35.34/5.00  --trig_cnt_out_tolerance                1.
% 35.34/5.00  --trig_cnt_out_sk_spl                   false
% 35.34/5.00  --abstr_cl_out                          false
% 35.34/5.00  
% 35.34/5.00  ------ Global Options
% 35.34/5.00  
% 35.34/5.00  --schedule                              default
% 35.34/5.00  --add_important_lit                     false
% 35.34/5.00  --prop_solver_per_cl                    1000
% 35.34/5.00  --min_unsat_core                        false
% 35.34/5.00  --soft_assumptions                      false
% 35.34/5.00  --soft_lemma_size                       3
% 35.34/5.00  --prop_impl_unit_size                   0
% 35.34/5.00  --prop_impl_unit                        []
% 35.34/5.00  --share_sel_clauses                     true
% 35.34/5.00  --reset_solvers                         false
% 35.34/5.00  --bc_imp_inh                            [conj_cone]
% 35.34/5.00  --conj_cone_tolerance                   3.
% 35.34/5.00  --extra_neg_conj                        none
% 35.34/5.00  --large_theory_mode                     true
% 35.34/5.00  --prolific_symb_bound                   200
% 35.34/5.00  --lt_threshold                          2000
% 35.34/5.00  --clause_weak_htbl                      true
% 35.34/5.00  --gc_record_bc_elim                     false
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing Options
% 35.34/5.00  
% 35.34/5.00  --preprocessing_flag                    true
% 35.34/5.00  --time_out_prep_mult                    0.1
% 35.34/5.00  --splitting_mode                        input
% 35.34/5.00  --splitting_grd                         true
% 35.34/5.00  --splitting_cvd                         false
% 35.34/5.00  --splitting_cvd_svl                     false
% 35.34/5.00  --splitting_nvd                         32
% 35.34/5.00  --sub_typing                            true
% 35.34/5.00  --prep_gs_sim                           true
% 35.34/5.00  --prep_unflatten                        true
% 35.34/5.00  --prep_res_sim                          true
% 35.34/5.00  --prep_upred                            true
% 35.34/5.00  --prep_sem_filter                       exhaustive
% 35.34/5.00  --prep_sem_filter_out                   false
% 35.34/5.00  --pred_elim                             true
% 35.34/5.00  --res_sim_input                         true
% 35.34/5.00  --eq_ax_congr_red                       true
% 35.34/5.00  --pure_diseq_elim                       true
% 35.34/5.00  --brand_transform                       false
% 35.34/5.00  --non_eq_to_eq                          false
% 35.34/5.00  --prep_def_merge                        true
% 35.34/5.00  --prep_def_merge_prop_impl              false
% 35.34/5.00  --prep_def_merge_mbd                    true
% 35.34/5.00  --prep_def_merge_tr_red                 false
% 35.34/5.00  --prep_def_merge_tr_cl                  false
% 35.34/5.00  --smt_preprocessing                     true
% 35.34/5.00  --smt_ac_axioms                         fast
% 35.34/5.00  --preprocessed_out                      false
% 35.34/5.00  --preprocessed_stats                    false
% 35.34/5.00  
% 35.34/5.00  ------ Abstraction refinement Options
% 35.34/5.00  
% 35.34/5.00  --abstr_ref                             []
% 35.34/5.00  --abstr_ref_prep                        false
% 35.34/5.00  --abstr_ref_until_sat                   false
% 35.34/5.00  --abstr_ref_sig_restrict                funpre
% 35.34/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.34/5.00  --abstr_ref_under                       []
% 35.34/5.00  
% 35.34/5.00  ------ SAT Options
% 35.34/5.00  
% 35.34/5.00  --sat_mode                              false
% 35.34/5.00  --sat_fm_restart_options                ""
% 35.34/5.00  --sat_gr_def                            false
% 35.34/5.00  --sat_epr_types                         true
% 35.34/5.00  --sat_non_cyclic_types                  false
% 35.34/5.00  --sat_finite_models                     false
% 35.34/5.00  --sat_fm_lemmas                         false
% 35.34/5.00  --sat_fm_prep                           false
% 35.34/5.00  --sat_fm_uc_incr                        true
% 35.34/5.00  --sat_out_model                         small
% 35.34/5.00  --sat_out_clauses                       false
% 35.34/5.00  
% 35.34/5.00  ------ QBF Options
% 35.34/5.00  
% 35.34/5.00  --qbf_mode                              false
% 35.34/5.00  --qbf_elim_univ                         false
% 35.34/5.00  --qbf_dom_inst                          none
% 35.34/5.00  --qbf_dom_pre_inst                      false
% 35.34/5.00  --qbf_sk_in                             false
% 35.34/5.00  --qbf_pred_elim                         true
% 35.34/5.00  --qbf_split                             512
% 35.34/5.00  
% 35.34/5.00  ------ BMC1 Options
% 35.34/5.00  
% 35.34/5.00  --bmc1_incremental                      false
% 35.34/5.00  --bmc1_axioms                           reachable_all
% 35.34/5.00  --bmc1_min_bound                        0
% 35.34/5.00  --bmc1_max_bound                        -1
% 35.34/5.00  --bmc1_max_bound_default                -1
% 35.34/5.00  --bmc1_symbol_reachability              true
% 35.34/5.00  --bmc1_property_lemmas                  false
% 35.34/5.00  --bmc1_k_induction                      false
% 35.34/5.00  --bmc1_non_equiv_states                 false
% 35.34/5.00  --bmc1_deadlock                         false
% 35.34/5.00  --bmc1_ucm                              false
% 35.34/5.00  --bmc1_add_unsat_core                   none
% 35.34/5.00  --bmc1_unsat_core_children              false
% 35.34/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.34/5.00  --bmc1_out_stat                         full
% 35.34/5.00  --bmc1_ground_init                      false
% 35.34/5.00  --bmc1_pre_inst_next_state              false
% 35.34/5.00  --bmc1_pre_inst_state                   false
% 35.34/5.00  --bmc1_pre_inst_reach_state             false
% 35.34/5.00  --bmc1_out_unsat_core                   false
% 35.34/5.00  --bmc1_aig_witness_out                  false
% 35.34/5.00  --bmc1_verbose                          false
% 35.34/5.00  --bmc1_dump_clauses_tptp                false
% 35.34/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.34/5.00  --bmc1_dump_file                        -
% 35.34/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.34/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.34/5.00  --bmc1_ucm_extend_mode                  1
% 35.34/5.00  --bmc1_ucm_init_mode                    2
% 35.34/5.00  --bmc1_ucm_cone_mode                    none
% 35.34/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.34/5.00  --bmc1_ucm_relax_model                  4
% 35.34/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.34/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.34/5.00  --bmc1_ucm_layered_model                none
% 35.34/5.00  --bmc1_ucm_max_lemma_size               10
% 35.34/5.00  
% 35.34/5.00  ------ AIG Options
% 35.34/5.00  
% 35.34/5.00  --aig_mode                              false
% 35.34/5.00  
% 35.34/5.00  ------ Instantiation Options
% 35.34/5.00  
% 35.34/5.00  --instantiation_flag                    true
% 35.34/5.00  --inst_sos_flag                         true
% 35.34/5.00  --inst_sos_phase                        true
% 35.34/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.34/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.34/5.00  --inst_lit_sel_side                     none
% 35.34/5.00  --inst_solver_per_active                1400
% 35.34/5.00  --inst_solver_calls_frac                1.
% 35.34/5.00  --inst_passive_queue_type               priority_queues
% 35.34/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.34/5.00  --inst_passive_queues_freq              [25;2]
% 35.34/5.00  --inst_dismatching                      true
% 35.34/5.00  --inst_eager_unprocessed_to_passive     true
% 35.34/5.00  --inst_prop_sim_given                   true
% 35.34/5.00  --inst_prop_sim_new                     false
% 35.34/5.00  --inst_subs_new                         false
% 35.34/5.00  --inst_eq_res_simp                      false
% 35.34/5.00  --inst_subs_given                       false
% 35.34/5.00  --inst_orphan_elimination               true
% 35.34/5.00  --inst_learning_loop_flag               true
% 35.34/5.00  --inst_learning_start                   3000
% 35.34/5.00  --inst_learning_factor                  2
% 35.34/5.00  --inst_start_prop_sim_after_learn       3
% 35.34/5.00  --inst_sel_renew                        solver
% 35.34/5.00  --inst_lit_activity_flag                true
% 35.34/5.00  --inst_restr_to_given                   false
% 35.34/5.00  --inst_activity_threshold               500
% 35.34/5.00  --inst_out_proof                        true
% 35.34/5.00  
% 35.34/5.00  ------ Resolution Options
% 35.34/5.00  
% 35.34/5.00  --resolution_flag                       false
% 35.34/5.00  --res_lit_sel                           adaptive
% 35.34/5.00  --res_lit_sel_side                      none
% 35.34/5.00  --res_ordering                          kbo
% 35.34/5.00  --res_to_prop_solver                    active
% 35.34/5.00  --res_prop_simpl_new                    false
% 35.34/5.00  --res_prop_simpl_given                  true
% 35.34/5.00  --res_passive_queue_type                priority_queues
% 35.34/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.34/5.00  --res_passive_queues_freq               [15;5]
% 35.34/5.00  --res_forward_subs                      full
% 35.34/5.00  --res_backward_subs                     full
% 35.34/5.00  --res_forward_subs_resolution           true
% 35.34/5.00  --res_backward_subs_resolution          true
% 35.34/5.00  --res_orphan_elimination                true
% 35.34/5.00  --res_time_limit                        2.
% 35.34/5.00  --res_out_proof                         true
% 35.34/5.00  
% 35.34/5.00  ------ Superposition Options
% 35.34/5.00  
% 35.34/5.00  --superposition_flag                    true
% 35.34/5.00  --sup_passive_queue_type                priority_queues
% 35.34/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.34/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.34/5.00  --demod_completeness_check              fast
% 35.34/5.00  --demod_use_ground                      true
% 35.34/5.00  --sup_to_prop_solver                    passive
% 35.34/5.00  --sup_prop_simpl_new                    true
% 35.34/5.00  --sup_prop_simpl_given                  true
% 35.34/5.00  --sup_fun_splitting                     true
% 35.34/5.00  --sup_smt_interval                      50000
% 35.34/5.00  
% 35.34/5.00  ------ Superposition Simplification Setup
% 35.34/5.00  
% 35.34/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.34/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.34/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.34/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.34/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.34/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.34/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.34/5.00  --sup_immed_triv                        [TrivRules]
% 35.34/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.34/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.34/5.00  --sup_immed_bw_main                     []
% 35.34/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.34/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.34/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.34/5.00  --sup_input_bw                          []
% 35.34/5.00  
% 35.34/5.00  ------ Combination Options
% 35.34/5.00  
% 35.34/5.00  --comb_res_mult                         3
% 35.34/5.00  --comb_sup_mult                         2
% 35.34/5.00  --comb_inst_mult                        10
% 35.34/5.00  
% 35.34/5.00  ------ Debug Options
% 35.34/5.00  
% 35.34/5.00  --dbg_backtrace                         false
% 35.34/5.00  --dbg_dump_prop_clauses                 false
% 35.34/5.00  --dbg_dump_prop_clauses_file            -
% 35.34/5.00  --dbg_out_stat                          false
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  % SZS status Theorem for theBenchmark.p
% 35.34/5.00  
% 35.34/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.34/5.00  
% 35.34/5.00  fof(f2,axiom,(
% 35.34/5.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f22,plain,(
% 35.34/5.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 35.34/5.00    inference(nnf_transformation,[],[f2])).
% 35.34/5.00  
% 35.34/5.00  fof(f23,plain,(
% 35.34/5.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 35.34/5.00    inference(flattening,[],[f22])).
% 35.34/5.00  
% 35.34/5.00  fof(f24,plain,(
% 35.34/5.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 35.34/5.00    inference(rectify,[],[f23])).
% 35.34/5.00  
% 35.34/5.00  fof(f25,plain,(
% 35.34/5.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.34/5.00    introduced(choice_axiom,[])).
% 35.34/5.00  
% 35.34/5.00  fof(f26,plain,(
% 35.34/5.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 35.34/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 35.34/5.00  
% 35.34/5.00  fof(f35,plain,(
% 35.34/5.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 35.34/5.00    inference(cnf_transformation,[],[f26])).
% 35.34/5.00  
% 35.34/5.00  fof(f3,axiom,(
% 35.34/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f40,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.34/5.00    inference(cnf_transformation,[],[f3])).
% 35.34/5.00  
% 35.34/5.00  fof(f67,plain,(
% 35.34/5.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 35.34/5.00    inference(definition_unfolding,[],[f35,f40])).
% 35.34/5.00  
% 35.34/5.00  fof(f83,plain,(
% 35.34/5.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 35.34/5.00    inference(equality_resolution,[],[f67])).
% 35.34/5.00  
% 35.34/5.00  fof(f14,axiom,(
% 35.34/5.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f28,plain,(
% 35.34/5.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 35.34/5.00    inference(nnf_transformation,[],[f14])).
% 35.34/5.00  
% 35.34/5.00  fof(f29,plain,(
% 35.34/5.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 35.34/5.00    inference(flattening,[],[f28])).
% 35.34/5.00  
% 35.34/5.00  fof(f54,plain,(
% 35.34/5.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f29])).
% 35.34/5.00  
% 35.34/5.00  fof(f9,axiom,(
% 35.34/5.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f46,plain,(
% 35.34/5.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f9])).
% 35.34/5.00  
% 35.34/5.00  fof(f10,axiom,(
% 35.34/5.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f47,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f10])).
% 35.34/5.00  
% 35.34/5.00  fof(f11,axiom,(
% 35.34/5.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f48,plain,(
% 35.34/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f11])).
% 35.34/5.00  
% 35.34/5.00  fof(f59,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 35.34/5.00    inference(definition_unfolding,[],[f47,f48])).
% 35.34/5.00  
% 35.34/5.00  fof(f61,plain,(
% 35.34/5.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.34/5.00    inference(definition_unfolding,[],[f46,f59])).
% 35.34/5.00  
% 35.34/5.00  fof(f76,plain,(
% 35.34/5.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 35.34/5.00    inference(definition_unfolding,[],[f54,f40,f61])).
% 35.34/5.00  
% 35.34/5.00  fof(f12,axiom,(
% 35.34/5.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f27,plain,(
% 35.34/5.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 35.34/5.00    inference(nnf_transformation,[],[f12])).
% 35.34/5.00  
% 35.34/5.00  fof(f50,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f27])).
% 35.34/5.00  
% 35.34/5.00  fof(f74,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 35.34/5.00    inference(definition_unfolding,[],[f50,f40,f61,f61])).
% 35.34/5.00  
% 35.34/5.00  fof(f7,axiom,(
% 35.34/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f18,plain,(
% 35.34/5.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 35.34/5.00    inference(unused_predicate_definition_removal,[],[f7])).
% 35.34/5.00  
% 35.34/5.00  fof(f19,plain,(
% 35.34/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 35.34/5.00    inference(ennf_transformation,[],[f18])).
% 35.34/5.00  
% 35.34/5.00  fof(f44,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 35.34/5.00    inference(cnf_transformation,[],[f19])).
% 35.34/5.00  
% 35.34/5.00  fof(f72,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 35.34/5.00    inference(definition_unfolding,[],[f44,f40])).
% 35.34/5.00  
% 35.34/5.00  fof(f8,axiom,(
% 35.34/5.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f20,plain,(
% 35.34/5.00    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 35.34/5.00    inference(ennf_transformation,[],[f8])).
% 35.34/5.00  
% 35.34/5.00  fof(f45,plain,(
% 35.34/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f20])).
% 35.34/5.00  
% 35.34/5.00  fof(f13,axiom,(
% 35.34/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f51,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.34/5.00    inference(cnf_transformation,[],[f13])).
% 35.34/5.00  
% 35.34/5.00  fof(f60,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 35.34/5.00    inference(definition_unfolding,[],[f51,f59])).
% 35.34/5.00  
% 35.34/5.00  fof(f73,plain,(
% 35.34/5.00    ( ! [X2,X0,X1] : (k5_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),X0)) = k3_tarski(k2_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) | ~r1_xboole_0(X0,X1)) )),
% 35.34/5.00    inference(definition_unfolding,[],[f45,f60,f40,f40,f60])).
% 35.34/5.00  
% 35.34/5.00  fof(f16,conjecture,(
% 35.34/5.00    ! [X0,X1,X2] : (X0 != X1 => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)))),
% 35.34/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f17,negated_conjecture,(
% 35.34/5.00    ~! [X0,X1,X2] : (X0 != X1 => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)))),
% 35.34/5.00    inference(negated_conjecture,[],[f16])).
% 35.34/5.00  
% 35.34/5.00  fof(f21,plain,(
% 35.34/5.00    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) & X0 != X1)),
% 35.34/5.00    inference(ennf_transformation,[],[f17])).
% 35.34/5.00  
% 35.34/5.00  fof(f31,plain,(
% 35.34/5.00    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) & X0 != X1) => (k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) & sK1 != sK2)),
% 35.34/5.00    introduced(choice_axiom,[])).
% 35.34/5.00  
% 35.34/5.00  fof(f32,plain,(
% 35.34/5.00    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) & sK1 != sK2),
% 35.34/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f31])).
% 35.34/5.00  
% 35.34/5.00  fof(f58,plain,(
% 35.34/5.00    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))),
% 35.34/5.00    inference(cnf_transformation,[],[f32])).
% 35.34/5.00  
% 35.34/5.00  fof(f81,plain,(
% 35.34/5.00    k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 35.34/5.00    inference(definition_unfolding,[],[f58,f60,f40,f61,f61,f40,f60,f61,f61])).
% 35.34/5.00  
% 35.34/5.00  fof(f57,plain,(
% 35.34/5.00    sK1 != sK2),
% 35.34/5.00    inference(cnf_transformation,[],[f32])).
% 35.34/5.00  
% 35.34/5.00  cnf(c_5,plain,
% 35.34/5.00      ( ~ r2_hidden(X0,X1)
% 35.34/5.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 35.34/5.00      inference(cnf_transformation,[],[f83]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_3468,plain,
% 35.34/5.00      ( ~ r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
% 35.34/5.00      | ~ r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_60983,plain,
% 35.34/5.00      ( ~ r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
% 35.34/5.00      | ~ r2_hidden(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)))) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_3468]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_14,plain,
% 35.34/5.00      ( ~ r2_hidden(X0,X1)
% 35.34/5.00      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
% 35.34/5.00      | X2 = X0 ),
% 35.34/5.00      inference(cnf_transformation,[],[f76]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_641,plain,
% 35.34/5.00      ( ~ r2_hidden(sK2,X0)
% 35.34/5.00      | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK1))))
% 35.34/5.00      | sK1 = sK2 ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_14]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_22247,plain,
% 35.34/5.00      ( ~ r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
% 35.34/5.00      | r2_hidden(sK2,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))))
% 35.34/5.00      | sK1 = sK2 ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_641]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_12,plain,
% 35.34/5.00      ( r2_hidden(X0,X1)
% 35.34/5.00      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 35.34/5.00      inference(cnf_transformation,[],[f74]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_833,plain,
% 35.34/5.00      ( r2_hidden(sK2,X0)
% 35.34/5.00      | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),X0)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_12]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_1161,plain,
% 35.34/5.00      ( r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0))
% 35.34/5.00      | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_833]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_10787,plain,
% 35.34/5.00      ( r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
% 35.34/5.00      | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_1161]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_10,plain,
% 35.34/5.00      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 35.34/5.00      inference(cnf_transformation,[],[f72]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_2286,plain,
% 35.34/5.00      ( r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
% 35.34/5.00      | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))) != k2_enumset1(sK2,sK2,sK2,sK2) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_10]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_11,plain,
% 35.34/5.00      ( ~ r1_xboole_0(X0,X1)
% 35.34/5.00      | k3_tarski(k2_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) = k5_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k2_enumset1(X2,X2,X2,X1)),X0)) ),
% 35.34/5.00      inference(cnf_transformation,[],[f73]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_1337,plain,
% 35.34/5.00      ( ~ r1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))
% 35.34/5.00      | k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_11]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_240,plain,( X0 = X0 ),theory(equality) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_949,plain,
% 35.34/5.00      ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) = k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_240]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_241,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_631,plain,
% 35.34/5.00      ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != X0
% 35.34/5.00      | k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) = k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1)))
% 35.34/5.00      | k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) != X0 ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_241]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_778,plain,
% 35.34/5.00      ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2)))
% 35.34/5.00      | k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) = k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1)))
% 35.34/5.00      | k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) != k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_631]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_19,negated_conjecture,
% 35.34/5.00      ( k5_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k3_xboole_0(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK1,sK1,sK1,sK1))),k2_enumset1(sK2,sK2,sK2,sK2))) != k3_tarski(k2_enumset1(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK1,sK1,sK1,sK1))) ),
% 35.34/5.01      inference(cnf_transformation,[],[f81]) ).
% 35.34/5.01  
% 35.34/5.01  cnf(c_20,negated_conjecture,
% 35.34/5.01      ( sK1 != sK2 ),
% 35.34/5.01      inference(cnf_transformation,[],[f57]) ).
% 35.34/5.01  
% 35.34/5.01  cnf(contradiction,plain,
% 35.34/5.01      ( $false ),
% 35.34/5.01      inference(minisat,
% 35.34/5.01                [status(thm)],
% 35.34/5.01                [c_60983,c_22247,c_10787,c_2286,c_1337,c_949,c_778,c_19,
% 35.34/5.01                 c_20]) ).
% 35.34/5.01  
% 35.34/5.01  
% 35.34/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.34/5.01  
% 35.34/5.01  ------                               Statistics
% 35.34/5.01  
% 35.34/5.01  ------ General
% 35.34/5.01  
% 35.34/5.01  abstr_ref_over_cycles:                  0
% 35.34/5.01  abstr_ref_under_cycles:                 0
% 35.34/5.01  gc_basic_clause_elim:                   0
% 35.34/5.01  forced_gc_time:                         0
% 35.34/5.01  parsing_time:                           0.011
% 35.34/5.01  unif_index_cands_time:                  0.
% 35.34/5.01  unif_index_add_time:                    0.
% 35.34/5.01  orderings_time:                         0.
% 35.34/5.01  out_proof_time:                         0.012
% 35.34/5.01  total_time:                             4.181
% 35.34/5.01  num_of_symbols:                         41
% 35.34/5.01  num_of_terms:                           111500
% 35.34/5.01  
% 35.34/5.01  ------ Preprocessing
% 35.34/5.01  
% 35.34/5.01  num_of_splits:                          0
% 35.34/5.01  num_of_split_atoms:                     0
% 35.34/5.01  num_of_reused_defs:                     0
% 35.34/5.01  num_eq_ax_congr_red:                    10
% 35.34/5.01  num_of_sem_filtered_clauses:            1
% 35.34/5.01  num_of_subtypes:                        0
% 35.34/5.01  monotx_restored_types:                  0
% 35.34/5.01  sat_num_of_epr_types:                   0
% 35.34/5.01  sat_num_of_non_cyclic_types:            0
% 35.34/5.01  sat_guarded_non_collapsed_types:        0
% 35.34/5.01  num_pure_diseq_elim:                    0
% 35.34/5.01  simp_replaced_by:                       0
% 35.34/5.01  res_preprocessed:                       78
% 35.34/5.01  prep_upred:                             0
% 35.34/5.01  prep_unflattend:                        0
% 35.34/5.01  smt_new_axioms:                         0
% 35.34/5.01  pred_elim_cands:                        2
% 35.34/5.01  pred_elim:                              0
% 35.34/5.01  pred_elim_cl:                           0
% 35.34/5.01  pred_elim_cycles:                       1
% 35.34/5.01  merged_defs:                            12
% 35.34/5.01  merged_defs_ncl:                        0
% 35.34/5.01  bin_hyper_res:                          12
% 35.34/5.01  prep_cycles:                            3
% 35.34/5.01  pred_elim_time:                         0.
% 35.34/5.01  splitting_time:                         0.
% 35.34/5.01  sem_filter_time:                        0.
% 35.34/5.01  monotx_time:                            0.
% 35.34/5.01  subtype_inf_time:                       0.
% 35.34/5.01  
% 35.34/5.01  ------ Problem properties
% 35.34/5.01  
% 35.34/5.01  clauses:                                21
% 35.34/5.01  conjectures:                            2
% 35.34/5.01  epr:                                    1
% 35.34/5.01  horn:                                   14
% 35.34/5.01  ground:                                 2
% 35.34/5.01  unary:                                  7
% 35.34/5.01  binary:                                 9
% 35.34/5.01  lits:                                   41
% 35.34/5.01  lits_eq:                                16
% 35.34/5.01  fd_pure:                                0
% 35.34/5.01  fd_pseudo:                              0
% 35.34/5.01  fd_cond:                                0
% 35.34/5.01  fd_pseudo_cond:                         4
% 35.34/5.01  ac_symbols:                             0
% 35.34/5.01  
% 35.34/5.01  ------ Propositional Solver
% 35.34/5.01  
% 35.34/5.01  prop_solver_calls:                      27
% 35.34/5.01  prop_fast_solver_calls:                 707
% 35.34/5.01  smt_solver_calls:                       0
% 35.34/5.01  smt_fast_solver_calls:                  0
% 35.34/5.01  prop_num_of_clauses:                    24207
% 35.34/5.01  prop_preprocess_simplified:             29699
% 35.34/5.01  prop_fo_subsumed:                       3
% 35.34/5.01  prop_solver_time:                       0.
% 35.34/5.01  smt_solver_time:                        0.
% 35.34/5.01  smt_fast_solver_time:                   0.
% 35.34/5.01  prop_fast_solver_time:                  0.
% 35.34/5.01  prop_unsat_core_time:                   0.002
% 35.34/5.01  
% 35.34/5.01  ------ QBF
% 35.34/5.01  
% 35.34/5.01  qbf_q_res:                              0
% 35.34/5.01  qbf_num_tautologies:                    0
% 35.34/5.01  qbf_prep_cycles:                        0
% 35.34/5.01  
% 35.34/5.01  ------ BMC1
% 35.34/5.01  
% 35.34/5.01  bmc1_current_bound:                     -1
% 35.34/5.01  bmc1_last_solved_bound:                 -1
% 35.34/5.01  bmc1_unsat_core_size:                   -1
% 35.34/5.01  bmc1_unsat_core_parents_size:           -1
% 35.34/5.01  bmc1_merge_next_fun:                    0
% 35.34/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.34/5.01  
% 35.34/5.01  ------ Instantiation
% 35.34/5.01  
% 35.34/5.01  inst_num_of_clauses:                    3142
% 35.34/5.01  inst_num_in_passive:                    2163
% 35.34/5.01  inst_num_in_active:                     883
% 35.34/5.01  inst_num_in_unprocessed:                95
% 35.34/5.01  inst_num_of_loops:                      1355
% 35.34/5.01  inst_num_of_learning_restarts:          0
% 35.34/5.01  inst_num_moves_active_passive:          471
% 35.34/5.01  inst_lit_activity:                      0
% 35.34/5.01  inst_lit_activity_moves:                0
% 35.34/5.01  inst_num_tautologies:                   0
% 35.34/5.01  inst_num_prop_implied:                  0
% 35.34/5.01  inst_num_existing_simplified:           0
% 35.34/5.01  inst_num_eq_res_simplified:             0
% 35.34/5.01  inst_num_child_elim:                    0
% 35.34/5.01  inst_num_of_dismatching_blockings:      5196
% 35.34/5.01  inst_num_of_non_proper_insts:           3550
% 35.34/5.01  inst_num_of_duplicates:                 0
% 35.34/5.01  inst_inst_num_from_inst_to_res:         0
% 35.34/5.01  inst_dismatching_checking_time:         0.
% 35.34/5.01  
% 35.34/5.01  ------ Resolution
% 35.34/5.01  
% 35.34/5.01  res_num_of_clauses:                     0
% 35.34/5.01  res_num_in_passive:                     0
% 35.34/5.01  res_num_in_active:                      0
% 35.34/5.01  res_num_of_loops:                       81
% 35.34/5.01  res_forward_subset_subsumed:            469
% 35.34/5.01  res_backward_subset_subsumed:           0
% 35.34/5.01  res_forward_subsumed:                   0
% 35.34/5.01  res_backward_subsumed:                  0
% 35.34/5.01  res_forward_subsumption_resolution:     0
% 35.34/5.01  res_backward_subsumption_resolution:    0
% 35.34/5.01  res_clause_to_clause_subsumption:       167359
% 35.34/5.01  res_orphan_elimination:                 0
% 35.34/5.01  res_tautology_del:                      185
% 35.34/5.01  res_num_eq_res_simplified:              0
% 35.34/5.01  res_num_sel_changes:                    0
% 35.34/5.01  res_moves_from_active_to_pass:          0
% 35.34/5.01  
% 35.34/5.01  ------ Superposition
% 35.34/5.01  
% 35.34/5.01  sup_time_total:                         0.
% 35.34/5.01  sup_time_generating:                    0.
% 35.34/5.01  sup_time_sim_full:                      0.
% 35.34/5.01  sup_time_sim_immed:                     0.
% 35.34/5.01  
% 35.34/5.01  sup_num_of_clauses:                     5437
% 35.34/5.01  sup_num_in_active:                      254
% 35.34/5.01  sup_num_in_passive:                     5183
% 35.34/5.01  sup_num_of_loops:                       270
% 35.34/5.01  sup_fw_superposition:                   9661
% 35.34/5.01  sup_bw_superposition:                   7786
% 35.34/5.01  sup_immediate_simplified:               6185
% 35.34/5.01  sup_given_eliminated:                   0
% 35.34/5.01  comparisons_done:                       0
% 35.34/5.01  comparisons_avoided:                    0
% 35.34/5.01  
% 35.34/5.01  ------ Simplifications
% 35.34/5.01  
% 35.34/5.01  
% 35.34/5.01  sim_fw_subset_subsumed:                 58
% 35.34/5.01  sim_bw_subset_subsumed:                 46
% 35.34/5.01  sim_fw_subsumed:                        1348
% 35.34/5.01  sim_bw_subsumed:                        152
% 35.34/5.01  sim_fw_subsumption_res:                 0
% 35.34/5.01  sim_bw_subsumption_res:                 0
% 35.34/5.01  sim_tautology_del:                      34
% 35.34/5.01  sim_eq_tautology_del:                   80
% 35.34/5.01  sim_eq_res_simp:                        2
% 35.34/5.01  sim_fw_demodulated:                     5160
% 35.34/5.01  sim_bw_demodulated:                     108
% 35.34/5.01  sim_light_normalised:                   993
% 35.34/5.01  sim_joinable_taut:                      0
% 35.34/5.01  sim_joinable_simp:                      0
% 35.34/5.01  sim_ac_normalised:                      0
% 35.34/5.01  sim_smt_subsumption:                    0
% 35.34/5.01  
%------------------------------------------------------------------------------
