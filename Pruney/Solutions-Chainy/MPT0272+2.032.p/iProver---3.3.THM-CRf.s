%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:16 EST 2020

% Result     : Theorem 6.68s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 820 expanded)
%              Number of clauses        :   57 ( 225 expanded)
%              Number of leaves         :   16 ( 197 expanded)
%              Depth                    :   18
%              Number of atoms          :  343 (2373 expanded)
%              Number of equality atoms :  184 (1067 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f38,f38])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f73,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
   => ( k4_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2)
      & k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k4_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2)
    & k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f25])).

fof(f47,plain,(
    k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f47,f38,f49])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f48,plain,(
    k4_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != k1_enumset1(sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f48,f38,f49,f49])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_668,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_663,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_662,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1387,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_663,c_662])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1393,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1387,c_0])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1394,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1393,c_12])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_666,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2039,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_666])).

cnf(c_1395,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1394,c_1387])).

cnf(c_2040,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2039,c_1395])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_665,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1668,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_665])).

cnf(c_1669,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1668,c_1395])).

cnf(c_2077,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2040,c_1669])).

cnf(c_3197,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_2077])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_657,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5634,plain,
    ( sK0(k1_enumset1(X0,X0,X0),X1,k1_xboole_0) = X0
    | k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3197,c_657])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13379,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_5634,c_18])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_669,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13506,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_xboole_0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13379,c_669])).

cnf(c_13512,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13506,c_13379])).

cnf(c_343,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3093,plain,
    ( X0 != X1
    | X0 = sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_3094,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) != sK2
    | sK2 = sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3093])).

cnf(c_342,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2682,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_2080,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1403,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | X0 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1915,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | X0 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_1916,plain,
    ( X0 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
    | sK3 != sK3
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_1918,plain,
    ( sK3 != sK3
    | sK2 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_1630,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(X0,X0,X0))
    | sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1632,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_909,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_713,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_804,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_685,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_692,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2)
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_687,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_688,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2)
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_20,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != k1_enumset1(sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13512,c_3094,c_2682,c_2080,c_1918,c_1632,c_909,c_804,c_692,c_688,c_687,c_23,c_20,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.68/1.54  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.68/1.54  
% 6.68/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.68/1.54  
% 6.68/1.54  ------  iProver source info
% 6.68/1.54  
% 6.68/1.54  git: date: 2020-06-30 10:37:57 +0100
% 6.68/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.68/1.54  git: non_committed_changes: false
% 6.68/1.54  git: last_make_outside_of_git: false
% 6.68/1.54  
% 6.68/1.54  ------ 
% 6.68/1.54  
% 6.68/1.54  ------ Input Options
% 6.68/1.54  
% 6.68/1.54  --out_options                           all
% 6.68/1.54  --tptp_safe_out                         true
% 6.68/1.54  --problem_path                          ""
% 6.68/1.54  --include_path                          ""
% 6.68/1.54  --clausifier                            res/vclausify_rel
% 6.68/1.54  --clausifier_options                    ""
% 6.68/1.54  --stdin                                 false
% 6.68/1.54  --stats_out                             all
% 6.68/1.54  
% 6.68/1.54  ------ General Options
% 6.68/1.54  
% 6.68/1.54  --fof                                   false
% 6.68/1.54  --time_out_real                         305.
% 6.68/1.54  --time_out_virtual                      -1.
% 6.68/1.54  --symbol_type_check                     false
% 6.68/1.54  --clausify_out                          false
% 6.68/1.54  --sig_cnt_out                           false
% 6.68/1.54  --trig_cnt_out                          false
% 6.68/1.54  --trig_cnt_out_tolerance                1.
% 6.68/1.54  --trig_cnt_out_sk_spl                   false
% 6.68/1.54  --abstr_cl_out                          false
% 6.68/1.54  
% 6.68/1.54  ------ Global Options
% 6.68/1.54  
% 6.68/1.54  --schedule                              default
% 6.68/1.54  --add_important_lit                     false
% 6.68/1.54  --prop_solver_per_cl                    1000
% 6.68/1.54  --min_unsat_core                        false
% 6.68/1.54  --soft_assumptions                      false
% 6.68/1.54  --soft_lemma_size                       3
% 6.68/1.54  --prop_impl_unit_size                   0
% 6.68/1.54  --prop_impl_unit                        []
% 6.68/1.54  --share_sel_clauses                     true
% 6.68/1.54  --reset_solvers                         false
% 6.68/1.54  --bc_imp_inh                            [conj_cone]
% 6.68/1.54  --conj_cone_tolerance                   3.
% 6.68/1.54  --extra_neg_conj                        none
% 6.68/1.54  --large_theory_mode                     true
% 6.68/1.54  --prolific_symb_bound                   200
% 6.68/1.54  --lt_threshold                          2000
% 6.68/1.54  --clause_weak_htbl                      true
% 6.68/1.54  --gc_record_bc_elim                     false
% 6.68/1.54  
% 6.68/1.54  ------ Preprocessing Options
% 6.68/1.54  
% 6.68/1.54  --preprocessing_flag                    true
% 6.68/1.54  --time_out_prep_mult                    0.1
% 6.68/1.54  --splitting_mode                        input
% 6.68/1.54  --splitting_grd                         true
% 6.68/1.54  --splitting_cvd                         false
% 6.68/1.54  --splitting_cvd_svl                     false
% 6.68/1.54  --splitting_nvd                         32
% 6.68/1.54  --sub_typing                            true
% 6.68/1.54  --prep_gs_sim                           true
% 6.68/1.54  --prep_unflatten                        true
% 6.68/1.54  --prep_res_sim                          true
% 6.68/1.54  --prep_upred                            true
% 6.68/1.54  --prep_sem_filter                       exhaustive
% 6.68/1.54  --prep_sem_filter_out                   false
% 6.68/1.54  --pred_elim                             true
% 6.68/1.54  --res_sim_input                         true
% 6.68/1.54  --eq_ax_congr_red                       true
% 6.68/1.54  --pure_diseq_elim                       true
% 6.68/1.54  --brand_transform                       false
% 6.68/1.54  --non_eq_to_eq                          false
% 6.68/1.54  --prep_def_merge                        true
% 6.68/1.54  --prep_def_merge_prop_impl              false
% 6.68/1.54  --prep_def_merge_mbd                    true
% 6.68/1.54  --prep_def_merge_tr_red                 false
% 6.68/1.54  --prep_def_merge_tr_cl                  false
% 6.68/1.54  --smt_preprocessing                     true
% 6.68/1.54  --smt_ac_axioms                         fast
% 6.68/1.54  --preprocessed_out                      false
% 6.68/1.54  --preprocessed_stats                    false
% 6.68/1.54  
% 6.68/1.54  ------ Abstraction refinement Options
% 6.68/1.54  
% 6.68/1.54  --abstr_ref                             []
% 6.68/1.54  --abstr_ref_prep                        false
% 6.68/1.54  --abstr_ref_until_sat                   false
% 6.68/1.54  --abstr_ref_sig_restrict                funpre
% 6.68/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.68/1.54  --abstr_ref_under                       []
% 6.68/1.54  
% 6.68/1.54  ------ SAT Options
% 6.68/1.54  
% 6.68/1.54  --sat_mode                              false
% 6.68/1.54  --sat_fm_restart_options                ""
% 6.68/1.54  --sat_gr_def                            false
% 6.68/1.54  --sat_epr_types                         true
% 6.68/1.54  --sat_non_cyclic_types                  false
% 6.68/1.54  --sat_finite_models                     false
% 6.68/1.54  --sat_fm_lemmas                         false
% 6.68/1.54  --sat_fm_prep                           false
% 6.68/1.54  --sat_fm_uc_incr                        true
% 6.68/1.54  --sat_out_model                         small
% 6.68/1.54  --sat_out_clauses                       false
% 6.68/1.54  
% 6.68/1.54  ------ QBF Options
% 6.68/1.54  
% 6.68/1.54  --qbf_mode                              false
% 6.68/1.54  --qbf_elim_univ                         false
% 6.68/1.54  --qbf_dom_inst                          none
% 6.68/1.54  --qbf_dom_pre_inst                      false
% 6.68/1.54  --qbf_sk_in                             false
% 6.68/1.54  --qbf_pred_elim                         true
% 6.68/1.54  --qbf_split                             512
% 6.68/1.54  
% 6.68/1.54  ------ BMC1 Options
% 6.68/1.54  
% 6.68/1.54  --bmc1_incremental                      false
% 6.68/1.54  --bmc1_axioms                           reachable_all
% 6.68/1.54  --bmc1_min_bound                        0
% 6.68/1.54  --bmc1_max_bound                        -1
% 6.68/1.54  --bmc1_max_bound_default                -1
% 6.68/1.54  --bmc1_symbol_reachability              true
% 6.68/1.54  --bmc1_property_lemmas                  false
% 6.68/1.54  --bmc1_k_induction                      false
% 6.68/1.54  --bmc1_non_equiv_states                 false
% 6.68/1.54  --bmc1_deadlock                         false
% 6.68/1.54  --bmc1_ucm                              false
% 6.68/1.54  --bmc1_add_unsat_core                   none
% 6.68/1.54  --bmc1_unsat_core_children              false
% 6.68/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.68/1.54  --bmc1_out_stat                         full
% 6.68/1.54  --bmc1_ground_init                      false
% 6.68/1.54  --bmc1_pre_inst_next_state              false
% 6.68/1.54  --bmc1_pre_inst_state                   false
% 6.68/1.54  --bmc1_pre_inst_reach_state             false
% 6.68/1.54  --bmc1_out_unsat_core                   false
% 6.68/1.54  --bmc1_aig_witness_out                  false
% 6.68/1.54  --bmc1_verbose                          false
% 6.68/1.54  --bmc1_dump_clauses_tptp                false
% 6.68/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.68/1.54  --bmc1_dump_file                        -
% 6.68/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.68/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.68/1.54  --bmc1_ucm_extend_mode                  1
% 6.68/1.54  --bmc1_ucm_init_mode                    2
% 6.68/1.54  --bmc1_ucm_cone_mode                    none
% 6.68/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.68/1.54  --bmc1_ucm_relax_model                  4
% 6.68/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.68/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.68/1.54  --bmc1_ucm_layered_model                none
% 6.68/1.54  --bmc1_ucm_max_lemma_size               10
% 6.68/1.54  
% 6.68/1.54  ------ AIG Options
% 6.68/1.54  
% 6.68/1.54  --aig_mode                              false
% 6.68/1.54  
% 6.68/1.54  ------ Instantiation Options
% 6.68/1.54  
% 6.68/1.54  --instantiation_flag                    true
% 6.68/1.54  --inst_sos_flag                         true
% 6.68/1.54  --inst_sos_phase                        true
% 6.68/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.68/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.68/1.54  --inst_lit_sel_side                     num_symb
% 6.68/1.54  --inst_solver_per_active                1400
% 6.68/1.54  --inst_solver_calls_frac                1.
% 6.68/1.54  --inst_passive_queue_type               priority_queues
% 6.68/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.68/1.54  --inst_passive_queues_freq              [25;2]
% 6.68/1.54  --inst_dismatching                      true
% 6.68/1.54  --inst_eager_unprocessed_to_passive     true
% 6.68/1.54  --inst_prop_sim_given                   true
% 6.68/1.54  --inst_prop_sim_new                     false
% 6.68/1.54  --inst_subs_new                         false
% 6.68/1.54  --inst_eq_res_simp                      false
% 6.68/1.54  --inst_subs_given                       false
% 6.68/1.54  --inst_orphan_elimination               true
% 6.68/1.54  --inst_learning_loop_flag               true
% 6.68/1.54  --inst_learning_start                   3000
% 6.68/1.54  --inst_learning_factor                  2
% 6.68/1.54  --inst_start_prop_sim_after_learn       3
% 6.68/1.54  --inst_sel_renew                        solver
% 6.68/1.54  --inst_lit_activity_flag                true
% 6.68/1.54  --inst_restr_to_given                   false
% 6.68/1.54  --inst_activity_threshold               500
% 6.68/1.54  --inst_out_proof                        true
% 6.68/1.54  
% 6.68/1.54  ------ Resolution Options
% 6.68/1.54  
% 6.68/1.54  --resolution_flag                       true
% 6.68/1.54  --res_lit_sel                           adaptive
% 6.68/1.54  --res_lit_sel_side                      none
% 6.68/1.54  --res_ordering                          kbo
% 6.68/1.54  --res_to_prop_solver                    active
% 6.68/1.54  --res_prop_simpl_new                    false
% 6.68/1.54  --res_prop_simpl_given                  true
% 6.68/1.54  --res_passive_queue_type                priority_queues
% 6.68/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.68/1.54  --res_passive_queues_freq               [15;5]
% 6.68/1.54  --res_forward_subs                      full
% 6.68/1.54  --res_backward_subs                     full
% 6.68/1.54  --res_forward_subs_resolution           true
% 6.68/1.54  --res_backward_subs_resolution          true
% 6.68/1.54  --res_orphan_elimination                true
% 6.68/1.54  --res_time_limit                        2.
% 6.68/1.54  --res_out_proof                         true
% 6.68/1.54  
% 6.68/1.54  ------ Superposition Options
% 6.68/1.54  
% 6.68/1.54  --superposition_flag                    true
% 6.68/1.54  --sup_passive_queue_type                priority_queues
% 6.68/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.68/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.68/1.54  --demod_completeness_check              fast
% 6.68/1.54  --demod_use_ground                      true
% 6.68/1.54  --sup_to_prop_solver                    passive
% 6.68/1.54  --sup_prop_simpl_new                    true
% 6.68/1.54  --sup_prop_simpl_given                  true
% 6.68/1.54  --sup_fun_splitting                     true
% 6.68/1.54  --sup_smt_interval                      50000
% 6.68/1.54  
% 6.68/1.54  ------ Superposition Simplification Setup
% 6.68/1.54  
% 6.68/1.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.68/1.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.68/1.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.68/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.68/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.68/1.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.68/1.54  --sup_immed_triv                        [TrivRules]
% 6.68/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.54  --sup_immed_bw_main                     []
% 6.68/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.68/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.68/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.54  --sup_input_bw                          []
% 6.68/1.54  
% 6.68/1.54  ------ Combination Options
% 6.68/1.54  
% 6.68/1.54  --comb_res_mult                         3
% 6.68/1.54  --comb_sup_mult                         2
% 6.68/1.54  --comb_inst_mult                        10
% 6.68/1.54  
% 6.68/1.54  ------ Debug Options
% 6.68/1.54  
% 6.68/1.54  --dbg_backtrace                         false
% 6.68/1.54  --dbg_dump_prop_clauses                 false
% 6.68/1.54  --dbg_dump_prop_clauses_file            -
% 6.68/1.54  --dbg_out_stat                          false
% 6.68/1.54  ------ Parsing...
% 6.68/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.68/1.54  
% 6.68/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.68/1.54  
% 6.68/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.68/1.54  
% 6.68/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.68/1.54  ------ Proving...
% 6.68/1.54  ------ Problem Properties 
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  clauses                                 18
% 6.68/1.54  conjectures                             2
% 6.68/1.54  EPR                                     2
% 6.68/1.54  Horn                                    13
% 6.68/1.54  unary                                   6
% 6.68/1.54  binary                                  5
% 6.68/1.54  lits                                    38
% 6.68/1.54  lits eq                                 15
% 6.68/1.54  fd_pure                                 0
% 6.68/1.54  fd_pseudo                               0
% 6.68/1.54  fd_cond                                 0
% 6.68/1.54  fd_pseudo_cond                          6
% 6.68/1.54  AC symbols                              0
% 6.68/1.54  
% 6.68/1.54  ------ Schedule dynamic 5 is on 
% 6.68/1.54  
% 6.68/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  ------ 
% 6.68/1.54  Current options:
% 6.68/1.54  ------ 
% 6.68/1.54  
% 6.68/1.54  ------ Input Options
% 6.68/1.54  
% 6.68/1.54  --out_options                           all
% 6.68/1.54  --tptp_safe_out                         true
% 6.68/1.54  --problem_path                          ""
% 6.68/1.54  --include_path                          ""
% 6.68/1.54  --clausifier                            res/vclausify_rel
% 6.68/1.54  --clausifier_options                    ""
% 6.68/1.54  --stdin                                 false
% 6.68/1.54  --stats_out                             all
% 6.68/1.54  
% 6.68/1.54  ------ General Options
% 6.68/1.54  
% 6.68/1.54  --fof                                   false
% 6.68/1.54  --time_out_real                         305.
% 6.68/1.54  --time_out_virtual                      -1.
% 6.68/1.54  --symbol_type_check                     false
% 6.68/1.54  --clausify_out                          false
% 6.68/1.54  --sig_cnt_out                           false
% 6.68/1.54  --trig_cnt_out                          false
% 6.68/1.54  --trig_cnt_out_tolerance                1.
% 6.68/1.54  --trig_cnt_out_sk_spl                   false
% 6.68/1.54  --abstr_cl_out                          false
% 6.68/1.54  
% 6.68/1.54  ------ Global Options
% 6.68/1.54  
% 6.68/1.54  --schedule                              default
% 6.68/1.54  --add_important_lit                     false
% 6.68/1.54  --prop_solver_per_cl                    1000
% 6.68/1.54  --min_unsat_core                        false
% 6.68/1.54  --soft_assumptions                      false
% 6.68/1.54  --soft_lemma_size                       3
% 6.68/1.54  --prop_impl_unit_size                   0
% 6.68/1.54  --prop_impl_unit                        []
% 6.68/1.54  --share_sel_clauses                     true
% 6.68/1.54  --reset_solvers                         false
% 6.68/1.54  --bc_imp_inh                            [conj_cone]
% 6.68/1.54  --conj_cone_tolerance                   3.
% 6.68/1.54  --extra_neg_conj                        none
% 6.68/1.54  --large_theory_mode                     true
% 6.68/1.54  --prolific_symb_bound                   200
% 6.68/1.54  --lt_threshold                          2000
% 6.68/1.54  --clause_weak_htbl                      true
% 6.68/1.54  --gc_record_bc_elim                     false
% 6.68/1.54  
% 6.68/1.54  ------ Preprocessing Options
% 6.68/1.54  
% 6.68/1.54  --preprocessing_flag                    true
% 6.68/1.54  --time_out_prep_mult                    0.1
% 6.68/1.54  --splitting_mode                        input
% 6.68/1.54  --splitting_grd                         true
% 6.68/1.54  --splitting_cvd                         false
% 6.68/1.54  --splitting_cvd_svl                     false
% 6.68/1.54  --splitting_nvd                         32
% 6.68/1.54  --sub_typing                            true
% 6.68/1.54  --prep_gs_sim                           true
% 6.68/1.54  --prep_unflatten                        true
% 6.68/1.54  --prep_res_sim                          true
% 6.68/1.54  --prep_upred                            true
% 6.68/1.54  --prep_sem_filter                       exhaustive
% 6.68/1.54  --prep_sem_filter_out                   false
% 6.68/1.54  --pred_elim                             true
% 6.68/1.54  --res_sim_input                         true
% 6.68/1.54  --eq_ax_congr_red                       true
% 6.68/1.54  --pure_diseq_elim                       true
% 6.68/1.54  --brand_transform                       false
% 6.68/1.54  --non_eq_to_eq                          false
% 6.68/1.54  --prep_def_merge                        true
% 6.68/1.54  --prep_def_merge_prop_impl              false
% 6.68/1.54  --prep_def_merge_mbd                    true
% 6.68/1.54  --prep_def_merge_tr_red                 false
% 6.68/1.54  --prep_def_merge_tr_cl                  false
% 6.68/1.54  --smt_preprocessing                     true
% 6.68/1.54  --smt_ac_axioms                         fast
% 6.68/1.54  --preprocessed_out                      false
% 6.68/1.54  --preprocessed_stats                    false
% 6.68/1.54  
% 6.68/1.54  ------ Abstraction refinement Options
% 6.68/1.54  
% 6.68/1.54  --abstr_ref                             []
% 6.68/1.54  --abstr_ref_prep                        false
% 6.68/1.54  --abstr_ref_until_sat                   false
% 6.68/1.54  --abstr_ref_sig_restrict                funpre
% 6.68/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.68/1.54  --abstr_ref_under                       []
% 6.68/1.54  
% 6.68/1.54  ------ SAT Options
% 6.68/1.54  
% 6.68/1.54  --sat_mode                              false
% 6.68/1.54  --sat_fm_restart_options                ""
% 6.68/1.54  --sat_gr_def                            false
% 6.68/1.54  --sat_epr_types                         true
% 6.68/1.54  --sat_non_cyclic_types                  false
% 6.68/1.54  --sat_finite_models                     false
% 6.68/1.54  --sat_fm_lemmas                         false
% 6.68/1.54  --sat_fm_prep                           false
% 6.68/1.54  --sat_fm_uc_incr                        true
% 6.68/1.54  --sat_out_model                         small
% 6.68/1.54  --sat_out_clauses                       false
% 6.68/1.54  
% 6.68/1.54  ------ QBF Options
% 6.68/1.54  
% 6.68/1.54  --qbf_mode                              false
% 6.68/1.54  --qbf_elim_univ                         false
% 6.68/1.54  --qbf_dom_inst                          none
% 6.68/1.54  --qbf_dom_pre_inst                      false
% 6.68/1.54  --qbf_sk_in                             false
% 6.68/1.54  --qbf_pred_elim                         true
% 6.68/1.54  --qbf_split                             512
% 6.68/1.54  
% 6.68/1.54  ------ BMC1 Options
% 6.68/1.54  
% 6.68/1.54  --bmc1_incremental                      false
% 6.68/1.54  --bmc1_axioms                           reachable_all
% 6.68/1.54  --bmc1_min_bound                        0
% 6.68/1.54  --bmc1_max_bound                        -1
% 6.68/1.54  --bmc1_max_bound_default                -1
% 6.68/1.54  --bmc1_symbol_reachability              true
% 6.68/1.54  --bmc1_property_lemmas                  false
% 6.68/1.54  --bmc1_k_induction                      false
% 6.68/1.54  --bmc1_non_equiv_states                 false
% 6.68/1.54  --bmc1_deadlock                         false
% 6.68/1.54  --bmc1_ucm                              false
% 6.68/1.54  --bmc1_add_unsat_core                   none
% 6.68/1.54  --bmc1_unsat_core_children              false
% 6.68/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.68/1.54  --bmc1_out_stat                         full
% 6.68/1.54  --bmc1_ground_init                      false
% 6.68/1.54  --bmc1_pre_inst_next_state              false
% 6.68/1.54  --bmc1_pre_inst_state                   false
% 6.68/1.54  --bmc1_pre_inst_reach_state             false
% 6.68/1.54  --bmc1_out_unsat_core                   false
% 6.68/1.54  --bmc1_aig_witness_out                  false
% 6.68/1.54  --bmc1_verbose                          false
% 6.68/1.54  --bmc1_dump_clauses_tptp                false
% 6.68/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.68/1.54  --bmc1_dump_file                        -
% 6.68/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.68/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.68/1.54  --bmc1_ucm_extend_mode                  1
% 6.68/1.54  --bmc1_ucm_init_mode                    2
% 6.68/1.54  --bmc1_ucm_cone_mode                    none
% 6.68/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.68/1.54  --bmc1_ucm_relax_model                  4
% 6.68/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.68/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.68/1.54  --bmc1_ucm_layered_model                none
% 6.68/1.54  --bmc1_ucm_max_lemma_size               10
% 6.68/1.54  
% 6.68/1.54  ------ AIG Options
% 6.68/1.54  
% 6.68/1.54  --aig_mode                              false
% 6.68/1.54  
% 6.68/1.54  ------ Instantiation Options
% 6.68/1.54  
% 6.68/1.54  --instantiation_flag                    true
% 6.68/1.54  --inst_sos_flag                         true
% 6.68/1.54  --inst_sos_phase                        true
% 6.68/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.68/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.68/1.54  --inst_lit_sel_side                     none
% 6.68/1.54  --inst_solver_per_active                1400
% 6.68/1.54  --inst_solver_calls_frac                1.
% 6.68/1.54  --inst_passive_queue_type               priority_queues
% 6.68/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.68/1.54  --inst_passive_queues_freq              [25;2]
% 6.68/1.54  --inst_dismatching                      true
% 6.68/1.54  --inst_eager_unprocessed_to_passive     true
% 6.68/1.54  --inst_prop_sim_given                   true
% 6.68/1.54  --inst_prop_sim_new                     false
% 6.68/1.54  --inst_subs_new                         false
% 6.68/1.54  --inst_eq_res_simp                      false
% 6.68/1.54  --inst_subs_given                       false
% 6.68/1.54  --inst_orphan_elimination               true
% 6.68/1.54  --inst_learning_loop_flag               true
% 6.68/1.54  --inst_learning_start                   3000
% 6.68/1.54  --inst_learning_factor                  2
% 6.68/1.54  --inst_start_prop_sim_after_learn       3
% 6.68/1.54  --inst_sel_renew                        solver
% 6.68/1.54  --inst_lit_activity_flag                true
% 6.68/1.54  --inst_restr_to_given                   false
% 6.68/1.54  --inst_activity_threshold               500
% 6.68/1.54  --inst_out_proof                        true
% 6.68/1.54  
% 6.68/1.54  ------ Resolution Options
% 6.68/1.54  
% 6.68/1.54  --resolution_flag                       false
% 6.68/1.54  --res_lit_sel                           adaptive
% 6.68/1.54  --res_lit_sel_side                      none
% 6.68/1.54  --res_ordering                          kbo
% 6.68/1.54  --res_to_prop_solver                    active
% 6.68/1.54  --res_prop_simpl_new                    false
% 6.68/1.54  --res_prop_simpl_given                  true
% 6.68/1.54  --res_passive_queue_type                priority_queues
% 6.68/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.68/1.54  --res_passive_queues_freq               [15;5]
% 6.68/1.54  --res_forward_subs                      full
% 6.68/1.54  --res_backward_subs                     full
% 6.68/1.54  --res_forward_subs_resolution           true
% 6.68/1.54  --res_backward_subs_resolution          true
% 6.68/1.54  --res_orphan_elimination                true
% 6.68/1.54  --res_time_limit                        2.
% 6.68/1.54  --res_out_proof                         true
% 6.68/1.54  
% 6.68/1.54  ------ Superposition Options
% 6.68/1.54  
% 6.68/1.54  --superposition_flag                    true
% 6.68/1.54  --sup_passive_queue_type                priority_queues
% 6.68/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.68/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.68/1.54  --demod_completeness_check              fast
% 6.68/1.54  --demod_use_ground                      true
% 6.68/1.54  --sup_to_prop_solver                    passive
% 6.68/1.54  --sup_prop_simpl_new                    true
% 6.68/1.54  --sup_prop_simpl_given                  true
% 6.68/1.54  --sup_fun_splitting                     true
% 6.68/1.54  --sup_smt_interval                      50000
% 6.68/1.54  
% 6.68/1.54  ------ Superposition Simplification Setup
% 6.68/1.54  
% 6.68/1.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.68/1.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.68/1.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.68/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.68/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.68/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.68/1.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.68/1.54  --sup_immed_triv                        [TrivRules]
% 6.68/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.54  --sup_immed_bw_main                     []
% 6.68/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.68/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.68/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.68/1.54  --sup_input_bw                          []
% 6.68/1.54  
% 6.68/1.54  ------ Combination Options
% 6.68/1.54  
% 6.68/1.54  --comb_res_mult                         3
% 6.68/1.54  --comb_sup_mult                         2
% 6.68/1.54  --comb_inst_mult                        10
% 6.68/1.54  
% 6.68/1.54  ------ Debug Options
% 6.68/1.54  
% 6.68/1.54  --dbg_backtrace                         false
% 6.68/1.54  --dbg_dump_prop_clauses                 false
% 6.68/1.54  --dbg_dump_prop_clauses_file            -
% 6.68/1.54  --dbg_out_stat                          false
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  ------ Proving...
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  % SZS status Theorem for theBenchmark.p
% 6.68/1.54  
% 6.68/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 6.68/1.54  
% 6.68/1.54  fof(f1,axiom,(
% 6.68/1.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f13,plain,(
% 6.68/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.68/1.54    inference(nnf_transformation,[],[f1])).
% 6.68/1.54  
% 6.68/1.54  fof(f14,plain,(
% 6.68/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.68/1.54    inference(flattening,[],[f13])).
% 6.68/1.54  
% 6.68/1.54  fof(f15,plain,(
% 6.68/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.68/1.54    inference(rectify,[],[f14])).
% 6.68/1.54  
% 6.68/1.54  fof(f16,plain,(
% 6.68/1.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 6.68/1.54    introduced(choice_axiom,[])).
% 6.68/1.54  
% 6.68/1.54  fof(f17,plain,(
% 6.68/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.68/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 6.68/1.54  
% 6.68/1.54  fof(f30,plain,(
% 6.68/1.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.68/1.54    inference(cnf_transformation,[],[f17])).
% 6.68/1.54  
% 6.68/1.54  fof(f4,axiom,(
% 6.68/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f38,plain,(
% 6.68/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.68/1.54    inference(cnf_transformation,[],[f4])).
% 6.68/1.54  
% 6.68/1.54  fof(f53,plain,(
% 6.68/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.68/1.54    inference(definition_unfolding,[],[f30,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f2,axiom,(
% 6.68/1.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f18,plain,(
% 6.68/1.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.68/1.54    inference(nnf_transformation,[],[f2])).
% 6.68/1.54  
% 6.68/1.54  fof(f19,plain,(
% 6.68/1.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.68/1.54    inference(flattening,[],[f18])).
% 6.68/1.54  
% 6.68/1.54  fof(f33,plain,(
% 6.68/1.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.68/1.54    inference(cnf_transformation,[],[f19])).
% 6.68/1.54  
% 6.68/1.54  fof(f70,plain,(
% 6.68/1.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.68/1.54    inference(equality_resolution,[],[f33])).
% 6.68/1.54  
% 6.68/1.54  fof(f3,axiom,(
% 6.68/1.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f20,plain,(
% 6.68/1.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 6.68/1.54    inference(nnf_transformation,[],[f3])).
% 6.68/1.54  
% 6.68/1.54  fof(f37,plain,(
% 6.68/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 6.68/1.54    inference(cnf_transformation,[],[f20])).
% 6.68/1.54  
% 6.68/1.54  fof(f57,plain,(
% 6.68/1.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 6.68/1.54    inference(definition_unfolding,[],[f37,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f6,axiom,(
% 6.68/1.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f40,plain,(
% 6.68/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 6.68/1.54    inference(cnf_transformation,[],[f6])).
% 6.68/1.54  
% 6.68/1.54  fof(f50,plain,(
% 6.68/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 6.68/1.54    inference(definition_unfolding,[],[f40,f38,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f5,axiom,(
% 6.68/1.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f39,plain,(
% 6.68/1.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.68/1.54    inference(cnf_transformation,[],[f5])).
% 6.68/1.54  
% 6.68/1.54  fof(f59,plain,(
% 6.68/1.54    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 6.68/1.54    inference(definition_unfolding,[],[f39,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f28,plain,(
% 6.68/1.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.68/1.54    inference(cnf_transformation,[],[f17])).
% 6.68/1.54  
% 6.68/1.54  fof(f55,plain,(
% 6.68/1.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 6.68/1.54    inference(definition_unfolding,[],[f28,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f67,plain,(
% 6.68/1.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 6.68/1.54    inference(equality_resolution,[],[f55])).
% 6.68/1.54  
% 6.68/1.54  fof(f27,plain,(
% 6.68/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.68/1.54    inference(cnf_transformation,[],[f17])).
% 6.68/1.54  
% 6.68/1.54  fof(f56,plain,(
% 6.68/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 6.68/1.54    inference(definition_unfolding,[],[f27,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f68,plain,(
% 6.68/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 6.68/1.54    inference(equality_resolution,[],[f56])).
% 6.68/1.54  
% 6.68/1.54  fof(f7,axiom,(
% 6.68/1.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f21,plain,(
% 6.68/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.68/1.54    inference(nnf_transformation,[],[f7])).
% 6.68/1.54  
% 6.68/1.54  fof(f22,plain,(
% 6.68/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.68/1.54    inference(rectify,[],[f21])).
% 6.68/1.54  
% 6.68/1.54  fof(f23,plain,(
% 6.68/1.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 6.68/1.54    introduced(choice_axiom,[])).
% 6.68/1.54  
% 6.68/1.54  fof(f24,plain,(
% 6.68/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.68/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 6.68/1.54  
% 6.68/1.54  fof(f41,plain,(
% 6.68/1.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.68/1.54    inference(cnf_transformation,[],[f24])).
% 6.68/1.54  
% 6.68/1.54  fof(f8,axiom,(
% 6.68/1.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f45,plain,(
% 6.68/1.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.68/1.54    inference(cnf_transformation,[],[f8])).
% 6.68/1.54  
% 6.68/1.54  fof(f9,axiom,(
% 6.68/1.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f46,plain,(
% 6.68/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.68/1.54    inference(cnf_transformation,[],[f9])).
% 6.68/1.54  
% 6.68/1.54  fof(f49,plain,(
% 6.68/1.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 6.68/1.54    inference(definition_unfolding,[],[f45,f46])).
% 6.68/1.54  
% 6.68/1.54  fof(f63,plain,(
% 6.68/1.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 6.68/1.54    inference(definition_unfolding,[],[f41,f49])).
% 6.68/1.54  
% 6.68/1.54  fof(f73,plain,(
% 6.68/1.54    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 6.68/1.54    inference(equality_resolution,[],[f63])).
% 6.68/1.54  
% 6.68/1.54  fof(f10,conjecture,(
% 6.68/1.54    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 6.68/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.68/1.54  
% 6.68/1.54  fof(f11,negated_conjecture,(
% 6.68/1.54    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 6.68/1.54    inference(negated_conjecture,[],[f10])).
% 6.68/1.54  
% 6.68/1.54  fof(f12,plain,(
% 6.68/1.54    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0)),
% 6.68/1.54    inference(ennf_transformation,[],[f11])).
% 6.68/1.54  
% 6.68/1.54  fof(f25,plain,(
% 6.68/1.54    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) => (k4_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2) & k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0)),
% 6.68/1.54    introduced(choice_axiom,[])).
% 6.68/1.54  
% 6.68/1.54  fof(f26,plain,(
% 6.68/1.54    k4_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2) & k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0),
% 6.68/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f25])).
% 6.68/1.54  
% 6.68/1.54  fof(f47,plain,(
% 6.68/1.54    k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0),
% 6.68/1.54    inference(cnf_transformation,[],[f26])).
% 6.68/1.54  
% 6.68/1.54  fof(f65,plain,(
% 6.68/1.54    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3))),
% 6.68/1.54    inference(definition_unfolding,[],[f47,f38,f49])).
% 6.68/1.54  
% 6.68/1.54  fof(f31,plain,(
% 6.68/1.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.68/1.54    inference(cnf_transformation,[],[f17])).
% 6.68/1.54  
% 6.68/1.54  fof(f52,plain,(
% 6.68/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.68/1.54    inference(definition_unfolding,[],[f31,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f32,plain,(
% 6.68/1.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.68/1.54    inference(cnf_transformation,[],[f17])).
% 6.68/1.54  
% 6.68/1.54  fof(f51,plain,(
% 6.68/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.68/1.54    inference(definition_unfolding,[],[f32,f38])).
% 6.68/1.54  
% 6.68/1.54  fof(f42,plain,(
% 6.68/1.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 6.68/1.54    inference(cnf_transformation,[],[f24])).
% 6.68/1.54  
% 6.68/1.54  fof(f62,plain,(
% 6.68/1.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 6.68/1.54    inference(definition_unfolding,[],[f42,f49])).
% 6.68/1.54  
% 6.68/1.54  fof(f71,plain,(
% 6.68/1.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 6.68/1.54    inference(equality_resolution,[],[f62])).
% 6.68/1.54  
% 6.68/1.54  fof(f72,plain,(
% 6.68/1.54    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 6.68/1.54    inference(equality_resolution,[],[f71])).
% 6.68/1.54  
% 6.68/1.54  fof(f48,plain,(
% 6.68/1.54    k4_xboole_0(k1_tarski(sK2),sK3) != k1_tarski(sK2)),
% 6.68/1.54    inference(cnf_transformation,[],[f26])).
% 6.68/1.54  
% 6.68/1.54  fof(f64,plain,(
% 6.68/1.54    k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != k1_enumset1(sK2,sK2,sK2)),
% 6.68/1.54    inference(definition_unfolding,[],[f48,f38,f49,f49])).
% 6.68/1.54  
% 6.68/1.54  cnf(c_3,plain,
% 6.68/1.54      ( r2_hidden(sK0(X0,X1,X2),X0)
% 6.68/1.54      | r2_hidden(sK0(X0,X1,X2),X2)
% 6.68/1.54      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 6.68/1.54      inference(cnf_transformation,[],[f53]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_668,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 6.68/1.54      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 6.68/1.54      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_9,plain,
% 6.68/1.54      ( r1_tarski(X0,X0) ),
% 6.68/1.54      inference(cnf_transformation,[],[f70]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_663,plain,
% 6.68/1.54      ( r1_tarski(X0,X0) = iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_10,plain,
% 6.68/1.54      ( ~ r1_tarski(X0,X1)
% 6.68/1.54      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.68/1.54      inference(cnf_transformation,[],[f57]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_662,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 6.68/1.54      | r1_tarski(X0,X1) != iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1387,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_663,c_662]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_0,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 6.68/1.54      inference(cnf_transformation,[],[f50]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1393,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_1387,c_0]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_12,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 6.68/1.54      inference(cnf_transformation,[],[f59]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1394,plain,
% 6.68/1.54      ( k3_xboole_0(X0,X0) = X0 ),
% 6.68/1.54      inference(light_normalisation,[status(thm)],[c_1393,c_12]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_5,plain,
% 6.68/1.54      ( ~ r2_hidden(X0,X1)
% 6.68/1.54      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 6.68/1.54      inference(cnf_transformation,[],[f67]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_666,plain,
% 6.68/1.54      ( r2_hidden(X0,X1) != iProver_top
% 6.68/1.54      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_2039,plain,
% 6.68/1.54      ( r2_hidden(X0,X1) != iProver_top
% 6.68/1.54      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_1394,c_666]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1395,plain,
% 6.68/1.54      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.68/1.54      inference(demodulation,[status(thm)],[c_1394,c_1387]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_2040,plain,
% 6.68/1.54      ( r2_hidden(X0,X1) != iProver_top
% 6.68/1.54      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.68/1.54      inference(demodulation,[status(thm)],[c_2039,c_1395]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_6,plain,
% 6.68/1.54      ( r2_hidden(X0,X1)
% 6.68/1.54      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 6.68/1.54      inference(cnf_transformation,[],[f68]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_665,plain,
% 6.68/1.54      ( r2_hidden(X0,X1) = iProver_top
% 6.68/1.54      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1668,plain,
% 6.68/1.54      ( r2_hidden(X0,X1) = iProver_top
% 6.68/1.54      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_1394,c_665]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1669,plain,
% 6.68/1.54      ( r2_hidden(X0,X1) = iProver_top
% 6.68/1.54      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.68/1.54      inference(demodulation,[status(thm)],[c_1668,c_1395]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_2077,plain,
% 6.68/1.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.68/1.54      inference(global_propositional_subsumption,
% 6.68/1.54                [status(thm)],
% 6.68/1.54                [c_2040,c_1669]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_3197,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 6.68/1.54      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_668,c_2077]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_16,plain,
% 6.68/1.54      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 6.68/1.54      inference(cnf_transformation,[],[f73]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_657,plain,
% 6.68/1.54      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_5634,plain,
% 6.68/1.54      ( sK0(k1_enumset1(X0,X0,X0),X1,k1_xboole_0) = X0
% 6.68/1.54      | k5_xboole_0(k1_enumset1(X0,X0,X0),k3_xboole_0(k1_enumset1(X0,X0,X0),X1)) = k1_xboole_0 ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_3197,c_657]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_18,negated_conjecture,
% 6.68/1.54      ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) ),
% 6.68/1.54      inference(cnf_transformation,[],[f65]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_13379,plain,
% 6.68/1.54      ( sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_xboole_0) = sK2 ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_5634,c_18]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_2,plain,
% 6.68/1.54      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 6.68/1.54      | r2_hidden(sK0(X0,X1,X2),X2)
% 6.68/1.54      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 6.68/1.54      inference(cnf_transformation,[],[f52]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_669,plain,
% 6.68/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 6.68/1.54      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 6.68/1.54      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_13506,plain,
% 6.68/1.54      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_xboole_0
% 6.68/1.54      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_xboole_0),k1_xboole_0) = iProver_top
% 6.68/1.54      | r2_hidden(sK2,sK3) != iProver_top ),
% 6.68/1.54      inference(superposition,[status(thm)],[c_13379,c_669]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_13512,plain,
% 6.68/1.54      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_xboole_0
% 6.68/1.54      | r2_hidden(sK2,sK3) != iProver_top
% 6.68/1.54      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 6.68/1.54      inference(light_normalisation,[status(thm)],[c_13506,c_13379]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_343,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_3093,plain,
% 6.68/1.54      ( X0 != X1
% 6.68/1.54      | X0 = sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) != X1 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_343]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_3094,plain,
% 6.68/1.54      ( sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) != sK2
% 6.68/1.54      | sK2 = sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | sK2 != sK2 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_3093]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_342,plain,( X0 = X0 ),theory(equality) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_2682,plain,
% 6.68/1.54      ( sK3 = sK3 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_342]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_2080,plain,
% 6.68/1.54      ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_2077]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_346,plain,
% 6.68/1.54      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.68/1.54      theory(equality) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1403,plain,
% 6.68/1.54      ( r2_hidden(X0,X1)
% 6.68/1.54      | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 6.68/1.54      | X0 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | X1 != sK3 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_346]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1915,plain,
% 6.68/1.54      ( r2_hidden(X0,sK3)
% 6.68/1.54      | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 6.68/1.54      | X0 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | sK3 != sK3 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_1403]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1916,plain,
% 6.68/1.54      ( X0 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | sK3 != sK3
% 6.68/1.54      | r2_hidden(X0,sK3) = iProver_top
% 6.68/1.54      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) != iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1918,plain,
% 6.68/1.54      ( sK3 != sK3
% 6.68/1.54      | sK2 != sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) != iProver_top
% 6.68/1.54      | r2_hidden(sK2,sK3) = iProver_top ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_1916]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1630,plain,
% 6.68/1.54      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(X0,X0,X0))
% 6.68/1.54      | sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) = X0 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_16]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1632,plain,
% 6.68/1.54      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_1630]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_909,plain,
% 6.68/1.54      ( k1_xboole_0 = k1_xboole_0 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_342]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_713,plain,
% 6.68/1.54      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != X0
% 6.68/1.54      | k1_xboole_0 != X0
% 6.68/1.54      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_343]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_804,plain,
% 6.68/1.54      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != k1_xboole_0
% 6.68/1.54      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3))
% 6.68/1.54      | k1_xboole_0 != k1_xboole_0 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_713]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_1,plain,
% 6.68/1.54      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 6.68/1.54      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 6.68/1.54      | r2_hidden(sK0(X0,X1,X2),X1)
% 6.68/1.54      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 6.68/1.54      inference(cnf_transformation,[],[f51]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_685,plain,
% 6.68/1.54      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 6.68/1.54      | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_1]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_692,plain,
% 6.68/1.54      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2)
% 6.68/1.54      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 6.68/1.54      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) = iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_687,plain,
% 6.68/1.54      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 6.68/1.54      | k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_3]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_688,plain,
% 6.68/1.54      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) = k1_enumset1(sK2,sK2,sK2)
% 6.68/1.54      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK2),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) = iProver_top ),
% 6.68/1.54      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_15,plain,
% 6.68/1.54      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 6.68/1.54      inference(cnf_transformation,[],[f72]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_23,plain,
% 6.68/1.54      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_15]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_20,plain,
% 6.68/1.54      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) | sK2 = sK2 ),
% 6.68/1.54      inference(instantiation,[status(thm)],[c_16]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(c_17,negated_conjecture,
% 6.68/1.54      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK2),k3_xboole_0(k1_enumset1(sK2,sK2,sK2),sK3)) != k1_enumset1(sK2,sK2,sK2) ),
% 6.68/1.54      inference(cnf_transformation,[],[f64]) ).
% 6.68/1.54  
% 6.68/1.54  cnf(contradiction,plain,
% 6.68/1.54      ( $false ),
% 6.68/1.54      inference(minisat,
% 6.68/1.54                [status(thm)],
% 6.68/1.54                [c_13512,c_3094,c_2682,c_2080,c_1918,c_1632,c_909,c_804,
% 6.68/1.54                 c_692,c_688,c_687,c_23,c_20,c_17,c_18]) ).
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 6.68/1.54  
% 6.68/1.54  ------                               Statistics
% 6.68/1.54  
% 6.68/1.54  ------ General
% 6.68/1.54  
% 6.68/1.54  abstr_ref_over_cycles:                  0
% 6.68/1.54  abstr_ref_under_cycles:                 0
% 6.68/1.54  gc_basic_clause_elim:                   0
% 6.68/1.54  forced_gc_time:                         0
% 6.68/1.54  parsing_time:                           0.019
% 6.68/1.54  unif_index_cands_time:                  0.
% 6.68/1.54  unif_index_add_time:                    0.
% 6.68/1.54  orderings_time:                         0.
% 6.68/1.54  out_proof_time:                         0.008
% 6.68/1.54  total_time:                             0.609
% 6.68/1.54  num_of_symbols:                         41
% 6.68/1.54  num_of_terms:                           15275
% 6.68/1.54  
% 6.68/1.54  ------ Preprocessing
% 6.68/1.54  
% 6.68/1.54  num_of_splits:                          0
% 6.68/1.54  num_of_split_atoms:                     0
% 6.68/1.54  num_of_reused_defs:                     0
% 6.68/1.54  num_eq_ax_congr_red:                    21
% 6.68/1.54  num_of_sem_filtered_clauses:            1
% 6.68/1.54  num_of_subtypes:                        0
% 6.68/1.54  monotx_restored_types:                  0
% 6.68/1.54  sat_num_of_epr_types:                   0
% 6.68/1.54  sat_num_of_non_cyclic_types:            0
% 6.68/1.54  sat_guarded_non_collapsed_types:        0
% 6.68/1.54  num_pure_diseq_elim:                    0
% 6.68/1.54  simp_replaced_by:                       0
% 6.68/1.54  res_preprocessed:                       85
% 6.68/1.54  prep_upred:                             0
% 6.68/1.54  prep_unflattend:                        0
% 6.68/1.54  smt_new_axioms:                         0
% 6.68/1.54  pred_elim_cands:                        2
% 6.68/1.54  pred_elim:                              0
% 6.68/1.54  pred_elim_cl:                           0
% 6.68/1.54  pred_elim_cycles:                       2
% 6.68/1.54  merged_defs:                            8
% 6.68/1.54  merged_defs_ncl:                        0
% 6.68/1.54  bin_hyper_res:                          8
% 6.68/1.54  prep_cycles:                            4
% 6.68/1.54  pred_elim_time:                         0.026
% 6.68/1.54  splitting_time:                         0.
% 6.68/1.54  sem_filter_time:                        0.
% 6.68/1.54  monotx_time:                            0.
% 6.68/1.54  subtype_inf_time:                       0.
% 6.68/1.54  
% 6.68/1.54  ------ Problem properties
% 6.68/1.54  
% 6.68/1.54  clauses:                                18
% 6.68/1.54  conjectures:                            2
% 6.68/1.54  epr:                                    2
% 6.68/1.54  horn:                                   13
% 6.68/1.54  ground:                                 2
% 6.68/1.54  unary:                                  6
% 6.68/1.54  binary:                                 5
% 6.68/1.54  lits:                                   38
% 6.68/1.54  lits_eq:                                15
% 6.68/1.54  fd_pure:                                0
% 6.68/1.54  fd_pseudo:                              0
% 6.68/1.54  fd_cond:                                0
% 6.68/1.54  fd_pseudo_cond:                         6
% 6.68/1.54  ac_symbols:                             0
% 6.68/1.54  
% 6.68/1.54  ------ Propositional Solver
% 6.68/1.54  
% 6.68/1.54  prop_solver_calls:                      30
% 6.68/1.54  prop_fast_solver_calls:                 993
% 6.68/1.54  smt_solver_calls:                       0
% 6.68/1.54  smt_fast_solver_calls:                  0
% 6.68/1.54  prop_num_of_clauses:                    5981
% 6.68/1.54  prop_preprocess_simplified:             10685
% 6.68/1.54  prop_fo_subsumed:                       10
% 6.68/1.54  prop_solver_time:                       0.
% 6.68/1.54  smt_solver_time:                        0.
% 6.68/1.54  smt_fast_solver_time:                   0.
% 6.68/1.54  prop_fast_solver_time:                  0.
% 6.68/1.54  prop_unsat_core_time:                   0.
% 6.68/1.54  
% 6.68/1.54  ------ QBF
% 6.68/1.54  
% 6.68/1.54  qbf_q_res:                              0
% 6.68/1.54  qbf_num_tautologies:                    0
% 6.68/1.54  qbf_prep_cycles:                        0
% 6.68/1.54  
% 6.68/1.54  ------ BMC1
% 6.68/1.54  
% 6.68/1.54  bmc1_current_bound:                     -1
% 6.68/1.54  bmc1_last_solved_bound:                 -1
% 6.68/1.54  bmc1_unsat_core_size:                   -1
% 6.68/1.54  bmc1_unsat_core_parents_size:           -1
% 6.68/1.54  bmc1_merge_next_fun:                    0
% 6.68/1.54  bmc1_unsat_core_clauses_time:           0.
% 6.68/1.54  
% 6.68/1.54  ------ Instantiation
% 6.68/1.54  
% 6.68/1.54  inst_num_of_clauses:                    1489
% 6.68/1.54  inst_num_in_passive:                    415
% 6.68/1.54  inst_num_in_active:                     507
% 6.68/1.54  inst_num_in_unprocessed:                571
% 6.68/1.54  inst_num_of_loops:                      730
% 6.68/1.54  inst_num_of_learning_restarts:          0
% 6.68/1.54  inst_num_moves_active_passive:          221
% 6.68/1.54  inst_lit_activity:                      0
% 6.68/1.54  inst_lit_activity_moves:                0
% 6.68/1.54  inst_num_tautologies:                   0
% 6.68/1.54  inst_num_prop_implied:                  0
% 6.68/1.54  inst_num_existing_simplified:           0
% 6.68/1.54  inst_num_eq_res_simplified:             0
% 6.68/1.54  inst_num_child_elim:                    0
% 6.68/1.54  inst_num_of_dismatching_blockings:      1527
% 6.68/1.54  inst_num_of_non_proper_insts:           1901
% 6.68/1.54  inst_num_of_duplicates:                 0
% 6.68/1.54  inst_inst_num_from_inst_to_res:         0
% 6.68/1.54  inst_dismatching_checking_time:         0.
% 6.68/1.54  
% 6.68/1.54  ------ Resolution
% 6.68/1.54  
% 6.68/1.54  res_num_of_clauses:                     0
% 6.68/1.54  res_num_in_passive:                     0
% 6.68/1.54  res_num_in_active:                      0
% 6.68/1.54  res_num_of_loops:                       89
% 6.68/1.54  res_forward_subset_subsumed:            177
% 6.68/1.54  res_backward_subset_subsumed:           18
% 6.68/1.54  res_forward_subsumed:                   0
% 6.68/1.54  res_backward_subsumed:                  0
% 6.68/1.54  res_forward_subsumption_resolution:     0
% 6.68/1.54  res_backward_subsumption_resolution:    0
% 6.68/1.54  res_clause_to_clause_subsumption:       3894
% 6.68/1.54  res_orphan_elimination:                 0
% 6.68/1.54  res_tautology_del:                      115
% 6.68/1.54  res_num_eq_res_simplified:              0
% 6.68/1.54  res_num_sel_changes:                    0
% 6.68/1.54  res_moves_from_active_to_pass:          0
% 6.68/1.54  
% 6.68/1.54  ------ Superposition
% 6.68/1.54  
% 6.68/1.54  sup_time_total:                         0.
% 6.68/1.54  sup_time_generating:                    0.
% 6.68/1.54  sup_time_sim_full:                      0.
% 6.68/1.54  sup_time_sim_immed:                     0.
% 6.68/1.54  
% 6.68/1.54  sup_num_of_clauses:                     548
% 6.68/1.54  sup_num_in_active:                      135
% 6.68/1.54  sup_num_in_passive:                     413
% 6.68/1.54  sup_num_of_loops:                       145
% 6.68/1.54  sup_fw_superposition:                   681
% 6.68/1.54  sup_bw_superposition:                   479
% 6.68/1.54  sup_immediate_simplified:               334
% 6.68/1.54  sup_given_eliminated:                   1
% 6.68/1.54  comparisons_done:                       0
% 6.68/1.54  comparisons_avoided:                    26
% 6.68/1.54  
% 6.68/1.54  ------ Simplifications
% 6.68/1.54  
% 6.68/1.54  
% 6.68/1.54  sim_fw_subset_subsumed:                 56
% 6.68/1.54  sim_bw_subset_subsumed:                 7
% 6.68/1.54  sim_fw_subsumed:                        70
% 6.68/1.54  sim_bw_subsumed:                        11
% 6.68/1.54  sim_fw_subsumption_res:                 0
% 6.68/1.54  sim_bw_subsumption_res:                 0
% 6.68/1.54  sim_tautology_del:                      27
% 6.68/1.54  sim_eq_tautology_del:                   62
% 6.68/1.54  sim_eq_res_simp:                        11
% 6.68/1.54  sim_fw_demodulated:                     161
% 6.68/1.54  sim_bw_demodulated:                     5
% 6.68/1.54  sim_light_normalised:                   94
% 6.68/1.54  sim_joinable_taut:                      0
% 6.68/1.54  sim_joinable_simp:                      0
% 6.68/1.54  sim_ac_normalised:                      0
% 6.68/1.54  sim_smt_subsumption:                    0
% 6.68/1.54  
%------------------------------------------------------------------------------
