%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:34 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  124 (1164 expanded)
%              Number of clauses        :   57 ( 225 expanded)
%              Number of leaves         :   17 ( 312 expanded)
%              Depth                    :   21
%              Number of atoms          :  363 (3945 expanded)
%              Number of equality atoms :  253 (2968 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f79,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f80,plain,(
    ! [X4,X0] : r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f79])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f54,f61,f50])).

fof(f85,plain,(
    ! [X2,X1] : r1_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f30])).

fof(f58,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f58,f61,f61])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f51,f61,f50,f50,f61])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f57,f50,f61])).

fof(f59,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f50,f61])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f81,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k5_enumset1(X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f68])).

fof(f82,plain,(
    ! [X4,X1] : r2_hidden(X4,k5_enumset1(X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f81])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1049,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1045,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1040,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1042,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = X2
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X2
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2342,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1040,c_1042])).

cnf(c_21,plain,
    ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | X1 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1041,plain,
    ( X0 = X1
    | X2 = X1
    | r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2715,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2342,c_1041])).

cnf(c_3350,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK3 ),
    inference(superposition,[status(thm)],[c_1045,c_2715])).

cnf(c_23,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( sK1 != sK4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1228,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0))
    | sK1 = X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1312,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK1))
    | sK1 = sK4
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_1313,plain,
    ( r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_20,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1044,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3351,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = sK1 ),
    inference(superposition,[status(thm)],[c_1044,c_2715])).

cnf(c_688,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1206,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_3955,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1206])).

cnf(c_3975,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3350,c_23,c_22,c_1312,c_1313,c_3351,c_3955])).

cnf(c_3976,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3975])).

cnf(c_3990,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | sK4 = X0
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_1041])).

cnf(c_1204,plain,
    ( sK4 != X0
    | sK1 != X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_3921,plain,
    ( sK4 != sK1
    | sK1 = sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_13,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1048,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1047,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3988,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_1047])).

cnf(c_4697,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = sK1
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_1048,c_3988])).

cnf(c_4837,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3990,c_23,c_22,c_1312,c_1313,c_3921,c_3955,c_4697])).

cnf(c_4838,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4837])).

cnf(c_4849,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4838,c_1047])).

cnf(c_5050,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK4 ),
    inference(superposition,[status(thm)],[c_1049,c_4849])).

cnf(c_5051,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_1048,c_4849])).

cnf(c_5500,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5050,c_22,c_1312,c_1313,c_3921,c_5051])).

cnf(c_5513,plain,
    ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5500,c_1048])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1053,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1381,plain,
    ( r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1053])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1054,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1056,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1770,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(k3_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1056])).

cnf(c_1778,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1381,c_1770])).

cnf(c_2017,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1778,c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1058,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3579,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2017,c_1058])).

cnf(c_5555,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5513,c_3579])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.53/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.03  
% 2.53/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.03  
% 2.53/1.03  ------  iProver source info
% 2.53/1.03  
% 2.53/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.03  git: non_committed_changes: false
% 2.53/1.03  git: last_make_outside_of_git: false
% 2.53/1.03  
% 2.53/1.03  ------ 
% 2.53/1.03  
% 2.53/1.03  ------ Input Options
% 2.53/1.03  
% 2.53/1.03  --out_options                           all
% 2.53/1.03  --tptp_safe_out                         true
% 2.53/1.03  --problem_path                          ""
% 2.53/1.03  --include_path                          ""
% 2.53/1.03  --clausifier                            res/vclausify_rel
% 2.53/1.03  --clausifier_options                    --mode clausify
% 2.53/1.03  --stdin                                 false
% 2.53/1.03  --stats_out                             all
% 2.53/1.03  
% 2.53/1.03  ------ General Options
% 2.53/1.03  
% 2.53/1.03  --fof                                   false
% 2.53/1.03  --time_out_real                         305.
% 2.53/1.03  --time_out_virtual                      -1.
% 2.53/1.03  --symbol_type_check                     false
% 2.53/1.03  --clausify_out                          false
% 2.53/1.03  --sig_cnt_out                           false
% 2.53/1.03  --trig_cnt_out                          false
% 2.53/1.03  --trig_cnt_out_tolerance                1.
% 2.53/1.03  --trig_cnt_out_sk_spl                   false
% 2.53/1.03  --abstr_cl_out                          false
% 2.53/1.03  
% 2.53/1.03  ------ Global Options
% 2.53/1.03  
% 2.53/1.03  --schedule                              default
% 2.53/1.03  --add_important_lit                     false
% 2.53/1.03  --prop_solver_per_cl                    1000
% 2.53/1.03  --min_unsat_core                        false
% 2.53/1.03  --soft_assumptions                      false
% 2.53/1.03  --soft_lemma_size                       3
% 2.53/1.03  --prop_impl_unit_size                   0
% 2.53/1.03  --prop_impl_unit                        []
% 2.53/1.03  --share_sel_clauses                     true
% 2.53/1.03  --reset_solvers                         false
% 2.53/1.03  --bc_imp_inh                            [conj_cone]
% 2.53/1.03  --conj_cone_tolerance                   3.
% 2.53/1.03  --extra_neg_conj                        none
% 2.53/1.03  --large_theory_mode                     true
% 2.53/1.03  --prolific_symb_bound                   200
% 2.53/1.03  --lt_threshold                          2000
% 2.53/1.03  --clause_weak_htbl                      true
% 2.53/1.03  --gc_record_bc_elim                     false
% 2.53/1.03  
% 2.53/1.03  ------ Preprocessing Options
% 2.53/1.03  
% 2.53/1.03  --preprocessing_flag                    true
% 2.53/1.03  --time_out_prep_mult                    0.1
% 2.53/1.03  --splitting_mode                        input
% 2.53/1.03  --splitting_grd                         true
% 2.53/1.03  --splitting_cvd                         false
% 2.53/1.03  --splitting_cvd_svl                     false
% 2.53/1.03  --splitting_nvd                         32
% 2.53/1.03  --sub_typing                            true
% 2.53/1.03  --prep_gs_sim                           true
% 2.53/1.03  --prep_unflatten                        true
% 2.53/1.03  --prep_res_sim                          true
% 2.53/1.03  --prep_upred                            true
% 2.53/1.03  --prep_sem_filter                       exhaustive
% 2.53/1.03  --prep_sem_filter_out                   false
% 2.53/1.03  --pred_elim                             true
% 2.53/1.03  --res_sim_input                         true
% 2.53/1.03  --eq_ax_congr_red                       true
% 2.53/1.03  --pure_diseq_elim                       true
% 2.53/1.03  --brand_transform                       false
% 2.53/1.03  --non_eq_to_eq                          false
% 2.53/1.03  --prep_def_merge                        true
% 2.53/1.03  --prep_def_merge_prop_impl              false
% 2.53/1.03  --prep_def_merge_mbd                    true
% 2.53/1.03  --prep_def_merge_tr_red                 false
% 2.53/1.03  --prep_def_merge_tr_cl                  false
% 2.53/1.03  --smt_preprocessing                     true
% 2.53/1.03  --smt_ac_axioms                         fast
% 2.53/1.03  --preprocessed_out                      false
% 2.53/1.03  --preprocessed_stats                    false
% 2.53/1.03  
% 2.53/1.03  ------ Abstraction refinement Options
% 2.53/1.03  
% 2.53/1.03  --abstr_ref                             []
% 2.53/1.03  --abstr_ref_prep                        false
% 2.53/1.03  --abstr_ref_until_sat                   false
% 2.53/1.03  --abstr_ref_sig_restrict                funpre
% 2.53/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.03  --abstr_ref_under                       []
% 2.53/1.03  
% 2.53/1.03  ------ SAT Options
% 2.53/1.03  
% 2.53/1.03  --sat_mode                              false
% 2.53/1.03  --sat_fm_restart_options                ""
% 2.53/1.03  --sat_gr_def                            false
% 2.53/1.03  --sat_epr_types                         true
% 2.53/1.03  --sat_non_cyclic_types                  false
% 2.53/1.03  --sat_finite_models                     false
% 2.53/1.03  --sat_fm_lemmas                         false
% 2.53/1.03  --sat_fm_prep                           false
% 2.53/1.03  --sat_fm_uc_incr                        true
% 2.53/1.03  --sat_out_model                         small
% 2.53/1.03  --sat_out_clauses                       false
% 2.53/1.03  
% 2.53/1.03  ------ QBF Options
% 2.53/1.03  
% 2.53/1.03  --qbf_mode                              false
% 2.53/1.03  --qbf_elim_univ                         false
% 2.53/1.03  --qbf_dom_inst                          none
% 2.53/1.03  --qbf_dom_pre_inst                      false
% 2.53/1.03  --qbf_sk_in                             false
% 2.53/1.03  --qbf_pred_elim                         true
% 2.53/1.03  --qbf_split                             512
% 2.53/1.03  
% 2.53/1.03  ------ BMC1 Options
% 2.53/1.03  
% 2.53/1.03  --bmc1_incremental                      false
% 2.53/1.03  --bmc1_axioms                           reachable_all
% 2.53/1.03  --bmc1_min_bound                        0
% 2.53/1.03  --bmc1_max_bound                        -1
% 2.53/1.03  --bmc1_max_bound_default                -1
% 2.53/1.03  --bmc1_symbol_reachability              true
% 2.53/1.03  --bmc1_property_lemmas                  false
% 2.53/1.03  --bmc1_k_induction                      false
% 2.53/1.03  --bmc1_non_equiv_states                 false
% 2.53/1.03  --bmc1_deadlock                         false
% 2.53/1.03  --bmc1_ucm                              false
% 2.53/1.03  --bmc1_add_unsat_core                   none
% 2.53/1.03  --bmc1_unsat_core_children              false
% 2.53/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.03  --bmc1_out_stat                         full
% 2.53/1.03  --bmc1_ground_init                      false
% 2.53/1.03  --bmc1_pre_inst_next_state              false
% 2.53/1.03  --bmc1_pre_inst_state                   false
% 2.53/1.03  --bmc1_pre_inst_reach_state             false
% 2.53/1.03  --bmc1_out_unsat_core                   false
% 2.53/1.03  --bmc1_aig_witness_out                  false
% 2.53/1.03  --bmc1_verbose                          false
% 2.53/1.03  --bmc1_dump_clauses_tptp                false
% 2.53/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.03  --bmc1_dump_file                        -
% 2.53/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.03  --bmc1_ucm_extend_mode                  1
% 2.53/1.03  --bmc1_ucm_init_mode                    2
% 2.53/1.03  --bmc1_ucm_cone_mode                    none
% 2.53/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.03  --bmc1_ucm_relax_model                  4
% 2.53/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.03  --bmc1_ucm_layered_model                none
% 2.53/1.03  --bmc1_ucm_max_lemma_size               10
% 2.53/1.03  
% 2.53/1.03  ------ AIG Options
% 2.53/1.03  
% 2.53/1.03  --aig_mode                              false
% 2.53/1.03  
% 2.53/1.03  ------ Instantiation Options
% 2.53/1.03  
% 2.53/1.03  --instantiation_flag                    true
% 2.53/1.03  --inst_sos_flag                         false
% 2.53/1.03  --inst_sos_phase                        true
% 2.53/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.03  --inst_lit_sel_side                     num_symb
% 2.53/1.03  --inst_solver_per_active                1400
% 2.53/1.03  --inst_solver_calls_frac                1.
% 2.53/1.03  --inst_passive_queue_type               priority_queues
% 2.53/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.03  --inst_passive_queues_freq              [25;2]
% 2.53/1.03  --inst_dismatching                      true
% 2.53/1.03  --inst_eager_unprocessed_to_passive     true
% 2.53/1.03  --inst_prop_sim_given                   true
% 2.53/1.03  --inst_prop_sim_new                     false
% 2.53/1.03  --inst_subs_new                         false
% 2.53/1.03  --inst_eq_res_simp                      false
% 2.53/1.03  --inst_subs_given                       false
% 2.53/1.03  --inst_orphan_elimination               true
% 2.53/1.03  --inst_learning_loop_flag               true
% 2.53/1.03  --inst_learning_start                   3000
% 2.53/1.03  --inst_learning_factor                  2
% 2.53/1.03  --inst_start_prop_sim_after_learn       3
% 2.53/1.03  --inst_sel_renew                        solver
% 2.53/1.03  --inst_lit_activity_flag                true
% 2.53/1.03  --inst_restr_to_given                   false
% 2.53/1.03  --inst_activity_threshold               500
% 2.53/1.03  --inst_out_proof                        true
% 2.53/1.03  
% 2.53/1.03  ------ Resolution Options
% 2.53/1.03  
% 2.53/1.03  --resolution_flag                       true
% 2.53/1.03  --res_lit_sel                           adaptive
% 2.53/1.03  --res_lit_sel_side                      none
% 2.53/1.03  --res_ordering                          kbo
% 2.53/1.03  --res_to_prop_solver                    active
% 2.53/1.03  --res_prop_simpl_new                    false
% 2.53/1.03  --res_prop_simpl_given                  true
% 2.53/1.03  --res_passive_queue_type                priority_queues
% 2.53/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.03  --res_passive_queues_freq               [15;5]
% 2.53/1.03  --res_forward_subs                      full
% 2.53/1.03  --res_backward_subs                     full
% 2.53/1.03  --res_forward_subs_resolution           true
% 2.53/1.03  --res_backward_subs_resolution          true
% 2.53/1.03  --res_orphan_elimination                true
% 2.53/1.03  --res_time_limit                        2.
% 2.53/1.03  --res_out_proof                         true
% 2.53/1.03  
% 2.53/1.03  ------ Superposition Options
% 2.53/1.03  
% 2.53/1.03  --superposition_flag                    true
% 2.53/1.03  --sup_passive_queue_type                priority_queues
% 2.53/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.03  --demod_completeness_check              fast
% 2.53/1.03  --demod_use_ground                      true
% 2.53/1.03  --sup_to_prop_solver                    passive
% 2.53/1.03  --sup_prop_simpl_new                    true
% 2.53/1.03  --sup_prop_simpl_given                  true
% 2.53/1.03  --sup_fun_splitting                     false
% 2.53/1.03  --sup_smt_interval                      50000
% 2.53/1.03  
% 2.53/1.03  ------ Superposition Simplification Setup
% 2.53/1.03  
% 2.53/1.03  --sup_indices_passive                   []
% 2.53/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.03  --sup_full_bw                           [BwDemod]
% 2.53/1.03  --sup_immed_triv                        [TrivRules]
% 2.53/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.03  --sup_immed_bw_main                     []
% 2.53/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.03  
% 2.53/1.03  ------ Combination Options
% 2.53/1.03  
% 2.53/1.03  --comb_res_mult                         3
% 2.53/1.03  --comb_sup_mult                         2
% 2.53/1.03  --comb_inst_mult                        10
% 2.53/1.03  
% 2.53/1.03  ------ Debug Options
% 2.53/1.03  
% 2.53/1.03  --dbg_backtrace                         false
% 2.53/1.03  --dbg_dump_prop_clauses                 false
% 2.53/1.03  --dbg_dump_prop_clauses_file            -
% 2.53/1.03  --dbg_out_stat                          false
% 2.53/1.03  ------ Parsing...
% 2.53/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.03  
% 2.53/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.53/1.03  
% 2.53/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.03  
% 2.53/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.03  ------ Proving...
% 2.53/1.03  ------ Problem Properties 
% 2.53/1.03  
% 2.53/1.03  
% 2.53/1.03  clauses                                 24
% 2.53/1.03  conjectures                             3
% 2.53/1.03  EPR                                     4
% 2.53/1.03  Horn                                    17
% 2.53/1.03  unary                                   12
% 2.53/1.03  binary                                  2
% 2.53/1.03  lits                                    49
% 2.53/1.03  lits eq                                 19
% 2.53/1.03  fd_pure                                 0
% 2.53/1.03  fd_pseudo                               0
% 2.53/1.03  fd_cond                                 1
% 2.53/1.03  fd_pseudo_cond                          5
% 2.53/1.03  AC symbols                              0
% 2.53/1.03  
% 2.53/1.03  ------ Schedule dynamic 5 is on 
% 2.53/1.03  
% 2.53/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.03  
% 2.53/1.03  
% 2.53/1.03  ------ 
% 2.53/1.03  Current options:
% 2.53/1.03  ------ 
% 2.53/1.03  
% 2.53/1.03  ------ Input Options
% 2.53/1.03  
% 2.53/1.03  --out_options                           all
% 2.53/1.03  --tptp_safe_out                         true
% 2.53/1.03  --problem_path                          ""
% 2.53/1.03  --include_path                          ""
% 2.53/1.03  --clausifier                            res/vclausify_rel
% 2.53/1.03  --clausifier_options                    --mode clausify
% 2.53/1.03  --stdin                                 false
% 2.53/1.03  --stats_out                             all
% 2.53/1.03  
% 2.53/1.03  ------ General Options
% 2.53/1.04  
% 2.53/1.04  --fof                                   false
% 2.53/1.04  --time_out_real                         305.
% 2.53/1.04  --time_out_virtual                      -1.
% 2.53/1.04  --symbol_type_check                     false
% 2.53/1.04  --clausify_out                          false
% 2.53/1.04  --sig_cnt_out                           false
% 2.53/1.04  --trig_cnt_out                          false
% 2.53/1.04  --trig_cnt_out_tolerance                1.
% 2.53/1.04  --trig_cnt_out_sk_spl                   false
% 2.53/1.04  --abstr_cl_out                          false
% 2.53/1.04  
% 2.53/1.04  ------ Global Options
% 2.53/1.04  
% 2.53/1.04  --schedule                              default
% 2.53/1.04  --add_important_lit                     false
% 2.53/1.04  --prop_solver_per_cl                    1000
% 2.53/1.04  --min_unsat_core                        false
% 2.53/1.04  --soft_assumptions                      false
% 2.53/1.04  --soft_lemma_size                       3
% 2.53/1.04  --prop_impl_unit_size                   0
% 2.53/1.04  --prop_impl_unit                        []
% 2.53/1.04  --share_sel_clauses                     true
% 2.53/1.04  --reset_solvers                         false
% 2.53/1.04  --bc_imp_inh                            [conj_cone]
% 2.53/1.04  --conj_cone_tolerance                   3.
% 2.53/1.04  --extra_neg_conj                        none
% 2.53/1.04  --large_theory_mode                     true
% 2.53/1.04  --prolific_symb_bound                   200
% 2.53/1.04  --lt_threshold                          2000
% 2.53/1.04  --clause_weak_htbl                      true
% 2.53/1.04  --gc_record_bc_elim                     false
% 2.53/1.04  
% 2.53/1.04  ------ Preprocessing Options
% 2.53/1.04  
% 2.53/1.04  --preprocessing_flag                    true
% 2.53/1.04  --time_out_prep_mult                    0.1
% 2.53/1.04  --splitting_mode                        input
% 2.53/1.04  --splitting_grd                         true
% 2.53/1.04  --splitting_cvd                         false
% 2.53/1.04  --splitting_cvd_svl                     false
% 2.53/1.04  --splitting_nvd                         32
% 2.53/1.04  --sub_typing                            true
% 2.53/1.04  --prep_gs_sim                           true
% 2.53/1.04  --prep_unflatten                        true
% 2.53/1.04  --prep_res_sim                          true
% 2.53/1.04  --prep_upred                            true
% 2.53/1.04  --prep_sem_filter                       exhaustive
% 2.53/1.04  --prep_sem_filter_out                   false
% 2.53/1.04  --pred_elim                             true
% 2.53/1.04  --res_sim_input                         true
% 2.53/1.04  --eq_ax_congr_red                       true
% 2.53/1.04  --pure_diseq_elim                       true
% 2.53/1.04  --brand_transform                       false
% 2.53/1.04  --non_eq_to_eq                          false
% 2.53/1.04  --prep_def_merge                        true
% 2.53/1.04  --prep_def_merge_prop_impl              false
% 2.53/1.04  --prep_def_merge_mbd                    true
% 2.53/1.04  --prep_def_merge_tr_red                 false
% 2.53/1.04  --prep_def_merge_tr_cl                  false
% 2.53/1.04  --smt_preprocessing                     true
% 2.53/1.04  --smt_ac_axioms                         fast
% 2.53/1.04  --preprocessed_out                      false
% 2.53/1.04  --preprocessed_stats                    false
% 2.53/1.04  
% 2.53/1.04  ------ Abstraction refinement Options
% 2.53/1.04  
% 2.53/1.04  --abstr_ref                             []
% 2.53/1.04  --abstr_ref_prep                        false
% 2.53/1.04  --abstr_ref_until_sat                   false
% 2.53/1.04  --abstr_ref_sig_restrict                funpre
% 2.53/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.04  --abstr_ref_under                       []
% 2.53/1.04  
% 2.53/1.04  ------ SAT Options
% 2.53/1.04  
% 2.53/1.04  --sat_mode                              false
% 2.53/1.04  --sat_fm_restart_options                ""
% 2.53/1.04  --sat_gr_def                            false
% 2.53/1.04  --sat_epr_types                         true
% 2.53/1.04  --sat_non_cyclic_types                  false
% 2.53/1.04  --sat_finite_models                     false
% 2.53/1.04  --sat_fm_lemmas                         false
% 2.53/1.04  --sat_fm_prep                           false
% 2.53/1.04  --sat_fm_uc_incr                        true
% 2.53/1.04  --sat_out_model                         small
% 2.53/1.04  --sat_out_clauses                       false
% 2.53/1.04  
% 2.53/1.04  ------ QBF Options
% 2.53/1.04  
% 2.53/1.04  --qbf_mode                              false
% 2.53/1.04  --qbf_elim_univ                         false
% 2.53/1.04  --qbf_dom_inst                          none
% 2.53/1.04  --qbf_dom_pre_inst                      false
% 2.53/1.04  --qbf_sk_in                             false
% 2.53/1.04  --qbf_pred_elim                         true
% 2.53/1.04  --qbf_split                             512
% 2.53/1.04  
% 2.53/1.04  ------ BMC1 Options
% 2.53/1.04  
% 2.53/1.04  --bmc1_incremental                      false
% 2.53/1.04  --bmc1_axioms                           reachable_all
% 2.53/1.04  --bmc1_min_bound                        0
% 2.53/1.04  --bmc1_max_bound                        -1
% 2.53/1.04  --bmc1_max_bound_default                -1
% 2.53/1.04  --bmc1_symbol_reachability              true
% 2.53/1.04  --bmc1_property_lemmas                  false
% 2.53/1.04  --bmc1_k_induction                      false
% 2.53/1.04  --bmc1_non_equiv_states                 false
% 2.53/1.04  --bmc1_deadlock                         false
% 2.53/1.04  --bmc1_ucm                              false
% 2.53/1.04  --bmc1_add_unsat_core                   none
% 2.53/1.04  --bmc1_unsat_core_children              false
% 2.53/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.04  --bmc1_out_stat                         full
% 2.53/1.04  --bmc1_ground_init                      false
% 2.53/1.04  --bmc1_pre_inst_next_state              false
% 2.53/1.04  --bmc1_pre_inst_state                   false
% 2.53/1.04  --bmc1_pre_inst_reach_state             false
% 2.53/1.04  --bmc1_out_unsat_core                   false
% 2.53/1.04  --bmc1_aig_witness_out                  false
% 2.53/1.04  --bmc1_verbose                          false
% 2.53/1.04  --bmc1_dump_clauses_tptp                false
% 2.53/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.04  --bmc1_dump_file                        -
% 2.53/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.04  --bmc1_ucm_extend_mode                  1
% 2.53/1.04  --bmc1_ucm_init_mode                    2
% 2.53/1.04  --bmc1_ucm_cone_mode                    none
% 2.53/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.04  --bmc1_ucm_relax_model                  4
% 2.53/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.04  --bmc1_ucm_layered_model                none
% 2.53/1.04  --bmc1_ucm_max_lemma_size               10
% 2.53/1.04  
% 2.53/1.04  ------ AIG Options
% 2.53/1.04  
% 2.53/1.04  --aig_mode                              false
% 2.53/1.04  
% 2.53/1.04  ------ Instantiation Options
% 2.53/1.04  
% 2.53/1.04  --instantiation_flag                    true
% 2.53/1.04  --inst_sos_flag                         false
% 2.53/1.04  --inst_sos_phase                        true
% 2.53/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.04  --inst_lit_sel_side                     none
% 2.53/1.04  --inst_solver_per_active                1400
% 2.53/1.04  --inst_solver_calls_frac                1.
% 2.53/1.04  --inst_passive_queue_type               priority_queues
% 2.53/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.04  --inst_passive_queues_freq              [25;2]
% 2.53/1.04  --inst_dismatching                      true
% 2.53/1.04  --inst_eager_unprocessed_to_passive     true
% 2.53/1.04  --inst_prop_sim_given                   true
% 2.53/1.04  --inst_prop_sim_new                     false
% 2.53/1.04  --inst_subs_new                         false
% 2.53/1.04  --inst_eq_res_simp                      false
% 2.53/1.04  --inst_subs_given                       false
% 2.53/1.04  --inst_orphan_elimination               true
% 2.53/1.04  --inst_learning_loop_flag               true
% 2.53/1.04  --inst_learning_start                   3000
% 2.53/1.04  --inst_learning_factor                  2
% 2.53/1.04  --inst_start_prop_sim_after_learn       3
% 2.53/1.04  --inst_sel_renew                        solver
% 2.53/1.04  --inst_lit_activity_flag                true
% 2.53/1.04  --inst_restr_to_given                   false
% 2.53/1.04  --inst_activity_threshold               500
% 2.53/1.04  --inst_out_proof                        true
% 2.53/1.04  
% 2.53/1.04  ------ Resolution Options
% 2.53/1.04  
% 2.53/1.04  --resolution_flag                       false
% 2.53/1.04  --res_lit_sel                           adaptive
% 2.53/1.04  --res_lit_sel_side                      none
% 2.53/1.04  --res_ordering                          kbo
% 2.53/1.04  --res_to_prop_solver                    active
% 2.53/1.04  --res_prop_simpl_new                    false
% 2.53/1.04  --res_prop_simpl_given                  true
% 2.53/1.04  --res_passive_queue_type                priority_queues
% 2.53/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.04  --res_passive_queues_freq               [15;5]
% 2.53/1.04  --res_forward_subs                      full
% 2.53/1.04  --res_backward_subs                     full
% 2.53/1.04  --res_forward_subs_resolution           true
% 2.53/1.04  --res_backward_subs_resolution          true
% 2.53/1.04  --res_orphan_elimination                true
% 2.53/1.04  --res_time_limit                        2.
% 2.53/1.04  --res_out_proof                         true
% 2.53/1.04  
% 2.53/1.04  ------ Superposition Options
% 2.53/1.04  
% 2.53/1.04  --superposition_flag                    true
% 2.53/1.04  --sup_passive_queue_type                priority_queues
% 2.53/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.04  --demod_completeness_check              fast
% 2.53/1.04  --demod_use_ground                      true
% 2.53/1.04  --sup_to_prop_solver                    passive
% 2.53/1.04  --sup_prop_simpl_new                    true
% 2.53/1.04  --sup_prop_simpl_given                  true
% 2.53/1.04  --sup_fun_splitting                     false
% 2.53/1.04  --sup_smt_interval                      50000
% 2.53/1.04  
% 2.53/1.04  ------ Superposition Simplification Setup
% 2.53/1.04  
% 2.53/1.04  --sup_indices_passive                   []
% 2.53/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.04  --sup_full_bw                           [BwDemod]
% 2.53/1.04  --sup_immed_triv                        [TrivRules]
% 2.53/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.04  --sup_immed_bw_main                     []
% 2.53/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.04  
% 2.53/1.04  ------ Combination Options
% 2.53/1.04  
% 2.53/1.04  --comb_res_mult                         3
% 2.53/1.04  --comb_sup_mult                         2
% 2.53/1.04  --comb_inst_mult                        10
% 2.53/1.04  
% 2.53/1.04  ------ Debug Options
% 2.53/1.04  
% 2.53/1.04  --dbg_backtrace                         false
% 2.53/1.04  --dbg_dump_prop_clauses                 false
% 2.53/1.04  --dbg_dump_prop_clauses_file            -
% 2.53/1.04  --dbg_out_stat                          false
% 2.53/1.04  
% 2.53/1.04  
% 2.53/1.04  
% 2.53/1.04  
% 2.53/1.04  ------ Proving...
% 2.53/1.04  
% 2.53/1.04  
% 2.53/1.04  % SZS status Theorem for theBenchmark.p
% 2.53/1.04  
% 2.53/1.04   Resolution empty clause
% 2.53/1.04  
% 2.53/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.04  
% 2.53/1.04  fof(f7,axiom,(
% 2.53/1.04    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f23,plain,(
% 2.53/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/1.04    inference(nnf_transformation,[],[f7])).
% 2.53/1.04  
% 2.53/1.04  fof(f24,plain,(
% 2.53/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/1.04    inference(flattening,[],[f23])).
% 2.53/1.04  
% 2.53/1.04  fof(f25,plain,(
% 2.53/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/1.04    inference(rectify,[],[f24])).
% 2.53/1.04  
% 2.53/1.04  fof(f26,plain,(
% 2.53/1.04    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.53/1.04    introduced(choice_axiom,[])).
% 2.53/1.04  
% 2.53/1.04  fof(f27,plain,(
% 2.53/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.53/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.53/1.04  
% 2.53/1.04  fof(f44,plain,(
% 2.53/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.53/1.04    inference(cnf_transformation,[],[f27])).
% 2.53/1.04  
% 2.53/1.04  fof(f8,axiom,(
% 2.53/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f48,plain,(
% 2.53/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.53/1.04    inference(cnf_transformation,[],[f8])).
% 2.53/1.04  
% 2.53/1.04  fof(f9,axiom,(
% 2.53/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f49,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.53/1.04    inference(cnf_transformation,[],[f9])).
% 2.53/1.04  
% 2.53/1.04  fof(f61,plain,(
% 2.53/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.53/1.04    inference(definition_unfolding,[],[f48,f49])).
% 2.53/1.04  
% 2.53/1.04  fof(f67,plain,(
% 2.53/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.53/1.04    inference(definition_unfolding,[],[f44,f61])).
% 2.53/1.04  
% 2.53/1.04  fof(f79,plain,(
% 2.53/1.04    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X4) != X2) )),
% 2.53/1.04    inference(equality_resolution,[],[f67])).
% 2.53/1.04  
% 2.53/1.04  fof(f80,plain,(
% 2.53/1.04    ( ! [X4,X0] : (r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X4))) )),
% 2.53/1.04    inference(equality_resolution,[],[f79])).
% 2.53/1.04  
% 2.53/1.04  fof(f11,axiom,(
% 2.53/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f19,plain,(
% 2.53/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.53/1.04    inference(ennf_transformation,[],[f11])).
% 2.53/1.04  
% 2.53/1.04  fof(f28,plain,(
% 2.53/1.04    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.53/1.04    inference(nnf_transformation,[],[f19])).
% 2.53/1.04  
% 2.53/1.04  fof(f29,plain,(
% 2.53/1.04    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.53/1.04    inference(flattening,[],[f28])).
% 2.53/1.04  
% 2.53/1.04  fof(f54,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 2.53/1.04    inference(cnf_transformation,[],[f29])).
% 2.53/1.04  
% 2.53/1.04  fof(f10,axiom,(
% 2.53/1.04    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f50,plain,(
% 2.53/1.04    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 2.53/1.04    inference(cnf_transformation,[],[f10])).
% 2.53/1.04  
% 2.53/1.04  fof(f71,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X0) )),
% 2.53/1.04    inference(definition_unfolding,[],[f54,f61,f50])).
% 2.53/1.04  
% 2.53/1.04  fof(f85,plain,(
% 2.53/1.04    ( ! [X2,X1] : (r1_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 2.53/1.04    inference(equality_resolution,[],[f71])).
% 2.53/1.04  
% 2.53/1.04  fof(f14,conjecture,(
% 2.53/1.04    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f15,negated_conjecture,(
% 2.53/1.04    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.53/1.04    inference(negated_conjecture,[],[f14])).
% 2.53/1.04  
% 2.53/1.04  fof(f21,plain,(
% 2.53/1.04    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.53/1.04    inference(ennf_transformation,[],[f15])).
% 2.53/1.04  
% 2.53/1.04  fof(f30,plain,(
% 2.53/1.04    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 2.53/1.04    introduced(choice_axiom,[])).
% 2.53/1.04  
% 2.53/1.04  fof(f31,plain,(
% 2.53/1.04    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 2.53/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f30])).
% 2.53/1.04  
% 2.53/1.04  fof(f58,plain,(
% 2.53/1.04    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 2.53/1.04    inference(cnf_transformation,[],[f31])).
% 2.53/1.04  
% 2.53/1.04  fof(f77,plain,(
% 2.53/1.04    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 2.53/1.04    inference(definition_unfolding,[],[f58,f61,f61])).
% 2.53/1.04  
% 2.53/1.04  fof(f51,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.53/1.04    inference(cnf_transformation,[],[f29])).
% 2.53/1.04  
% 2.53/1.04  fof(f74,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0 | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 2.53/1.04    inference(definition_unfolding,[],[f51,f61,f50,f50,f61])).
% 2.53/1.04  
% 2.53/1.04  fof(f13,axiom,(
% 2.53/1.04    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f20,plain,(
% 2.53/1.04    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.53/1.04    inference(ennf_transformation,[],[f13])).
% 2.53/1.04  
% 2.53/1.04  fof(f57,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.53/1.04    inference(cnf_transformation,[],[f20])).
% 2.53/1.04  
% 2.53/1.04  fof(f76,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 2.53/1.04    inference(definition_unfolding,[],[f57,f50,f61])).
% 2.53/1.04  
% 2.53/1.04  fof(f59,plain,(
% 2.53/1.04    sK1 != sK3),
% 2.53/1.04    inference(cnf_transformation,[],[f31])).
% 2.53/1.04  
% 2.53/1.04  fof(f60,plain,(
% 2.53/1.04    sK1 != sK4),
% 2.53/1.04    inference(cnf_transformation,[],[f31])).
% 2.53/1.04  
% 2.53/1.04  fof(f42,plain,(
% 2.53/1.04    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.53/1.04    inference(cnf_transformation,[],[f27])).
% 2.53/1.04  
% 2.53/1.04  fof(f69,plain,(
% 2.53/1.04    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.53/1.04    inference(definition_unfolding,[],[f42,f61])).
% 2.53/1.04  
% 2.53/1.04  fof(f83,plain,(
% 2.53/1.04    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 2.53/1.04    inference(equality_resolution,[],[f69])).
% 2.53/1.04  
% 2.53/1.04  fof(f12,axiom,(
% 2.53/1.04    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f56,plain,(
% 2.53/1.04    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.53/1.04    inference(cnf_transformation,[],[f12])).
% 2.53/1.04  
% 2.53/1.04  fof(f75,plain,(
% 2.53/1.04    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 2.53/1.04    inference(definition_unfolding,[],[f56,f50,f61])).
% 2.53/1.04  
% 2.53/1.04  fof(f43,plain,(
% 2.53/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.53/1.04    inference(cnf_transformation,[],[f27])).
% 2.53/1.04  
% 2.53/1.04  fof(f68,plain,(
% 2.53/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.53/1.04    inference(definition_unfolding,[],[f43,f61])).
% 2.53/1.04  
% 2.53/1.04  fof(f81,plain,(
% 2.53/1.04    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k5_enumset1(X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 2.53/1.04    inference(equality_resolution,[],[f68])).
% 2.53/1.04  
% 2.53/1.04  fof(f82,plain,(
% 2.53/1.04    ( ! [X4,X1] : (r2_hidden(X4,k5_enumset1(X4,X4,X4,X4,X4,X4,X1))) )),
% 2.53/1.04    inference(equality_resolution,[],[f81])).
% 2.53/1.04  
% 2.53/1.04  fof(f3,axiom,(
% 2.53/1.04    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f37,plain,(
% 2.53/1.04    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 2.53/1.04    inference(cnf_transformation,[],[f3])).
% 2.53/1.04  
% 2.53/1.04  fof(f2,axiom,(
% 2.53/1.04    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f36,plain,(
% 2.53/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.53/1.04    inference(cnf_transformation,[],[f2])).
% 2.53/1.04  
% 2.53/1.04  fof(f62,plain,(
% 2.53/1.04    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0) )),
% 2.53/1.04    inference(definition_unfolding,[],[f37,f36])).
% 2.53/1.04  
% 2.53/1.04  fof(f6,axiom,(
% 2.53/1.04    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f41,plain,(
% 2.53/1.04    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 2.53/1.04    inference(cnf_transformation,[],[f6])).
% 2.53/1.04  
% 2.53/1.04  fof(f63,plain,(
% 2.53/1.04    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.53/1.04    inference(definition_unfolding,[],[f41,f36])).
% 2.53/1.04  
% 2.53/1.04  fof(f5,axiom,(
% 2.53/1.04    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f18,plain,(
% 2.53/1.04    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 2.53/1.04    inference(ennf_transformation,[],[f5])).
% 2.53/1.04  
% 2.53/1.04  fof(f40,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.53/1.04    inference(cnf_transformation,[],[f18])).
% 2.53/1.04  
% 2.53/1.04  fof(f4,axiom,(
% 2.53/1.04    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f17,plain,(
% 2.53/1.04    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.53/1.04    inference(ennf_transformation,[],[f4])).
% 2.53/1.04  
% 2.53/1.04  fof(f39,plain,(
% 2.53/1.04    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.53/1.04    inference(cnf_transformation,[],[f17])).
% 2.53/1.04  
% 2.53/1.04  fof(f1,axiom,(
% 2.53/1.04    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.53/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.04  
% 2.53/1.04  fof(f16,plain,(
% 2.53/1.04    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.53/1.04    inference(ennf_transformation,[],[f1])).
% 2.53/1.04  
% 2.53/1.04  fof(f22,plain,(
% 2.53/1.04    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.53/1.04    inference(nnf_transformation,[],[f16])).
% 2.53/1.04  
% 2.53/1.04  fof(f33,plain,(
% 2.53/1.04    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 2.53/1.04    inference(cnf_transformation,[],[f22])).
% 2.53/1.04  
% 2.53/1.04  cnf(c_12,plain,
% 2.53/1.04      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
% 2.53/1.04      inference(cnf_transformation,[],[f80]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1049,plain,
% 2.53/1.04      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_16,plain,
% 2.53/1.04      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
% 2.53/1.04      inference(cnf_transformation,[],[f85]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1045,plain,
% 2.53/1.04      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_24,negated_conjecture,
% 2.53/1.04      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.53/1.04      inference(cnf_transformation,[],[f77]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1040,plain,
% 2.53/1.04      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_19,plain,
% 2.53/1.04      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 2.53/1.04      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
% 2.53/1.04      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
% 2.53/1.04      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 2.53/1.04      | k1_xboole_0 = X0 ),
% 2.53/1.04      inference(cnf_transformation,[],[f74]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1042,plain,
% 2.53/1.04      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = X2
% 2.53/1.04      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X2
% 2.53/1.04      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X2
% 2.53/1.04      | k1_xboole_0 = X2
% 2.53/1.04      | r1_tarski(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_2342,plain,
% 2.53/1.04      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1040,c_1042]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_21,plain,
% 2.53/1.04      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 2.53/1.04      | X1 = X0
% 2.53/1.04      | X2 = X0 ),
% 2.53/1.04      inference(cnf_transformation,[],[f76]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1041,plain,
% 2.53/1.04      ( X0 = X1
% 2.53/1.04      | X2 = X1
% 2.53/1.04      | r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_2715,plain,
% 2.53/1.04      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | sK3 = X0
% 2.53/1.04      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_2342,c_1041]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3350,plain,
% 2.53/1.04      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | sK2 = sK3 ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1045,c_2715]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_23,negated_conjecture,
% 2.53/1.04      ( sK1 != sK3 ),
% 2.53/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_22,negated_conjecture,
% 2.53/1.04      ( sK1 != sK4 ),
% 2.53/1.04      inference(cnf_transformation,[],[f60]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_14,plain,
% 2.53/1.04      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 2.53/1.04      inference(cnf_transformation,[],[f83]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1228,plain,
% 2.53/1.04      ( ~ r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0))
% 2.53/1.04      | sK1 = X0
% 2.53/1.04      | sK1 = sK4 ),
% 2.53/1.04      inference(instantiation,[status(thm)],[c_14]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1312,plain,
% 2.53/1.04      ( ~ r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK1))
% 2.53/1.04      | sK1 = sK4
% 2.53/1.04      | sK1 = sK1 ),
% 2.53/1.04      inference(instantiation,[status(thm)],[c_1228]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1313,plain,
% 2.53/1.04      ( r2_hidden(sK1,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK1)) ),
% 2.53/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_20,plain,
% 2.53/1.04      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 2.53/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1044,plain,
% 2.53/1.04      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3351,plain,
% 2.53/1.04      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | sK3 = sK1 ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1044,c_2715]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_688,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1206,plain,
% 2.53/1.04      ( sK3 != X0 | sK1 != X0 | sK1 = sK3 ),
% 2.53/1.04      inference(instantiation,[status(thm)],[c_688]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3955,plain,
% 2.53/1.04      ( sK3 != sK1 | sK1 = sK3 | sK1 != sK1 ),
% 2.53/1.04      inference(instantiation,[status(thm)],[c_1206]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3975,plain,
% 2.53/1.04      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 2.53/1.04      inference(global_propositional_subsumption,
% 2.53/1.04                [status(thm)],
% 2.53/1.04                [c_3350,c_23,c_22,c_1312,c_1313,c_3351,c_3955]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3976,plain,
% 2.53/1.04      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 2.53/1.04      inference(renaming,[status(thm)],[c_3975]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3990,plain,
% 2.53/1.04      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | sK3 = X0
% 2.53/1.04      | sK4 = X0
% 2.53/1.04      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_3976,c_1041]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1204,plain,
% 2.53/1.04      ( sK4 != X0 | sK1 != X0 | sK1 = sK4 ),
% 2.53/1.04      inference(instantiation,[status(thm)],[c_688]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3921,plain,
% 2.53/1.04      ( sK4 != sK1 | sK1 = sK4 | sK1 != sK1 ),
% 2.53/1.04      inference(instantiation,[status(thm)],[c_1204]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_13,plain,
% 2.53/1.04      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 2.53/1.04      inference(cnf_transformation,[],[f82]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1048,plain,
% 2.53/1.04      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1047,plain,
% 2.53/1.04      ( X0 = X1
% 2.53/1.04      | X0 = X2
% 2.53/1.04      | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3988,plain,
% 2.53/1.04      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | sK3 = X0
% 2.53/1.04      | sK4 = X0
% 2.53/1.04      | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_3976,c_1047]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_4697,plain,
% 2.53/1.04      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | sK3 = sK1
% 2.53/1.04      | sK4 = sK1 ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1048,c_3988]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_4837,plain,
% 2.53/1.04      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 2.53/1.04      inference(global_propositional_subsumption,
% 2.53/1.04                [status(thm)],
% 2.53/1.04                [c_3990,c_23,c_22,c_1312,c_1313,c_3921,c_3955,c_4697]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_4838,plain,
% 2.53/1.04      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 2.53/1.04      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 2.53/1.04      inference(renaming,[status(thm)],[c_4837]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_4849,plain,
% 2.53/1.04      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 2.53/1.04      | sK4 = X0
% 2.53/1.04      | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_4838,c_1047]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_5050,plain,
% 2.53/1.04      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 | sK2 = sK4 ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1049,c_4849]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_5051,plain,
% 2.53/1.04      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 | sK4 = sK1 ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1048,c_4849]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_5500,plain,
% 2.53/1.04      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 2.53/1.04      inference(global_propositional_subsumption,
% 2.53/1.04                [status(thm)],
% 2.53/1.04                [c_5050,c_22,c_1312,c_1313,c_3921,c_5051]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_5513,plain,
% 2.53/1.04      ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_5500,c_1048]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_4,plain,
% 2.53/1.04      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.53/1.04      inference(cnf_transformation,[],[f62]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_8,plain,
% 2.53/1.04      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 2.53/1.04      inference(cnf_transformation,[],[f63]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1053,plain,
% 2.53/1.04      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1381,plain,
% 2.53/1.04      ( r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_4,c_1053]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_7,plain,
% 2.53/1.04      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 2.53/1.04      inference(cnf_transformation,[],[f40]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1054,plain,
% 2.53/1.04      ( r1_xboole_0(X0,X1) != iProver_top
% 2.53/1.04      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_5,plain,
% 2.53/1.04      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.53/1.04      inference(cnf_transformation,[],[f39]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1056,plain,
% 2.53/1.04      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1770,plain,
% 2.53/1.04      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 2.53/1.04      | r1_xboole_0(k3_xboole_0(X0,X1),X0) != iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1054,c_1056]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1778,plain,
% 2.53/1.04      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_1381,c_1770]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_2017,plain,
% 2.53/1.04      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.53/1.04      inference(demodulation,[status(thm)],[c_1778,c_4]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_2,plain,
% 2.53/1.04      ( ~ r2_hidden(X0,X1)
% 2.53/1.04      | ~ r2_hidden(X0,X2)
% 2.53/1.04      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 2.53/1.04      inference(cnf_transformation,[],[f33]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_1058,plain,
% 2.53/1.04      ( r2_hidden(X0,X1) != iProver_top
% 2.53/1.04      | r2_hidden(X0,X2) != iProver_top
% 2.53/1.04      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 2.53/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_3579,plain,
% 2.53/1.04      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.53/1.04      inference(superposition,[status(thm)],[c_2017,c_1058]) ).
% 2.53/1.04  
% 2.53/1.04  cnf(c_5555,plain,
% 2.53/1.04      ( $false ),
% 2.53/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_5513,c_3579]) ).
% 2.53/1.04  
% 2.53/1.04  
% 2.53/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.04  
% 2.53/1.04  ------                               Statistics
% 2.53/1.04  
% 2.53/1.04  ------ General
% 2.53/1.04  
% 2.53/1.04  abstr_ref_over_cycles:                  0
% 2.53/1.04  abstr_ref_under_cycles:                 0
% 2.53/1.04  gc_basic_clause_elim:                   0
% 2.53/1.04  forced_gc_time:                         0
% 2.53/1.04  parsing_time:                           0.011
% 2.53/1.04  unif_index_cands_time:                  0.
% 2.53/1.04  unif_index_add_time:                    0.
% 2.53/1.04  orderings_time:                         0.
% 2.53/1.04  out_proof_time:                         0.011
% 2.53/1.04  total_time:                             0.251
% 2.53/1.04  num_of_symbols:                         43
% 2.53/1.04  num_of_terms:                           5731
% 2.53/1.04  
% 2.53/1.04  ------ Preprocessing
% 2.53/1.04  
% 2.53/1.04  num_of_splits:                          0
% 2.53/1.04  num_of_split_atoms:                     0
% 2.53/1.04  num_of_reused_defs:                     0
% 2.53/1.04  num_eq_ax_congr_red:                    12
% 2.53/1.04  num_of_sem_filtered_clauses:            1
% 2.53/1.04  num_of_subtypes:                        0
% 2.53/1.04  monotx_restored_types:                  0
% 2.53/1.04  sat_num_of_epr_types:                   0
% 2.53/1.04  sat_num_of_non_cyclic_types:            0
% 2.53/1.04  sat_guarded_non_collapsed_types:        0
% 2.53/1.04  num_pure_diseq_elim:                    0
% 2.53/1.04  simp_replaced_by:                       0
% 2.53/1.04  res_preprocessed:                       113
% 2.53/1.04  prep_upred:                             0
% 2.53/1.04  prep_unflattend:                        10
% 2.53/1.04  smt_new_axioms:                         0
% 2.53/1.04  pred_elim_cands:                        3
% 2.53/1.04  pred_elim:                              0
% 2.53/1.04  pred_elim_cl:                           0
% 2.53/1.04  pred_elim_cycles:                       2
% 2.53/1.04  merged_defs:                            0
% 2.53/1.04  merged_defs_ncl:                        0
% 2.53/1.04  bin_hyper_res:                          0
% 2.53/1.04  prep_cycles:                            4
% 2.53/1.04  pred_elim_time:                         0.02
% 2.53/1.04  splitting_time:                         0.
% 2.53/1.04  sem_filter_time:                        0.
% 2.53/1.04  monotx_time:                            0.004
% 2.53/1.04  subtype_inf_time:                       0.
% 2.53/1.04  
% 2.53/1.04  ------ Problem properties
% 2.53/1.04  
% 2.53/1.04  clauses:                                24
% 2.53/1.04  conjectures:                            3
% 2.53/1.04  epr:                                    4
% 2.53/1.04  horn:                                   17
% 2.53/1.04  ground:                                 4
% 2.53/1.04  unary:                                  12
% 2.53/1.04  binary:                                 2
% 2.53/1.04  lits:                                   49
% 2.53/1.04  lits_eq:                                19
% 2.53/1.04  fd_pure:                                0
% 2.53/1.04  fd_pseudo:                              0
% 2.53/1.04  fd_cond:                                1
% 2.53/1.04  fd_pseudo_cond:                         5
% 2.53/1.04  ac_symbols:                             0
% 2.53/1.04  
% 2.53/1.04  ------ Propositional Solver
% 2.53/1.04  
% 2.53/1.04  prop_solver_calls:                      26
% 2.53/1.04  prop_fast_solver_calls:                 758
% 2.53/1.04  smt_solver_calls:                       0
% 2.53/1.04  smt_fast_solver_calls:                  0
% 2.53/1.04  prop_num_of_clauses:                    1778
% 2.53/1.04  prop_preprocess_simplified:             5706
% 2.53/1.04  prop_fo_subsumed:                       16
% 2.53/1.04  prop_solver_time:                       0.
% 2.53/1.04  smt_solver_time:                        0.
% 2.53/1.04  smt_fast_solver_time:                   0.
% 2.53/1.04  prop_fast_solver_time:                  0.
% 2.53/1.04  prop_unsat_core_time:                   0.
% 2.53/1.04  
% 2.53/1.04  ------ QBF
% 2.53/1.04  
% 2.53/1.04  qbf_q_res:                              0
% 2.53/1.04  qbf_num_tautologies:                    0
% 2.53/1.04  qbf_prep_cycles:                        0
% 2.53/1.04  
% 2.53/1.04  ------ BMC1
% 2.53/1.04  
% 2.53/1.04  bmc1_current_bound:                     -1
% 2.53/1.04  bmc1_last_solved_bound:                 -1
% 2.53/1.04  bmc1_unsat_core_size:                   -1
% 2.53/1.04  bmc1_unsat_core_parents_size:           -1
% 2.53/1.04  bmc1_merge_next_fun:                    0
% 2.53/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.04  
% 2.53/1.04  ------ Instantiation
% 2.53/1.04  
% 2.53/1.04  inst_num_of_clauses:                    494
% 2.53/1.04  inst_num_in_passive:                    113
% 2.53/1.04  inst_num_in_active:                     203
% 2.53/1.04  inst_num_in_unprocessed:                178
% 2.53/1.04  inst_num_of_loops:                      260
% 2.53/1.04  inst_num_of_learning_restarts:          0
% 2.53/1.04  inst_num_moves_active_passive:          56
% 2.53/1.04  inst_lit_activity:                      0
% 2.53/1.04  inst_lit_activity_moves:                0
% 2.53/1.04  inst_num_tautologies:                   0
% 2.53/1.04  inst_num_prop_implied:                  0
% 2.53/1.04  inst_num_existing_simplified:           0
% 2.53/1.04  inst_num_eq_res_simplified:             0
% 2.53/1.04  inst_num_child_elim:                    0
% 2.53/1.04  inst_num_of_dismatching_blockings:      389
% 2.53/1.04  inst_num_of_non_proper_insts:           542
% 2.53/1.04  inst_num_of_duplicates:                 0
% 2.53/1.04  inst_inst_num_from_inst_to_res:         0
% 2.53/1.04  inst_dismatching_checking_time:         0.
% 2.53/1.04  
% 2.53/1.04  ------ Resolution
% 2.53/1.04  
% 2.53/1.04  res_num_of_clauses:                     0
% 2.53/1.04  res_num_in_passive:                     0
% 2.53/1.04  res_num_in_active:                      0
% 2.53/1.04  res_num_of_loops:                       117
% 2.53/1.04  res_forward_subset_subsumed:            89
% 2.53/1.04  res_backward_subset_subsumed:           0
% 2.53/1.04  res_forward_subsumed:                   0
% 2.53/1.04  res_backward_subsumed:                  0
% 2.53/1.04  res_forward_subsumption_resolution:     0
% 2.53/1.04  res_backward_subsumption_resolution:    0
% 2.53/1.04  res_clause_to_clause_subsumption:       457
% 2.53/1.04  res_orphan_elimination:                 0
% 2.53/1.04  res_tautology_del:                      36
% 2.53/1.04  res_num_eq_res_simplified:              0
% 2.53/1.04  res_num_sel_changes:                    0
% 2.53/1.04  res_moves_from_active_to_pass:          0
% 2.53/1.04  
% 2.53/1.04  ------ Superposition
% 2.53/1.04  
% 2.53/1.04  sup_time_total:                         0.
% 2.53/1.04  sup_time_generating:                    0.
% 2.53/1.04  sup_time_sim_full:                      0.
% 2.53/1.04  sup_time_sim_immed:                     0.
% 2.53/1.04  
% 2.53/1.04  sup_num_of_clauses:                     60
% 2.53/1.04  sup_num_in_active:                      30
% 2.53/1.04  sup_num_in_passive:                     30
% 2.53/1.04  sup_num_of_loops:                       51
% 2.53/1.04  sup_fw_superposition:                   57
% 2.53/1.04  sup_bw_superposition:                   85
% 2.53/1.04  sup_immediate_simplified:               17
% 2.53/1.04  sup_given_eliminated:                   0
% 2.53/1.04  comparisons_done:                       0
% 2.53/1.04  comparisons_avoided:                    24
% 2.53/1.04  
% 2.53/1.04  ------ Simplifications
% 2.53/1.04  
% 2.53/1.04  
% 2.53/1.04  sim_fw_subset_subsumed:                 4
% 2.53/1.04  sim_bw_subset_subsumed:                 32
% 2.53/1.04  sim_fw_subsumed:                        10
% 2.53/1.04  sim_bw_subsumed:                        0
% 2.53/1.04  sim_fw_subsumption_res:                 1
% 2.53/1.04  sim_bw_subsumption_res:                 0
% 2.53/1.04  sim_tautology_del:                      6
% 2.53/1.04  sim_eq_tautology_del:                   25
% 2.53/1.04  sim_eq_res_simp:                        1
% 2.53/1.04  sim_fw_demodulated:                     2
% 2.53/1.04  sim_bw_demodulated:                     7
% 2.53/1.04  sim_light_normalised:                   3
% 2.53/1.04  sim_joinable_taut:                      0
% 2.53/1.04  sim_joinable_simp:                      0
% 2.53/1.04  sim_ac_normalised:                      0
% 2.53/1.04  sim_smt_subsumption:                    0
% 2.53/1.04  
%------------------------------------------------------------------------------
