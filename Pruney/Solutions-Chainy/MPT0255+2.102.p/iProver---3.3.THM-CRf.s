%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:32 EST 2020

% Result     : Theorem 43.99s
% Output     : CNFRefutation 43.99s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 230 expanded)
%              Number of clauses        :   34 (  38 expanded)
%              Number of leaves         :   18 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  230 ( 390 expanded)
%              Number of equality atoms :  148 ( 290 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f66,f79,f79])).

fof(f26,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f26])).

fof(f33,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f27])).

fof(f41,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f41])).

fof(f77,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f19,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f81,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f102,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f77,f82,f81])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f82])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f107,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f97])).

fof(f108,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f107])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_22,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1599,plain,
    ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22,c_24])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_974,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8084,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_974])).

cnf(c_15796,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_8084])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_977,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_97854,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15796,c_977])).

cnf(c_1508,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_765,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1097,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1295,plain,
    ( ~ r1_tarski(X0,k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)))
    | r1_tarski(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1419,plain,
    ( r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)))
    | X0 != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_2019,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)))
    | r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_759,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5102,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_1325,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),X0)
    | k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1824,plain,
    ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
    | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_10595,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_92531,plain,
    ( r1_tarski(k1_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_100113,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_97854,c_24,c_1508,c_2019,c_5102,c_10595,c_92531])).

cnf(c_19,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_968,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_100131,plain,
    ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_100113,c_968])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_177,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_178,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_179,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_181,plain,
    ( r2_hidden(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_100131,c_181])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 43.99/6.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.99/6.02  
% 43.99/6.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.99/6.02  
% 43.99/6.02  ------  iProver source info
% 43.99/6.02  
% 43.99/6.02  git: date: 2020-06-30 10:37:57 +0100
% 43.99/6.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.99/6.02  git: non_committed_changes: false
% 43.99/6.02  git: last_make_outside_of_git: false
% 43.99/6.02  
% 43.99/6.02  ------ 
% 43.99/6.02  
% 43.99/6.02  ------ Input Options
% 43.99/6.02  
% 43.99/6.02  --out_options                           all
% 43.99/6.02  --tptp_safe_out                         true
% 43.99/6.02  --problem_path                          ""
% 43.99/6.02  --include_path                          ""
% 43.99/6.02  --clausifier                            res/vclausify_rel
% 43.99/6.02  --clausifier_options                    ""
% 43.99/6.02  --stdin                                 false
% 43.99/6.02  --stats_out                             all
% 43.99/6.02  
% 43.99/6.02  ------ General Options
% 43.99/6.02  
% 43.99/6.02  --fof                                   false
% 43.99/6.02  --time_out_real                         305.
% 43.99/6.02  --time_out_virtual                      -1.
% 43.99/6.02  --symbol_type_check                     false
% 43.99/6.02  --clausify_out                          false
% 43.99/6.02  --sig_cnt_out                           false
% 43.99/6.02  --trig_cnt_out                          false
% 43.99/6.02  --trig_cnt_out_tolerance                1.
% 43.99/6.02  --trig_cnt_out_sk_spl                   false
% 43.99/6.02  --abstr_cl_out                          false
% 43.99/6.02  
% 43.99/6.02  ------ Global Options
% 43.99/6.02  
% 43.99/6.02  --schedule                              default
% 43.99/6.02  --add_important_lit                     false
% 43.99/6.02  --prop_solver_per_cl                    1000
% 43.99/6.02  --min_unsat_core                        false
% 43.99/6.02  --soft_assumptions                      false
% 43.99/6.02  --soft_lemma_size                       3
% 43.99/6.02  --prop_impl_unit_size                   0
% 43.99/6.02  --prop_impl_unit                        []
% 43.99/6.02  --share_sel_clauses                     true
% 43.99/6.02  --reset_solvers                         false
% 43.99/6.02  --bc_imp_inh                            [conj_cone]
% 43.99/6.02  --conj_cone_tolerance                   3.
% 43.99/6.02  --extra_neg_conj                        none
% 43.99/6.02  --large_theory_mode                     true
% 43.99/6.02  --prolific_symb_bound                   200
% 43.99/6.02  --lt_threshold                          2000
% 43.99/6.02  --clause_weak_htbl                      true
% 43.99/6.02  --gc_record_bc_elim                     false
% 43.99/6.02  
% 43.99/6.02  ------ Preprocessing Options
% 43.99/6.02  
% 43.99/6.02  --preprocessing_flag                    true
% 43.99/6.02  --time_out_prep_mult                    0.1
% 43.99/6.02  --splitting_mode                        input
% 43.99/6.02  --splitting_grd                         true
% 43.99/6.02  --splitting_cvd                         false
% 43.99/6.02  --splitting_cvd_svl                     false
% 43.99/6.02  --splitting_nvd                         32
% 43.99/6.02  --sub_typing                            true
% 43.99/6.02  --prep_gs_sim                           true
% 43.99/6.02  --prep_unflatten                        true
% 43.99/6.02  --prep_res_sim                          true
% 43.99/6.02  --prep_upred                            true
% 43.99/6.02  --prep_sem_filter                       exhaustive
% 43.99/6.02  --prep_sem_filter_out                   false
% 43.99/6.02  --pred_elim                             true
% 43.99/6.02  --res_sim_input                         true
% 43.99/6.02  --eq_ax_congr_red                       true
% 43.99/6.02  --pure_diseq_elim                       true
% 43.99/6.02  --brand_transform                       false
% 43.99/6.02  --non_eq_to_eq                          false
% 43.99/6.02  --prep_def_merge                        true
% 43.99/6.02  --prep_def_merge_prop_impl              false
% 43.99/6.02  --prep_def_merge_mbd                    true
% 43.99/6.02  --prep_def_merge_tr_red                 false
% 43.99/6.02  --prep_def_merge_tr_cl                  false
% 43.99/6.02  --smt_preprocessing                     true
% 43.99/6.02  --smt_ac_axioms                         fast
% 43.99/6.02  --preprocessed_out                      false
% 43.99/6.02  --preprocessed_stats                    false
% 43.99/6.02  
% 43.99/6.02  ------ Abstraction refinement Options
% 43.99/6.02  
% 43.99/6.02  --abstr_ref                             []
% 43.99/6.02  --abstr_ref_prep                        false
% 43.99/6.02  --abstr_ref_until_sat                   false
% 43.99/6.02  --abstr_ref_sig_restrict                funpre
% 43.99/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.99/6.02  --abstr_ref_under                       []
% 43.99/6.02  
% 43.99/6.02  ------ SAT Options
% 43.99/6.02  
% 43.99/6.02  --sat_mode                              false
% 43.99/6.02  --sat_fm_restart_options                ""
% 43.99/6.02  --sat_gr_def                            false
% 43.99/6.02  --sat_epr_types                         true
% 43.99/6.02  --sat_non_cyclic_types                  false
% 43.99/6.02  --sat_finite_models                     false
% 43.99/6.02  --sat_fm_lemmas                         false
% 43.99/6.02  --sat_fm_prep                           false
% 43.99/6.02  --sat_fm_uc_incr                        true
% 43.99/6.02  --sat_out_model                         small
% 43.99/6.02  --sat_out_clauses                       false
% 43.99/6.02  
% 43.99/6.02  ------ QBF Options
% 43.99/6.02  
% 43.99/6.02  --qbf_mode                              false
% 43.99/6.02  --qbf_elim_univ                         false
% 43.99/6.02  --qbf_dom_inst                          none
% 43.99/6.02  --qbf_dom_pre_inst                      false
% 43.99/6.02  --qbf_sk_in                             false
% 43.99/6.02  --qbf_pred_elim                         true
% 43.99/6.02  --qbf_split                             512
% 43.99/6.02  
% 43.99/6.02  ------ BMC1 Options
% 43.99/6.02  
% 43.99/6.02  --bmc1_incremental                      false
% 43.99/6.02  --bmc1_axioms                           reachable_all
% 43.99/6.02  --bmc1_min_bound                        0
% 43.99/6.02  --bmc1_max_bound                        -1
% 43.99/6.02  --bmc1_max_bound_default                -1
% 43.99/6.02  --bmc1_symbol_reachability              true
% 43.99/6.02  --bmc1_property_lemmas                  false
% 43.99/6.02  --bmc1_k_induction                      false
% 43.99/6.02  --bmc1_non_equiv_states                 false
% 43.99/6.02  --bmc1_deadlock                         false
% 43.99/6.02  --bmc1_ucm                              false
% 43.99/6.02  --bmc1_add_unsat_core                   none
% 43.99/6.02  --bmc1_unsat_core_children              false
% 43.99/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.99/6.02  --bmc1_out_stat                         full
% 43.99/6.02  --bmc1_ground_init                      false
% 43.99/6.02  --bmc1_pre_inst_next_state              false
% 43.99/6.02  --bmc1_pre_inst_state                   false
% 43.99/6.02  --bmc1_pre_inst_reach_state             false
% 43.99/6.02  --bmc1_out_unsat_core                   false
% 43.99/6.02  --bmc1_aig_witness_out                  false
% 43.99/6.02  --bmc1_verbose                          false
% 43.99/6.02  --bmc1_dump_clauses_tptp                false
% 43.99/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.99/6.02  --bmc1_dump_file                        -
% 43.99/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.99/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.99/6.02  --bmc1_ucm_extend_mode                  1
% 43.99/6.02  --bmc1_ucm_init_mode                    2
% 43.99/6.02  --bmc1_ucm_cone_mode                    none
% 43.99/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.99/6.02  --bmc1_ucm_relax_model                  4
% 43.99/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.99/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.99/6.02  --bmc1_ucm_layered_model                none
% 43.99/6.02  --bmc1_ucm_max_lemma_size               10
% 43.99/6.02  
% 43.99/6.02  ------ AIG Options
% 43.99/6.02  
% 43.99/6.02  --aig_mode                              false
% 43.99/6.02  
% 43.99/6.02  ------ Instantiation Options
% 43.99/6.02  
% 43.99/6.02  --instantiation_flag                    true
% 43.99/6.02  --inst_sos_flag                         true
% 43.99/6.02  --inst_sos_phase                        true
% 43.99/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.99/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.99/6.02  --inst_lit_sel_side                     num_symb
% 43.99/6.02  --inst_solver_per_active                1400
% 43.99/6.02  --inst_solver_calls_frac                1.
% 43.99/6.02  --inst_passive_queue_type               priority_queues
% 43.99/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.99/6.02  --inst_passive_queues_freq              [25;2]
% 43.99/6.02  --inst_dismatching                      true
% 43.99/6.02  --inst_eager_unprocessed_to_passive     true
% 43.99/6.02  --inst_prop_sim_given                   true
% 43.99/6.02  --inst_prop_sim_new                     false
% 43.99/6.02  --inst_subs_new                         false
% 43.99/6.02  --inst_eq_res_simp                      false
% 43.99/6.02  --inst_subs_given                       false
% 43.99/6.02  --inst_orphan_elimination               true
% 43.99/6.02  --inst_learning_loop_flag               true
% 43.99/6.02  --inst_learning_start                   3000
% 43.99/6.02  --inst_learning_factor                  2
% 43.99/6.02  --inst_start_prop_sim_after_learn       3
% 43.99/6.02  --inst_sel_renew                        solver
% 43.99/6.02  --inst_lit_activity_flag                true
% 43.99/6.02  --inst_restr_to_given                   false
% 43.99/6.02  --inst_activity_threshold               500
% 43.99/6.02  --inst_out_proof                        true
% 43.99/6.02  
% 43.99/6.02  ------ Resolution Options
% 43.99/6.02  
% 43.99/6.02  --resolution_flag                       true
% 43.99/6.02  --res_lit_sel                           adaptive
% 43.99/6.02  --res_lit_sel_side                      none
% 43.99/6.02  --res_ordering                          kbo
% 43.99/6.02  --res_to_prop_solver                    active
% 43.99/6.02  --res_prop_simpl_new                    false
% 43.99/6.02  --res_prop_simpl_given                  true
% 43.99/6.02  --res_passive_queue_type                priority_queues
% 43.99/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.99/6.02  --res_passive_queues_freq               [15;5]
% 43.99/6.02  --res_forward_subs                      full
% 43.99/6.02  --res_backward_subs                     full
% 43.99/6.02  --res_forward_subs_resolution           true
% 43.99/6.02  --res_backward_subs_resolution          true
% 43.99/6.02  --res_orphan_elimination                true
% 43.99/6.02  --res_time_limit                        2.
% 43.99/6.02  --res_out_proof                         true
% 43.99/6.02  
% 43.99/6.02  ------ Superposition Options
% 43.99/6.02  
% 43.99/6.02  --superposition_flag                    true
% 43.99/6.02  --sup_passive_queue_type                priority_queues
% 43.99/6.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.99/6.02  --sup_passive_queues_freq               [8;1;4]
% 43.99/6.02  --demod_completeness_check              fast
% 43.99/6.02  --demod_use_ground                      true
% 43.99/6.02  --sup_to_prop_solver                    passive
% 43.99/6.02  --sup_prop_simpl_new                    true
% 43.99/6.02  --sup_prop_simpl_given                  true
% 43.99/6.02  --sup_fun_splitting                     true
% 43.99/6.02  --sup_smt_interval                      50000
% 43.99/6.02  
% 43.99/6.02  ------ Superposition Simplification Setup
% 43.99/6.02  
% 43.99/6.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.99/6.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.99/6.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.99/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.99/6.02  --sup_full_triv                         [TrivRules;PropSubs]
% 43.99/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.99/6.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.99/6.02  --sup_immed_triv                        [TrivRules]
% 43.99/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.99/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.99/6.02  --sup_immed_bw_main                     []
% 43.99/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.99/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.99/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.99/6.02  --sup_input_bw                          []
% 43.99/6.02  
% 43.99/6.02  ------ Combination Options
% 43.99/6.02  
% 43.99/6.02  --comb_res_mult                         3
% 43.99/6.02  --comb_sup_mult                         2
% 43.99/6.02  --comb_inst_mult                        10
% 43.99/6.02  
% 43.99/6.02  ------ Debug Options
% 43.99/6.02  
% 43.99/6.02  --dbg_backtrace                         false
% 43.99/6.02  --dbg_dump_prop_clauses                 false
% 43.99/6.02  --dbg_dump_prop_clauses_file            -
% 43.99/6.02  --dbg_out_stat                          false
% 43.99/6.02  ------ Parsing...
% 43.99/6.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.99/6.02  
% 43.99/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 43.99/6.02  
% 43.99/6.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.99/6.02  
% 43.99/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.99/6.02  ------ Proving...
% 43.99/6.02  ------ Problem Properties 
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  clauses                                 23
% 43.99/6.02  conjectures                             1
% 43.99/6.02  EPR                                     4
% 43.99/6.02  Horn                                    21
% 43.99/6.02  unary                                   17
% 43.99/6.02  binary                                  0
% 43.99/6.02  lits                                    38
% 43.99/6.02  lits eq                                 24
% 43.99/6.02  fd_pure                                 0
% 43.99/6.02  fd_pseudo                               0
% 43.99/6.02  fd_cond                                 0
% 43.99/6.02  fd_pseudo_cond                          5
% 43.99/6.02  AC symbols                              0
% 43.99/6.02  
% 43.99/6.02  ------ Schedule dynamic 5 is on 
% 43.99/6.02  
% 43.99/6.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  ------ 
% 43.99/6.02  Current options:
% 43.99/6.02  ------ 
% 43.99/6.02  
% 43.99/6.02  ------ Input Options
% 43.99/6.02  
% 43.99/6.02  --out_options                           all
% 43.99/6.02  --tptp_safe_out                         true
% 43.99/6.02  --problem_path                          ""
% 43.99/6.02  --include_path                          ""
% 43.99/6.02  --clausifier                            res/vclausify_rel
% 43.99/6.02  --clausifier_options                    ""
% 43.99/6.02  --stdin                                 false
% 43.99/6.02  --stats_out                             all
% 43.99/6.02  
% 43.99/6.02  ------ General Options
% 43.99/6.02  
% 43.99/6.02  --fof                                   false
% 43.99/6.02  --time_out_real                         305.
% 43.99/6.02  --time_out_virtual                      -1.
% 43.99/6.02  --symbol_type_check                     false
% 43.99/6.02  --clausify_out                          false
% 43.99/6.02  --sig_cnt_out                           false
% 43.99/6.02  --trig_cnt_out                          false
% 43.99/6.02  --trig_cnt_out_tolerance                1.
% 43.99/6.02  --trig_cnt_out_sk_spl                   false
% 43.99/6.02  --abstr_cl_out                          false
% 43.99/6.02  
% 43.99/6.02  ------ Global Options
% 43.99/6.02  
% 43.99/6.02  --schedule                              default
% 43.99/6.02  --add_important_lit                     false
% 43.99/6.02  --prop_solver_per_cl                    1000
% 43.99/6.02  --min_unsat_core                        false
% 43.99/6.02  --soft_assumptions                      false
% 43.99/6.02  --soft_lemma_size                       3
% 43.99/6.02  --prop_impl_unit_size                   0
% 43.99/6.02  --prop_impl_unit                        []
% 43.99/6.02  --share_sel_clauses                     true
% 43.99/6.02  --reset_solvers                         false
% 43.99/6.02  --bc_imp_inh                            [conj_cone]
% 43.99/6.02  --conj_cone_tolerance                   3.
% 43.99/6.02  --extra_neg_conj                        none
% 43.99/6.02  --large_theory_mode                     true
% 43.99/6.02  --prolific_symb_bound                   200
% 43.99/6.02  --lt_threshold                          2000
% 43.99/6.02  --clause_weak_htbl                      true
% 43.99/6.02  --gc_record_bc_elim                     false
% 43.99/6.02  
% 43.99/6.02  ------ Preprocessing Options
% 43.99/6.02  
% 43.99/6.02  --preprocessing_flag                    true
% 43.99/6.02  --time_out_prep_mult                    0.1
% 43.99/6.02  --splitting_mode                        input
% 43.99/6.02  --splitting_grd                         true
% 43.99/6.02  --splitting_cvd                         false
% 43.99/6.02  --splitting_cvd_svl                     false
% 43.99/6.02  --splitting_nvd                         32
% 43.99/6.02  --sub_typing                            true
% 43.99/6.02  --prep_gs_sim                           true
% 43.99/6.02  --prep_unflatten                        true
% 43.99/6.02  --prep_res_sim                          true
% 43.99/6.02  --prep_upred                            true
% 43.99/6.02  --prep_sem_filter                       exhaustive
% 43.99/6.02  --prep_sem_filter_out                   false
% 43.99/6.02  --pred_elim                             true
% 43.99/6.02  --res_sim_input                         true
% 43.99/6.02  --eq_ax_congr_red                       true
% 43.99/6.02  --pure_diseq_elim                       true
% 43.99/6.02  --brand_transform                       false
% 43.99/6.02  --non_eq_to_eq                          false
% 43.99/6.02  --prep_def_merge                        true
% 43.99/6.02  --prep_def_merge_prop_impl              false
% 43.99/6.02  --prep_def_merge_mbd                    true
% 43.99/6.02  --prep_def_merge_tr_red                 false
% 43.99/6.02  --prep_def_merge_tr_cl                  false
% 43.99/6.02  --smt_preprocessing                     true
% 43.99/6.02  --smt_ac_axioms                         fast
% 43.99/6.02  --preprocessed_out                      false
% 43.99/6.02  --preprocessed_stats                    false
% 43.99/6.02  
% 43.99/6.02  ------ Abstraction refinement Options
% 43.99/6.02  
% 43.99/6.02  --abstr_ref                             []
% 43.99/6.02  --abstr_ref_prep                        false
% 43.99/6.02  --abstr_ref_until_sat                   false
% 43.99/6.02  --abstr_ref_sig_restrict                funpre
% 43.99/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.99/6.02  --abstr_ref_under                       []
% 43.99/6.02  
% 43.99/6.02  ------ SAT Options
% 43.99/6.02  
% 43.99/6.02  --sat_mode                              false
% 43.99/6.02  --sat_fm_restart_options                ""
% 43.99/6.02  --sat_gr_def                            false
% 43.99/6.02  --sat_epr_types                         true
% 43.99/6.02  --sat_non_cyclic_types                  false
% 43.99/6.02  --sat_finite_models                     false
% 43.99/6.02  --sat_fm_lemmas                         false
% 43.99/6.02  --sat_fm_prep                           false
% 43.99/6.02  --sat_fm_uc_incr                        true
% 43.99/6.02  --sat_out_model                         small
% 43.99/6.02  --sat_out_clauses                       false
% 43.99/6.02  
% 43.99/6.02  ------ QBF Options
% 43.99/6.02  
% 43.99/6.02  --qbf_mode                              false
% 43.99/6.02  --qbf_elim_univ                         false
% 43.99/6.02  --qbf_dom_inst                          none
% 43.99/6.02  --qbf_dom_pre_inst                      false
% 43.99/6.02  --qbf_sk_in                             false
% 43.99/6.02  --qbf_pred_elim                         true
% 43.99/6.02  --qbf_split                             512
% 43.99/6.02  
% 43.99/6.02  ------ BMC1 Options
% 43.99/6.02  
% 43.99/6.02  --bmc1_incremental                      false
% 43.99/6.02  --bmc1_axioms                           reachable_all
% 43.99/6.02  --bmc1_min_bound                        0
% 43.99/6.02  --bmc1_max_bound                        -1
% 43.99/6.02  --bmc1_max_bound_default                -1
% 43.99/6.02  --bmc1_symbol_reachability              true
% 43.99/6.02  --bmc1_property_lemmas                  false
% 43.99/6.02  --bmc1_k_induction                      false
% 43.99/6.02  --bmc1_non_equiv_states                 false
% 43.99/6.02  --bmc1_deadlock                         false
% 43.99/6.02  --bmc1_ucm                              false
% 43.99/6.02  --bmc1_add_unsat_core                   none
% 43.99/6.02  --bmc1_unsat_core_children              false
% 43.99/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.99/6.02  --bmc1_out_stat                         full
% 43.99/6.02  --bmc1_ground_init                      false
% 43.99/6.02  --bmc1_pre_inst_next_state              false
% 43.99/6.02  --bmc1_pre_inst_state                   false
% 43.99/6.02  --bmc1_pre_inst_reach_state             false
% 43.99/6.02  --bmc1_out_unsat_core                   false
% 43.99/6.02  --bmc1_aig_witness_out                  false
% 43.99/6.02  --bmc1_verbose                          false
% 43.99/6.02  --bmc1_dump_clauses_tptp                false
% 43.99/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.99/6.02  --bmc1_dump_file                        -
% 43.99/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.99/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.99/6.02  --bmc1_ucm_extend_mode                  1
% 43.99/6.02  --bmc1_ucm_init_mode                    2
% 43.99/6.02  --bmc1_ucm_cone_mode                    none
% 43.99/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.99/6.02  --bmc1_ucm_relax_model                  4
% 43.99/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.99/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.99/6.02  --bmc1_ucm_layered_model                none
% 43.99/6.02  --bmc1_ucm_max_lemma_size               10
% 43.99/6.02  
% 43.99/6.02  ------ AIG Options
% 43.99/6.02  
% 43.99/6.02  --aig_mode                              false
% 43.99/6.02  
% 43.99/6.02  ------ Instantiation Options
% 43.99/6.02  
% 43.99/6.02  --instantiation_flag                    true
% 43.99/6.02  --inst_sos_flag                         true
% 43.99/6.02  --inst_sos_phase                        true
% 43.99/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.99/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.99/6.02  --inst_lit_sel_side                     none
% 43.99/6.02  --inst_solver_per_active                1400
% 43.99/6.02  --inst_solver_calls_frac                1.
% 43.99/6.02  --inst_passive_queue_type               priority_queues
% 43.99/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.99/6.02  --inst_passive_queues_freq              [25;2]
% 43.99/6.02  --inst_dismatching                      true
% 43.99/6.02  --inst_eager_unprocessed_to_passive     true
% 43.99/6.02  --inst_prop_sim_given                   true
% 43.99/6.02  --inst_prop_sim_new                     false
% 43.99/6.02  --inst_subs_new                         false
% 43.99/6.02  --inst_eq_res_simp                      false
% 43.99/6.02  --inst_subs_given                       false
% 43.99/6.02  --inst_orphan_elimination               true
% 43.99/6.02  --inst_learning_loop_flag               true
% 43.99/6.02  --inst_learning_start                   3000
% 43.99/6.02  --inst_learning_factor                  2
% 43.99/6.02  --inst_start_prop_sim_after_learn       3
% 43.99/6.02  --inst_sel_renew                        solver
% 43.99/6.02  --inst_lit_activity_flag                true
% 43.99/6.02  --inst_restr_to_given                   false
% 43.99/6.02  --inst_activity_threshold               500
% 43.99/6.02  --inst_out_proof                        true
% 43.99/6.02  
% 43.99/6.02  ------ Resolution Options
% 43.99/6.02  
% 43.99/6.02  --resolution_flag                       false
% 43.99/6.02  --res_lit_sel                           adaptive
% 43.99/6.02  --res_lit_sel_side                      none
% 43.99/6.02  --res_ordering                          kbo
% 43.99/6.02  --res_to_prop_solver                    active
% 43.99/6.02  --res_prop_simpl_new                    false
% 43.99/6.02  --res_prop_simpl_given                  true
% 43.99/6.02  --res_passive_queue_type                priority_queues
% 43.99/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.99/6.02  --res_passive_queues_freq               [15;5]
% 43.99/6.02  --res_forward_subs                      full
% 43.99/6.02  --res_backward_subs                     full
% 43.99/6.02  --res_forward_subs_resolution           true
% 43.99/6.02  --res_backward_subs_resolution          true
% 43.99/6.02  --res_orphan_elimination                true
% 43.99/6.02  --res_time_limit                        2.
% 43.99/6.02  --res_out_proof                         true
% 43.99/6.02  
% 43.99/6.02  ------ Superposition Options
% 43.99/6.02  
% 43.99/6.02  --superposition_flag                    true
% 43.99/6.02  --sup_passive_queue_type                priority_queues
% 43.99/6.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.99/6.02  --sup_passive_queues_freq               [8;1;4]
% 43.99/6.02  --demod_completeness_check              fast
% 43.99/6.02  --demod_use_ground                      true
% 43.99/6.02  --sup_to_prop_solver                    passive
% 43.99/6.02  --sup_prop_simpl_new                    true
% 43.99/6.02  --sup_prop_simpl_given                  true
% 43.99/6.02  --sup_fun_splitting                     true
% 43.99/6.02  --sup_smt_interval                      50000
% 43.99/6.02  
% 43.99/6.02  ------ Superposition Simplification Setup
% 43.99/6.02  
% 43.99/6.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.99/6.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.99/6.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.99/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.99/6.02  --sup_full_triv                         [TrivRules;PropSubs]
% 43.99/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.99/6.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.99/6.02  --sup_immed_triv                        [TrivRules]
% 43.99/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.99/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.99/6.02  --sup_immed_bw_main                     []
% 43.99/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.99/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.99/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.99/6.02  --sup_input_bw                          []
% 43.99/6.02  
% 43.99/6.02  ------ Combination Options
% 43.99/6.02  
% 43.99/6.02  --comb_res_mult                         3
% 43.99/6.02  --comb_sup_mult                         2
% 43.99/6.02  --comb_inst_mult                        10
% 43.99/6.02  
% 43.99/6.02  ------ Debug Options
% 43.99/6.02  
% 43.99/6.02  --dbg_backtrace                         false
% 43.99/6.02  --dbg_dump_prop_clauses                 false
% 43.99/6.02  --dbg_dump_prop_clauses_file            -
% 43.99/6.02  --dbg_out_stat                          false
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  ------ Proving...
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  % SZS status Theorem for theBenchmark.p
% 43.99/6.02  
% 43.99/6.02  % SZS output start CNFRefutation for theBenchmark.p
% 43.99/6.02  
% 43.99/6.02  fof(f15,axiom,(
% 43.99/6.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f66,plain,(
% 43.99/6.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f15])).
% 43.99/6.02  
% 43.99/6.02  fof(f21,axiom,(
% 43.99/6.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f72,plain,(
% 43.99/6.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f21])).
% 43.99/6.02  
% 43.99/6.02  fof(f22,axiom,(
% 43.99/6.02    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f73,plain,(
% 43.99/6.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f22])).
% 43.99/6.02  
% 43.99/6.02  fof(f23,axiom,(
% 43.99/6.02    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f74,plain,(
% 43.99/6.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f23])).
% 43.99/6.02  
% 43.99/6.02  fof(f78,plain,(
% 43.99/6.02    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.99/6.02    inference(definition_unfolding,[],[f73,f74])).
% 43.99/6.02  
% 43.99/6.02  fof(f79,plain,(
% 43.99/6.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 43.99/6.02    inference(definition_unfolding,[],[f72,f78])).
% 43.99/6.02  
% 43.99/6.02  fof(f100,plain,(
% 43.99/6.02    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 43.99/6.02    inference(definition_unfolding,[],[f66,f79,f79])).
% 43.99/6.02  
% 43.99/6.02  fof(f26,conjecture,(
% 43.99/6.02    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f27,negated_conjecture,(
% 43.99/6.02    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 43.99/6.02    inference(negated_conjecture,[],[f26])).
% 43.99/6.02  
% 43.99/6.02  fof(f33,plain,(
% 43.99/6.02    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 43.99/6.02    inference(ennf_transformation,[],[f27])).
% 43.99/6.02  
% 43.99/6.02  fof(f41,plain,(
% 43.99/6.02    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 43.99/6.02    introduced(choice_axiom,[])).
% 43.99/6.02  
% 43.99/6.02  fof(f42,plain,(
% 43.99/6.02    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 43.99/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f41])).
% 43.99/6.02  
% 43.99/6.02  fof(f77,plain,(
% 43.99/6.02    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 43.99/6.02    inference(cnf_transformation,[],[f42])).
% 43.99/6.02  
% 43.99/6.02  fof(f25,axiom,(
% 43.99/6.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f76,plain,(
% 43.99/6.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.99/6.02    inference(cnf_transformation,[],[f25])).
% 43.99/6.02  
% 43.99/6.02  fof(f82,plain,(
% 43.99/6.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 43.99/6.02    inference(definition_unfolding,[],[f76,f81])).
% 43.99/6.02  
% 43.99/6.02  fof(f19,axiom,(
% 43.99/6.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f70,plain,(
% 43.99/6.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f19])).
% 43.99/6.02  
% 43.99/6.02  fof(f20,axiom,(
% 43.99/6.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f71,plain,(
% 43.99/6.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f20])).
% 43.99/6.02  
% 43.99/6.02  fof(f80,plain,(
% 43.99/6.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 43.99/6.02    inference(definition_unfolding,[],[f71,f79])).
% 43.99/6.02  
% 43.99/6.02  fof(f81,plain,(
% 43.99/6.02    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.99/6.02    inference(definition_unfolding,[],[f70,f80])).
% 43.99/6.02  
% 43.99/6.02  fof(f102,plain,(
% 43.99/6.02    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3))),
% 43.99/6.02    inference(definition_unfolding,[],[f77,f82,f81])).
% 43.99/6.02  
% 43.99/6.02  fof(f10,axiom,(
% 43.99/6.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f54,plain,(
% 43.99/6.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 43.99/6.02    inference(cnf_transformation,[],[f10])).
% 43.99/6.02  
% 43.99/6.02  fof(f91,plain,(
% 43.99/6.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 43.99/6.02    inference(definition_unfolding,[],[f54,f82])).
% 43.99/6.02  
% 43.99/6.02  fof(f5,axiom,(
% 43.99/6.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f34,plain,(
% 43.99/6.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.99/6.02    inference(nnf_transformation,[],[f5])).
% 43.99/6.02  
% 43.99/6.02  fof(f35,plain,(
% 43.99/6.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.99/6.02    inference(flattening,[],[f34])).
% 43.99/6.02  
% 43.99/6.02  fof(f49,plain,(
% 43.99/6.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f35])).
% 43.99/6.02  
% 43.99/6.02  fof(f7,axiom,(
% 43.99/6.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f51,plain,(
% 43.99/6.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f7])).
% 43.99/6.02  
% 43.99/6.02  fof(f14,axiom,(
% 43.99/6.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f32,plain,(
% 43.99/6.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 43.99/6.02    inference(ennf_transformation,[],[f14])).
% 43.99/6.02  
% 43.99/6.02  fof(f36,plain,(
% 43.99/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.99/6.02    inference(nnf_transformation,[],[f32])).
% 43.99/6.02  
% 43.99/6.02  fof(f37,plain,(
% 43.99/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.99/6.02    inference(flattening,[],[f36])).
% 43.99/6.02  
% 43.99/6.02  fof(f38,plain,(
% 43.99/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.99/6.02    inference(rectify,[],[f37])).
% 43.99/6.02  
% 43.99/6.02  fof(f39,plain,(
% 43.99/6.02    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 43.99/6.02    introduced(choice_axiom,[])).
% 43.99/6.02  
% 43.99/6.02  fof(f40,plain,(
% 43.99/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.99/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 43.99/6.02  
% 43.99/6.02  fof(f60,plain,(
% 43.99/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 43.99/6.02    inference(cnf_transformation,[],[f40])).
% 43.99/6.02  
% 43.99/6.02  fof(f97,plain,(
% 43.99/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 43.99/6.02    inference(definition_unfolding,[],[f60,f80])).
% 43.99/6.02  
% 43.99/6.02  fof(f107,plain,(
% 43.99/6.02    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 43.99/6.02    inference(equality_resolution,[],[f97])).
% 43.99/6.02  
% 43.99/6.02  fof(f108,plain,(
% 43.99/6.02    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 43.99/6.02    inference(equality_resolution,[],[f107])).
% 43.99/6.02  
% 43.99/6.02  fof(f1,axiom,(
% 43.99/6.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f30,plain,(
% 43.99/6.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 43.99/6.02    inference(unused_predicate_definition_removal,[],[f1])).
% 43.99/6.02  
% 43.99/6.02  fof(f31,plain,(
% 43.99/6.02    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 43.99/6.02    inference(ennf_transformation,[],[f30])).
% 43.99/6.02  
% 43.99/6.02  fof(f43,plain,(
% 43.99/6.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 43.99/6.02    inference(cnf_transformation,[],[f31])).
% 43.99/6.02  
% 43.99/6.02  fof(f2,axiom,(
% 43.99/6.02    v1_xboole_0(k1_xboole_0)),
% 43.99/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.99/6.02  
% 43.99/6.02  fof(f44,plain,(
% 43.99/6.02    v1_xboole_0(k1_xboole_0)),
% 43.99/6.02    inference(cnf_transformation,[],[f2])).
% 43.99/6.02  
% 43.99/6.02  cnf(c_22,plain,
% 43.99/6.02      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
% 43.99/6.02      inference(cnf_transformation,[],[f100]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_24,negated_conjecture,
% 43.99/6.02      ( k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
% 43.99/6.02      inference(cnf_transformation,[],[f102]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1599,plain,
% 43.99/6.02      ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k1_xboole_0 ),
% 43.99/6.02      inference(demodulation,[status(thm)],[c_22,c_24]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_11,plain,
% 43.99/6.02      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 43.99/6.02      inference(cnf_transformation,[],[f91]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_974,plain,
% 43.99/6.02      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 43.99/6.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_8084,plain,
% 43.99/6.02      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 43.99/6.02      inference(superposition,[status(thm)],[c_22,c_974]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_15796,plain,
% 43.99/6.02      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = iProver_top ),
% 43.99/6.02      inference(superposition,[status(thm)],[c_1599,c_8084]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_5,plain,
% 43.99/6.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 43.99/6.02      inference(cnf_transformation,[],[f49]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_977,plain,
% 43.99/6.02      ( X0 = X1
% 43.99/6.02      | r1_tarski(X0,X1) != iProver_top
% 43.99/6.02      | r1_tarski(X1,X0) != iProver_top ),
% 43.99/6.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_97854,plain,
% 43.99/6.02      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 43.99/6.02      | r1_tarski(k1_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 43.99/6.02      inference(superposition,[status(thm)],[c_15796,c_977]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1508,plain,
% 43.99/6.02      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3))) ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_11]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_765,plain,
% 43.99/6.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.99/6.02      theory(equality) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1097,plain,
% 43.99/6.02      ( ~ r1_tarski(X0,X1)
% 43.99/6.02      | r1_tarski(X2,k1_xboole_0)
% 43.99/6.02      | X2 != X0
% 43.99/6.02      | k1_xboole_0 != X1 ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_765]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1295,plain,
% 43.99/6.02      ( ~ r1_tarski(X0,k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)))
% 43.99/6.02      | r1_tarski(X1,k1_xboole_0)
% 43.99/6.02      | X1 != X0
% 43.99/6.02      | k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_1097]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1419,plain,
% 43.99/6.02      ( r1_tarski(X0,k1_xboole_0)
% 43.99/6.02      | ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)))
% 43.99/6.02      | X0 != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 43.99/6.02      | k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_1295]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_2019,plain,
% 43.99/6.02      ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)))
% 43.99/6.02      | r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)
% 43.99/6.02      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 43.99/6.02      | k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_1419]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_759,plain,( X0 = X0 ),theory(equality) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_5102,plain,
% 43.99/6.02      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_759]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1325,plain,
% 43.99/6.02      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 43.99/6.02      | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),X0)
% 43.99/6.02      | k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = X0 ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_5]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1824,plain,
% 43.99/6.02      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k1_xboole_0)
% 43.99/6.02      | ~ r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
% 43.99/6.02      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_xboole_0 ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_1325]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_10595,plain,
% 43.99/6.02      ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)
% 43.99/6.02      | ~ r1_tarski(k1_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 43.99/6.02      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_1824]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_8,plain,
% 43.99/6.02      ( r1_tarski(k1_xboole_0,X0) ),
% 43.99/6.02      inference(cnf_transformation,[],[f51]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_92531,plain,
% 43.99/6.02      ( r1_tarski(k1_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_8]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_100113,plain,
% 43.99/6.02      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 43.99/6.02      inference(global_propositional_subsumption,
% 43.99/6.02                [status(thm)],
% 43.99/6.02                [c_97854,c_24,c_1508,c_2019,c_5102,c_10595,c_92531]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_19,plain,
% 43.99/6.02      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
% 43.99/6.02      inference(cnf_transformation,[],[f108]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_968,plain,
% 43.99/6.02      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 43.99/6.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_100131,plain,
% 43.99/6.02      ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 43.99/6.02      inference(superposition,[status(thm)],[c_100113,c_968]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_1,plain,
% 43.99/6.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 43.99/6.02      inference(cnf_transformation,[],[f43]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_2,plain,
% 43.99/6.02      ( v1_xboole_0(k1_xboole_0) ),
% 43.99/6.02      inference(cnf_transformation,[],[f44]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_177,plain,
% 43.99/6.02      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 43.99/6.02      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_178,plain,
% 43.99/6.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 43.99/6.02      inference(unflattening,[status(thm)],[c_177]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_179,plain,
% 43.99/6.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 43.99/6.02      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(c_181,plain,
% 43.99/6.02      ( r2_hidden(sK1,k1_xboole_0) != iProver_top ),
% 43.99/6.02      inference(instantiation,[status(thm)],[c_179]) ).
% 43.99/6.02  
% 43.99/6.02  cnf(contradiction,plain,
% 43.99/6.02      ( $false ),
% 43.99/6.02      inference(minisat,[status(thm)],[c_100131,c_181]) ).
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 43.99/6.02  
% 43.99/6.02  ------                               Statistics
% 43.99/6.02  
% 43.99/6.02  ------ General
% 43.99/6.02  
% 43.99/6.02  abstr_ref_over_cycles:                  0
% 43.99/6.02  abstr_ref_under_cycles:                 0
% 43.99/6.02  gc_basic_clause_elim:                   0
% 43.99/6.02  forced_gc_time:                         0
% 43.99/6.02  parsing_time:                           0.013
% 43.99/6.02  unif_index_cands_time:                  0.
% 43.99/6.02  unif_index_add_time:                    0.
% 43.99/6.02  orderings_time:                         0.
% 43.99/6.02  out_proof_time:                         0.011
% 43.99/6.02  total_time:                             5.457
% 43.99/6.02  num_of_symbols:                         42
% 43.99/6.02  num_of_terms:                           211322
% 43.99/6.02  
% 43.99/6.02  ------ Preprocessing
% 43.99/6.02  
% 43.99/6.02  num_of_splits:                          0
% 43.99/6.02  num_of_split_atoms:                     0
% 43.99/6.02  num_of_reused_defs:                     0
% 43.99/6.02  num_eq_ax_congr_red:                    12
% 43.99/6.02  num_of_sem_filtered_clauses:            1
% 43.99/6.02  num_of_subtypes:                        0
% 43.99/6.02  monotx_restored_types:                  0
% 43.99/6.02  sat_num_of_epr_types:                   0
% 43.99/6.02  sat_num_of_non_cyclic_types:            0
% 43.99/6.02  sat_guarded_non_collapsed_types:        0
% 43.99/6.02  num_pure_diseq_elim:                    0
% 43.99/6.02  simp_replaced_by:                       0
% 43.99/6.02  res_preprocessed:                       108
% 43.99/6.02  prep_upred:                             0
% 43.99/6.02  prep_unflattend:                        39
% 43.99/6.02  smt_new_axioms:                         0
% 43.99/6.02  pred_elim_cands:                        2
% 43.99/6.02  pred_elim:                              1
% 43.99/6.02  pred_elim_cl:                           1
% 43.99/6.02  pred_elim_cycles:                       3
% 43.99/6.02  merged_defs:                            0
% 43.99/6.02  merged_defs_ncl:                        0
% 43.99/6.02  bin_hyper_res:                          0
% 43.99/6.02  prep_cycles:                            4
% 43.99/6.02  pred_elim_time:                         0.007
% 43.99/6.02  splitting_time:                         0.
% 43.99/6.02  sem_filter_time:                        0.
% 43.99/6.02  monotx_time:                            0.
% 43.99/6.02  subtype_inf_time:                       0.
% 43.99/6.02  
% 43.99/6.02  ------ Problem properties
% 43.99/6.02  
% 43.99/6.02  clauses:                                23
% 43.99/6.02  conjectures:                            1
% 43.99/6.02  epr:                                    4
% 43.99/6.02  horn:                                   21
% 43.99/6.02  ground:                                 1
% 43.99/6.02  unary:                                  17
% 43.99/6.02  binary:                                 0
% 43.99/6.02  lits:                                   38
% 43.99/6.02  lits_eq:                                24
% 43.99/6.02  fd_pure:                                0
% 43.99/6.02  fd_pseudo:                              0
% 43.99/6.02  fd_cond:                                0
% 43.99/6.02  fd_pseudo_cond:                         5
% 43.99/6.02  ac_symbols:                             1
% 43.99/6.02  
% 43.99/6.02  ------ Propositional Solver
% 43.99/6.02  
% 43.99/6.02  prop_solver_calls:                      30
% 43.99/6.02  prop_fast_solver_calls:                 735
% 43.99/6.02  smt_solver_calls:                       0
% 43.99/6.02  smt_fast_solver_calls:                  0
% 43.99/6.02  prop_num_of_clauses:                    10961
% 43.99/6.02  prop_preprocess_simplified:             21810
% 43.99/6.02  prop_fo_subsumed:                       2
% 43.99/6.02  prop_solver_time:                       0.
% 43.99/6.02  smt_solver_time:                        0.
% 43.99/6.02  smt_fast_solver_time:                   0.
% 43.99/6.02  prop_fast_solver_time:                  0.
% 43.99/6.02  prop_unsat_core_time:                   0.001
% 43.99/6.02  
% 43.99/6.02  ------ QBF
% 43.99/6.02  
% 43.99/6.02  qbf_q_res:                              0
% 43.99/6.02  qbf_num_tautologies:                    0
% 43.99/6.02  qbf_prep_cycles:                        0
% 43.99/6.02  
% 43.99/6.02  ------ BMC1
% 43.99/6.02  
% 43.99/6.02  bmc1_current_bound:                     -1
% 43.99/6.02  bmc1_last_solved_bound:                 -1
% 43.99/6.02  bmc1_unsat_core_size:                   -1
% 43.99/6.02  bmc1_unsat_core_parents_size:           -1
% 43.99/6.02  bmc1_merge_next_fun:                    0
% 43.99/6.02  bmc1_unsat_core_clauses_time:           0.
% 43.99/6.02  
% 43.99/6.02  ------ Instantiation
% 43.99/6.02  
% 43.99/6.02  inst_num_of_clauses:                    3101
% 43.99/6.02  inst_num_in_passive:                    923
% 43.99/6.02  inst_num_in_active:                     705
% 43.99/6.02  inst_num_in_unprocessed:                1478
% 43.99/6.02  inst_num_of_loops:                      790
% 43.99/6.02  inst_num_of_learning_restarts:          0
% 43.99/6.02  inst_num_moves_active_passive:          81
% 43.99/6.02  inst_lit_activity:                      0
% 43.99/6.02  inst_lit_activity_moves:                0
% 43.99/6.02  inst_num_tautologies:                   0
% 43.99/6.02  inst_num_prop_implied:                  0
% 43.99/6.02  inst_num_existing_simplified:           0
% 43.99/6.02  inst_num_eq_res_simplified:             0
% 43.99/6.02  inst_num_child_elim:                    0
% 43.99/6.02  inst_num_of_dismatching_blockings:      6283
% 43.99/6.02  inst_num_of_non_proper_insts:           4575
% 43.99/6.02  inst_num_of_duplicates:                 0
% 43.99/6.02  inst_inst_num_from_inst_to_res:         0
% 43.99/6.02  inst_dismatching_checking_time:         0.
% 43.99/6.02  
% 43.99/6.02  ------ Resolution
% 43.99/6.02  
% 43.99/6.02  res_num_of_clauses:                     0
% 43.99/6.02  res_num_in_passive:                     0
% 43.99/6.02  res_num_in_active:                      0
% 43.99/6.02  res_num_of_loops:                       112
% 43.99/6.02  res_forward_subset_subsumed:            837
% 43.99/6.02  res_backward_subset_subsumed:           10
% 43.99/6.02  res_forward_subsumed:                   0
% 43.99/6.02  res_backward_subsumed:                  0
% 43.99/6.02  res_forward_subsumption_resolution:     0
% 43.99/6.02  res_backward_subsumption_resolution:    1
% 43.99/6.02  res_clause_to_clause_subsumption:       322554
% 43.99/6.02  res_orphan_elimination:                 0
% 43.99/6.02  res_tautology_del:                      226
% 43.99/6.02  res_num_eq_res_simplified:              0
% 43.99/6.02  res_num_sel_changes:                    0
% 43.99/6.02  res_moves_from_active_to_pass:          0
% 43.99/6.02  
% 43.99/6.02  ------ Superposition
% 43.99/6.02  
% 43.99/6.02  sup_time_total:                         0.
% 43.99/6.02  sup_time_generating:                    0.
% 43.99/6.02  sup_time_sim_full:                      0.
% 43.99/6.02  sup_time_sim_immed:                     0.
% 43.99/6.02  
% 43.99/6.02  sup_num_of_clauses:                     3343
% 43.99/6.02  sup_num_in_active:                      149
% 43.99/6.02  sup_num_in_passive:                     3194
% 43.99/6.02  sup_num_of_loops:                       156
% 43.99/6.02  sup_fw_superposition:                   26561
% 43.99/6.02  sup_bw_superposition:                   19760
% 43.99/6.02  sup_immediate_simplified:               25683
% 43.99/6.02  sup_given_eliminated:                   3
% 43.99/6.02  comparisons_done:                       0
% 43.99/6.02  comparisons_avoided:                    6
% 43.99/6.02  
% 43.99/6.02  ------ Simplifications
% 43.99/6.02  
% 43.99/6.02  
% 43.99/6.02  sim_fw_subset_subsumed:                 1
% 43.99/6.02  sim_bw_subset_subsumed:                 0
% 43.99/6.02  sim_fw_subsumed:                        428
% 43.99/6.02  sim_bw_subsumed:                        2
% 43.99/6.02  sim_fw_subsumption_res:                 0
% 43.99/6.02  sim_bw_subsumption_res:                 0
% 43.99/6.02  sim_tautology_del:                      0
% 43.99/6.02  sim_eq_tautology_del:                   4222
% 43.99/6.02  sim_eq_res_simp:                        0
% 43.99/6.02  sim_fw_demodulated:                     24708
% 43.99/6.02  sim_bw_demodulated:                     22
% 43.99/6.02  sim_light_normalised:                   5508
% 43.99/6.02  sim_joinable_taut:                      1721
% 43.99/6.02  sim_joinable_simp:                      0
% 43.99/6.02  sim_ac_normalised:                      0
% 43.99/6.02  sim_smt_subsumption:                    0
% 43.99/6.02  
%------------------------------------------------------------------------------
