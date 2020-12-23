%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:17 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  145 (6346 expanded)
%              Number of clauses        :   82 ( 837 expanded)
%              Number of leaves         :   23 (1997 expanded)
%              Depth                    :   34
%              Number of atoms          :  237 (9062 expanded)
%              Number of equality atoms :  208 (8917 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | k1_tarski(sK0) != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_xboole_0 != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_tarski(sK0) != sK1 )
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( k1_xboole_0 != sK2
      | k1_tarski(sK0) != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_xboole_0 != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_tarski(sK0) != sK1 )
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).

fof(f55,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f77,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f55,f64,f65])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f51,f65,f65])).

fof(f58,plain,
    ( k1_xboole_0 != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,
    ( k1_xboole_0 != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f56,plain,
    ( k1_tarski(sK0) != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f56,f65,f65])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f35,f64])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,
    ( k1_tarski(sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f57,f65])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_497,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4114,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_497])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_494,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4322,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4114,c_494])).

cnf(c_15,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4427,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4322,c_15])).

cnf(c_514,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_516,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_704,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_267,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_544,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_605,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_3747,plain,
    ( r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r1_tarski(sK2,sK1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_3749,plain,
    ( r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK2,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3747])).

cnf(c_17,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4425,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4322,c_17])).

cnf(c_0,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_259,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_0,c_5,c_1])).

cnf(c_743,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_18,c_259])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_849,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_11])).

cnf(c_2557,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_743,c_849])).

cnf(c_2744,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2557,c_10])).

cnf(c_846,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_10])).

cnf(c_2338,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_846])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2409,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2338,c_8])).

cnf(c_2746,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2744,c_2409])).

cnf(c_2822,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_2746])).

cnf(c_2833,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_2822,c_8])).

cnf(c_2838,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2833,c_2746])).

cnf(c_3898,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_743,c_2838])).

cnf(c_2340,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_743,c_846])).

cnf(c_956,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_743,c_10])).

cnf(c_1016,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_956])).

cnf(c_1018,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_1016,c_8])).

cnf(c_2344,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1018,c_846])).

cnf(c_845,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_1017,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0),X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_956,c_10])).

cnf(c_1022,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_10,c_1017])).

cnf(c_1031,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_1022,c_956])).

cnf(c_1686,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_845,c_1031])).

cnf(c_1698,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_1686,c_845])).

cnf(c_1079,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_8,c_1031])).

cnf(c_1105,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1079,c_10])).

cnf(c_1108,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,X0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_1105,c_845])).

cnf(c_1080,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,X0)),X1) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_1031])).

cnf(c_1339,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_1080,c_1108])).

cnf(c_1699,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1698,c_1031,c_1108,c_1339])).

cnf(c_1993,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1018,c_1699])).

cnf(c_1996,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(demodulation,[status(thm)],[c_1993,c_1018])).

cnf(c_2455,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_2344,c_1996])).

cnf(c_2460,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(demodulation,[status(thm)],[c_2340,c_2455])).

cnf(c_3918,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_3898,c_2460])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_498,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3980,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3918,c_498])).

cnf(c_4420,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4322,c_3980])).

cnf(c_1081,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_11,c_1031])).

cnf(c_1175,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1081,c_1081,c_1108])).

cnf(c_1179,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_11,c_1175])).

cnf(c_1185,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_1179,c_8,c_1108])).

cnf(c_2621,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1185,c_2409])).

cnf(c_4430,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4420,c_2621])).

cnf(c_4437,plain,
    ( r1_tarski(sK2,sK1)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4430])).

cnf(c_4438,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_15,c_516,c_704,c_3749,c_4322,c_4425,c_4437])).

cnf(c_4453,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_4438,c_18])).

cnf(c_4545,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_4453,c_259])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_708,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_4547,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_4545,c_8,c_708,c_2409])).

cnf(c_16,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4454,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4438,c_16])).

cnf(c_4456,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_4454])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4547,c_4456])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.51/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/1.00  
% 3.51/1.00  ------  iProver source info
% 3.51/1.00  
% 3.51/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.51/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/1.00  git: non_committed_changes: false
% 3.51/1.00  git: last_make_outside_of_git: false
% 3.51/1.00  
% 3.51/1.00  ------ 
% 3.51/1.00  
% 3.51/1.00  ------ Input Options
% 3.51/1.00  
% 3.51/1.00  --out_options                           all
% 3.51/1.00  --tptp_safe_out                         true
% 3.51/1.00  --problem_path                          ""
% 3.51/1.00  --include_path                          ""
% 3.51/1.00  --clausifier                            res/vclausify_rel
% 3.51/1.00  --clausifier_options                    ""
% 3.51/1.00  --stdin                                 false
% 3.51/1.00  --stats_out                             all
% 3.51/1.00  
% 3.51/1.00  ------ General Options
% 3.51/1.00  
% 3.51/1.00  --fof                                   false
% 3.51/1.00  --time_out_real                         305.
% 3.51/1.00  --time_out_virtual                      -1.
% 3.51/1.00  --symbol_type_check                     false
% 3.51/1.00  --clausify_out                          false
% 3.51/1.00  --sig_cnt_out                           false
% 3.51/1.00  --trig_cnt_out                          false
% 3.51/1.00  --trig_cnt_out_tolerance                1.
% 3.51/1.00  --trig_cnt_out_sk_spl                   false
% 3.51/1.00  --abstr_cl_out                          false
% 3.51/1.00  
% 3.51/1.00  ------ Global Options
% 3.51/1.00  
% 3.51/1.00  --schedule                              default
% 3.51/1.00  --add_important_lit                     false
% 3.51/1.00  --prop_solver_per_cl                    1000
% 3.51/1.00  --min_unsat_core                        false
% 3.51/1.00  --soft_assumptions                      false
% 3.51/1.00  --soft_lemma_size                       3
% 3.51/1.00  --prop_impl_unit_size                   0
% 3.51/1.00  --prop_impl_unit                        []
% 3.51/1.00  --share_sel_clauses                     true
% 3.51/1.00  --reset_solvers                         false
% 3.51/1.00  --bc_imp_inh                            [conj_cone]
% 3.51/1.00  --conj_cone_tolerance                   3.
% 3.51/1.00  --extra_neg_conj                        none
% 3.51/1.00  --large_theory_mode                     true
% 3.51/1.00  --prolific_symb_bound                   200
% 3.51/1.00  --lt_threshold                          2000
% 3.51/1.00  --clause_weak_htbl                      true
% 3.51/1.00  --gc_record_bc_elim                     false
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing Options
% 3.51/1.00  
% 3.51/1.00  --preprocessing_flag                    true
% 3.51/1.00  --time_out_prep_mult                    0.1
% 3.51/1.00  --splitting_mode                        input
% 3.51/1.00  --splitting_grd                         true
% 3.51/1.00  --splitting_cvd                         false
% 3.51/1.00  --splitting_cvd_svl                     false
% 3.51/1.00  --splitting_nvd                         32
% 3.51/1.00  --sub_typing                            true
% 3.51/1.00  --prep_gs_sim                           true
% 3.51/1.00  --prep_unflatten                        true
% 3.51/1.00  --prep_res_sim                          true
% 3.51/1.00  --prep_upred                            true
% 3.51/1.00  --prep_sem_filter                       exhaustive
% 3.51/1.00  --prep_sem_filter_out                   false
% 3.51/1.00  --pred_elim                             true
% 3.51/1.00  --res_sim_input                         true
% 3.51/1.00  --eq_ax_congr_red                       true
% 3.51/1.00  --pure_diseq_elim                       true
% 3.51/1.00  --brand_transform                       false
% 3.51/1.00  --non_eq_to_eq                          false
% 3.51/1.00  --prep_def_merge                        true
% 3.51/1.00  --prep_def_merge_prop_impl              false
% 3.51/1.00  --prep_def_merge_mbd                    true
% 3.51/1.00  --prep_def_merge_tr_red                 false
% 3.51/1.00  --prep_def_merge_tr_cl                  false
% 3.51/1.00  --smt_preprocessing                     true
% 3.51/1.00  --smt_ac_axioms                         fast
% 3.51/1.00  --preprocessed_out                      false
% 3.51/1.00  --preprocessed_stats                    false
% 3.51/1.00  
% 3.51/1.00  ------ Abstraction refinement Options
% 3.51/1.00  
% 3.51/1.00  --abstr_ref                             []
% 3.51/1.00  --abstr_ref_prep                        false
% 3.51/1.00  --abstr_ref_until_sat                   false
% 3.51/1.00  --abstr_ref_sig_restrict                funpre
% 3.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/1.00  --abstr_ref_under                       []
% 3.51/1.00  
% 3.51/1.00  ------ SAT Options
% 3.51/1.00  
% 3.51/1.00  --sat_mode                              false
% 3.51/1.00  --sat_fm_restart_options                ""
% 3.51/1.00  --sat_gr_def                            false
% 3.51/1.00  --sat_epr_types                         true
% 3.51/1.00  --sat_non_cyclic_types                  false
% 3.51/1.00  --sat_finite_models                     false
% 3.51/1.00  --sat_fm_lemmas                         false
% 3.51/1.00  --sat_fm_prep                           false
% 3.51/1.00  --sat_fm_uc_incr                        true
% 3.51/1.00  --sat_out_model                         small
% 3.51/1.00  --sat_out_clauses                       false
% 3.51/1.00  
% 3.51/1.00  ------ QBF Options
% 3.51/1.00  
% 3.51/1.00  --qbf_mode                              false
% 3.51/1.00  --qbf_elim_univ                         false
% 3.51/1.00  --qbf_dom_inst                          none
% 3.51/1.00  --qbf_dom_pre_inst                      false
% 3.51/1.00  --qbf_sk_in                             false
% 3.51/1.00  --qbf_pred_elim                         true
% 3.51/1.00  --qbf_split                             512
% 3.51/1.00  
% 3.51/1.00  ------ BMC1 Options
% 3.51/1.00  
% 3.51/1.00  --bmc1_incremental                      false
% 3.51/1.00  --bmc1_axioms                           reachable_all
% 3.51/1.00  --bmc1_min_bound                        0
% 3.51/1.00  --bmc1_max_bound                        -1
% 3.51/1.00  --bmc1_max_bound_default                -1
% 3.51/1.00  --bmc1_symbol_reachability              true
% 3.51/1.00  --bmc1_property_lemmas                  false
% 3.51/1.00  --bmc1_k_induction                      false
% 3.51/1.00  --bmc1_non_equiv_states                 false
% 3.51/1.00  --bmc1_deadlock                         false
% 3.51/1.00  --bmc1_ucm                              false
% 3.51/1.00  --bmc1_add_unsat_core                   none
% 3.51/1.00  --bmc1_unsat_core_children              false
% 3.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/1.00  --bmc1_out_stat                         full
% 3.51/1.00  --bmc1_ground_init                      false
% 3.51/1.00  --bmc1_pre_inst_next_state              false
% 3.51/1.00  --bmc1_pre_inst_state                   false
% 3.51/1.00  --bmc1_pre_inst_reach_state             false
% 3.51/1.00  --bmc1_out_unsat_core                   false
% 3.51/1.00  --bmc1_aig_witness_out                  false
% 3.51/1.00  --bmc1_verbose                          false
% 3.51/1.00  --bmc1_dump_clauses_tptp                false
% 3.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.51/1.00  --bmc1_dump_file                        -
% 3.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.51/1.00  --bmc1_ucm_extend_mode                  1
% 3.51/1.00  --bmc1_ucm_init_mode                    2
% 3.51/1.00  --bmc1_ucm_cone_mode                    none
% 3.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.51/1.00  --bmc1_ucm_relax_model                  4
% 3.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/1.00  --bmc1_ucm_layered_model                none
% 3.51/1.00  --bmc1_ucm_max_lemma_size               10
% 3.51/1.00  
% 3.51/1.00  ------ AIG Options
% 3.51/1.00  
% 3.51/1.00  --aig_mode                              false
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation Options
% 3.51/1.00  
% 3.51/1.00  --instantiation_flag                    true
% 3.51/1.00  --inst_sos_flag                         true
% 3.51/1.00  --inst_sos_phase                        true
% 3.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel_side                     num_symb
% 3.51/1.00  --inst_solver_per_active                1400
% 3.51/1.00  --inst_solver_calls_frac                1.
% 3.51/1.00  --inst_passive_queue_type               priority_queues
% 3.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/1.00  --inst_passive_queues_freq              [25;2]
% 3.51/1.00  --inst_dismatching                      true
% 3.51/1.00  --inst_eager_unprocessed_to_passive     true
% 3.51/1.00  --inst_prop_sim_given                   true
% 3.51/1.00  --inst_prop_sim_new                     false
% 3.51/1.00  --inst_subs_new                         false
% 3.51/1.00  --inst_eq_res_simp                      false
% 3.51/1.00  --inst_subs_given                       false
% 3.51/1.00  --inst_orphan_elimination               true
% 3.51/1.00  --inst_learning_loop_flag               true
% 3.51/1.00  --inst_learning_start                   3000
% 3.51/1.00  --inst_learning_factor                  2
% 3.51/1.00  --inst_start_prop_sim_after_learn       3
% 3.51/1.00  --inst_sel_renew                        solver
% 3.51/1.00  --inst_lit_activity_flag                true
% 3.51/1.00  --inst_restr_to_given                   false
% 3.51/1.00  --inst_activity_threshold               500
% 3.51/1.00  --inst_out_proof                        true
% 3.51/1.00  
% 3.51/1.00  ------ Resolution Options
% 3.51/1.00  
% 3.51/1.00  --resolution_flag                       true
% 3.51/1.00  --res_lit_sel                           adaptive
% 3.51/1.00  --res_lit_sel_side                      none
% 3.51/1.00  --res_ordering                          kbo
% 3.51/1.00  --res_to_prop_solver                    active
% 3.51/1.00  --res_prop_simpl_new                    false
% 3.51/1.00  --res_prop_simpl_given                  true
% 3.51/1.00  --res_passive_queue_type                priority_queues
% 3.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/1.00  --res_passive_queues_freq               [15;5]
% 3.51/1.00  --res_forward_subs                      full
% 3.51/1.00  --res_backward_subs                     full
% 3.51/1.00  --res_forward_subs_resolution           true
% 3.51/1.00  --res_backward_subs_resolution          true
% 3.51/1.00  --res_orphan_elimination                true
% 3.51/1.00  --res_time_limit                        2.
% 3.51/1.00  --res_out_proof                         true
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Options
% 3.51/1.00  
% 3.51/1.00  --superposition_flag                    true
% 3.51/1.00  --sup_passive_queue_type                priority_queues
% 3.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.51/1.00  --demod_completeness_check              fast
% 3.51/1.00  --demod_use_ground                      true
% 3.51/1.00  --sup_to_prop_solver                    passive
% 3.51/1.00  --sup_prop_simpl_new                    true
% 3.51/1.00  --sup_prop_simpl_given                  true
% 3.51/1.00  --sup_fun_splitting                     true
% 3.51/1.00  --sup_smt_interval                      50000
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Simplification Setup
% 3.51/1.00  
% 3.51/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.51/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.51/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.51/1.00  --sup_immed_triv                        [TrivRules]
% 3.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.00  --sup_immed_bw_main                     []
% 3.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.00  --sup_input_bw                          []
% 3.51/1.00  
% 3.51/1.00  ------ Combination Options
% 3.51/1.00  
% 3.51/1.00  --comb_res_mult                         3
% 3.51/1.00  --comb_sup_mult                         2
% 3.51/1.00  --comb_inst_mult                        10
% 3.51/1.00  
% 3.51/1.00  ------ Debug Options
% 3.51/1.00  
% 3.51/1.00  --dbg_backtrace                         false
% 3.51/1.00  --dbg_dump_prop_clauses                 false
% 3.51/1.00  --dbg_dump_prop_clauses_file            -
% 3.51/1.00  --dbg_out_stat                          false
% 3.51/1.00  ------ Parsing...
% 3.51/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/1.00  ------ Proving...
% 3.51/1.00  ------ Problem Properties 
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  clauses                                 19
% 3.51/1.00  conjectures                             4
% 3.51/1.00  EPR                                     0
% 3.51/1.00  Horn                                    18
% 3.51/1.00  unary                                   12
% 3.51/1.00  binary                                  6
% 3.51/1.00  lits                                    27
% 3.51/1.00  lits eq                                 19
% 3.51/1.00  fd_pure                                 0
% 3.51/1.00  fd_pseudo                               0
% 3.51/1.00  fd_cond                                 0
% 3.51/1.00  fd_pseudo_cond                          1
% 3.51/1.00  AC symbols                              1
% 3.51/1.00  
% 3.51/1.00  ------ Schedule dynamic 5 is on 
% 3.51/1.00  
% 3.51/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  ------ 
% 3.51/1.00  Current options:
% 3.51/1.00  ------ 
% 3.51/1.00  
% 3.51/1.00  ------ Input Options
% 3.51/1.00  
% 3.51/1.00  --out_options                           all
% 3.51/1.00  --tptp_safe_out                         true
% 3.51/1.00  --problem_path                          ""
% 3.51/1.00  --include_path                          ""
% 3.51/1.00  --clausifier                            res/vclausify_rel
% 3.51/1.00  --clausifier_options                    ""
% 3.51/1.00  --stdin                                 false
% 3.51/1.00  --stats_out                             all
% 3.51/1.00  
% 3.51/1.00  ------ General Options
% 3.51/1.00  
% 3.51/1.00  --fof                                   false
% 3.51/1.00  --time_out_real                         305.
% 3.51/1.00  --time_out_virtual                      -1.
% 3.51/1.00  --symbol_type_check                     false
% 3.51/1.00  --clausify_out                          false
% 3.51/1.00  --sig_cnt_out                           false
% 3.51/1.00  --trig_cnt_out                          false
% 3.51/1.00  --trig_cnt_out_tolerance                1.
% 3.51/1.00  --trig_cnt_out_sk_spl                   false
% 3.51/1.00  --abstr_cl_out                          false
% 3.51/1.00  
% 3.51/1.00  ------ Global Options
% 3.51/1.00  
% 3.51/1.00  --schedule                              default
% 3.51/1.00  --add_important_lit                     false
% 3.51/1.00  --prop_solver_per_cl                    1000
% 3.51/1.00  --min_unsat_core                        false
% 3.51/1.00  --soft_assumptions                      false
% 3.51/1.00  --soft_lemma_size                       3
% 3.51/1.00  --prop_impl_unit_size                   0
% 3.51/1.00  --prop_impl_unit                        []
% 3.51/1.00  --share_sel_clauses                     true
% 3.51/1.00  --reset_solvers                         false
% 3.51/1.00  --bc_imp_inh                            [conj_cone]
% 3.51/1.00  --conj_cone_tolerance                   3.
% 3.51/1.00  --extra_neg_conj                        none
% 3.51/1.00  --large_theory_mode                     true
% 3.51/1.00  --prolific_symb_bound                   200
% 3.51/1.00  --lt_threshold                          2000
% 3.51/1.00  --clause_weak_htbl                      true
% 3.51/1.00  --gc_record_bc_elim                     false
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing Options
% 3.51/1.00  
% 3.51/1.00  --preprocessing_flag                    true
% 3.51/1.00  --time_out_prep_mult                    0.1
% 3.51/1.00  --splitting_mode                        input
% 3.51/1.00  --splitting_grd                         true
% 3.51/1.00  --splitting_cvd                         false
% 3.51/1.00  --splitting_cvd_svl                     false
% 3.51/1.00  --splitting_nvd                         32
% 3.51/1.00  --sub_typing                            true
% 3.51/1.00  --prep_gs_sim                           true
% 3.51/1.00  --prep_unflatten                        true
% 3.51/1.00  --prep_res_sim                          true
% 3.51/1.00  --prep_upred                            true
% 3.51/1.00  --prep_sem_filter                       exhaustive
% 3.51/1.00  --prep_sem_filter_out                   false
% 3.51/1.00  --pred_elim                             true
% 3.51/1.00  --res_sim_input                         true
% 3.51/1.00  --eq_ax_congr_red                       true
% 3.51/1.00  --pure_diseq_elim                       true
% 3.51/1.00  --brand_transform                       false
% 3.51/1.00  --non_eq_to_eq                          false
% 3.51/1.00  --prep_def_merge                        true
% 3.51/1.00  --prep_def_merge_prop_impl              false
% 3.51/1.00  --prep_def_merge_mbd                    true
% 3.51/1.00  --prep_def_merge_tr_red                 false
% 3.51/1.00  --prep_def_merge_tr_cl                  false
% 3.51/1.00  --smt_preprocessing                     true
% 3.51/1.00  --smt_ac_axioms                         fast
% 3.51/1.00  --preprocessed_out                      false
% 3.51/1.00  --preprocessed_stats                    false
% 3.51/1.00  
% 3.51/1.00  ------ Abstraction refinement Options
% 3.51/1.00  
% 3.51/1.00  --abstr_ref                             []
% 3.51/1.00  --abstr_ref_prep                        false
% 3.51/1.00  --abstr_ref_until_sat                   false
% 3.51/1.00  --abstr_ref_sig_restrict                funpre
% 3.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/1.00  --abstr_ref_under                       []
% 3.51/1.00  
% 3.51/1.00  ------ SAT Options
% 3.51/1.00  
% 3.51/1.00  --sat_mode                              false
% 3.51/1.00  --sat_fm_restart_options                ""
% 3.51/1.00  --sat_gr_def                            false
% 3.51/1.00  --sat_epr_types                         true
% 3.51/1.00  --sat_non_cyclic_types                  false
% 3.51/1.00  --sat_finite_models                     false
% 3.51/1.01  --sat_fm_lemmas                         false
% 3.51/1.01  --sat_fm_prep                           false
% 3.51/1.01  --sat_fm_uc_incr                        true
% 3.51/1.01  --sat_out_model                         small
% 3.51/1.01  --sat_out_clauses                       false
% 3.51/1.01  
% 3.51/1.01  ------ QBF Options
% 3.51/1.01  
% 3.51/1.01  --qbf_mode                              false
% 3.51/1.01  --qbf_elim_univ                         false
% 3.51/1.01  --qbf_dom_inst                          none
% 3.51/1.01  --qbf_dom_pre_inst                      false
% 3.51/1.01  --qbf_sk_in                             false
% 3.51/1.01  --qbf_pred_elim                         true
% 3.51/1.01  --qbf_split                             512
% 3.51/1.01  
% 3.51/1.01  ------ BMC1 Options
% 3.51/1.01  
% 3.51/1.01  --bmc1_incremental                      false
% 3.51/1.01  --bmc1_axioms                           reachable_all
% 3.51/1.01  --bmc1_min_bound                        0
% 3.51/1.01  --bmc1_max_bound                        -1
% 3.51/1.01  --bmc1_max_bound_default                -1
% 3.51/1.01  --bmc1_symbol_reachability              true
% 3.51/1.01  --bmc1_property_lemmas                  false
% 3.51/1.01  --bmc1_k_induction                      false
% 3.51/1.01  --bmc1_non_equiv_states                 false
% 3.51/1.01  --bmc1_deadlock                         false
% 3.51/1.01  --bmc1_ucm                              false
% 3.51/1.01  --bmc1_add_unsat_core                   none
% 3.51/1.01  --bmc1_unsat_core_children              false
% 3.51/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/1.01  --bmc1_out_stat                         full
% 3.51/1.01  --bmc1_ground_init                      false
% 3.51/1.01  --bmc1_pre_inst_next_state              false
% 3.51/1.01  --bmc1_pre_inst_state                   false
% 3.51/1.01  --bmc1_pre_inst_reach_state             false
% 3.51/1.01  --bmc1_out_unsat_core                   false
% 3.51/1.01  --bmc1_aig_witness_out                  false
% 3.51/1.01  --bmc1_verbose                          false
% 3.51/1.01  --bmc1_dump_clauses_tptp                false
% 3.51/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.51/1.01  --bmc1_dump_file                        -
% 3.51/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.51/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.51/1.01  --bmc1_ucm_extend_mode                  1
% 3.51/1.01  --bmc1_ucm_init_mode                    2
% 3.51/1.01  --bmc1_ucm_cone_mode                    none
% 3.51/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.51/1.01  --bmc1_ucm_relax_model                  4
% 3.51/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.51/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/1.01  --bmc1_ucm_layered_model                none
% 3.51/1.01  --bmc1_ucm_max_lemma_size               10
% 3.51/1.01  
% 3.51/1.01  ------ AIG Options
% 3.51/1.01  
% 3.51/1.01  --aig_mode                              false
% 3.51/1.01  
% 3.51/1.01  ------ Instantiation Options
% 3.51/1.01  
% 3.51/1.01  --instantiation_flag                    true
% 3.51/1.01  --inst_sos_flag                         true
% 3.51/1.01  --inst_sos_phase                        true
% 3.51/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/1.01  --inst_lit_sel_side                     none
% 3.51/1.01  --inst_solver_per_active                1400
% 3.51/1.01  --inst_solver_calls_frac                1.
% 3.51/1.01  --inst_passive_queue_type               priority_queues
% 3.51/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/1.01  --inst_passive_queues_freq              [25;2]
% 3.51/1.01  --inst_dismatching                      true
% 3.51/1.01  --inst_eager_unprocessed_to_passive     true
% 3.51/1.01  --inst_prop_sim_given                   true
% 3.51/1.01  --inst_prop_sim_new                     false
% 3.51/1.01  --inst_subs_new                         false
% 3.51/1.01  --inst_eq_res_simp                      false
% 3.51/1.01  --inst_subs_given                       false
% 3.51/1.01  --inst_orphan_elimination               true
% 3.51/1.01  --inst_learning_loop_flag               true
% 3.51/1.01  --inst_learning_start                   3000
% 3.51/1.01  --inst_learning_factor                  2
% 3.51/1.01  --inst_start_prop_sim_after_learn       3
% 3.51/1.01  --inst_sel_renew                        solver
% 3.51/1.01  --inst_lit_activity_flag                true
% 3.51/1.01  --inst_restr_to_given                   false
% 3.51/1.01  --inst_activity_threshold               500
% 3.51/1.01  --inst_out_proof                        true
% 3.51/1.01  
% 3.51/1.01  ------ Resolution Options
% 3.51/1.01  
% 3.51/1.01  --resolution_flag                       false
% 3.51/1.01  --res_lit_sel                           adaptive
% 3.51/1.01  --res_lit_sel_side                      none
% 3.51/1.01  --res_ordering                          kbo
% 3.51/1.01  --res_to_prop_solver                    active
% 3.51/1.01  --res_prop_simpl_new                    false
% 3.51/1.01  --res_prop_simpl_given                  true
% 3.51/1.01  --res_passive_queue_type                priority_queues
% 3.51/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/1.01  --res_passive_queues_freq               [15;5]
% 3.51/1.01  --res_forward_subs                      full
% 3.51/1.01  --res_backward_subs                     full
% 3.51/1.01  --res_forward_subs_resolution           true
% 3.51/1.01  --res_backward_subs_resolution          true
% 3.51/1.01  --res_orphan_elimination                true
% 3.51/1.01  --res_time_limit                        2.
% 3.51/1.01  --res_out_proof                         true
% 3.51/1.01  
% 3.51/1.01  ------ Superposition Options
% 3.51/1.01  
% 3.51/1.01  --superposition_flag                    true
% 3.51/1.01  --sup_passive_queue_type                priority_queues
% 3.51/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.51/1.01  --demod_completeness_check              fast
% 3.51/1.01  --demod_use_ground                      true
% 3.51/1.01  --sup_to_prop_solver                    passive
% 3.51/1.01  --sup_prop_simpl_new                    true
% 3.51/1.01  --sup_prop_simpl_given                  true
% 3.51/1.01  --sup_fun_splitting                     true
% 3.51/1.01  --sup_smt_interval                      50000
% 3.51/1.01  
% 3.51/1.01  ------ Superposition Simplification Setup
% 3.51/1.01  
% 3.51/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.51/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.51/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.51/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.51/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.51/1.01  --sup_immed_triv                        [TrivRules]
% 3.51/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.01  --sup_immed_bw_main                     []
% 3.51/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.51/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.01  --sup_input_bw                          []
% 3.51/1.01  
% 3.51/1.01  ------ Combination Options
% 3.51/1.01  
% 3.51/1.01  --comb_res_mult                         3
% 3.51/1.01  --comb_sup_mult                         2
% 3.51/1.01  --comb_inst_mult                        10
% 3.51/1.01  
% 3.51/1.01  ------ Debug Options
% 3.51/1.01  
% 3.51/1.01  --dbg_backtrace                         false
% 3.51/1.01  --dbg_dump_prop_clauses                 false
% 3.51/1.01  --dbg_dump_prop_clauses_file            -
% 3.51/1.01  --dbg_out_stat                          false
% 3.51/1.01  
% 3.51/1.01  
% 3.51/1.01  
% 3.51/1.01  
% 3.51/1.01  ------ Proving...
% 3.51/1.01  
% 3.51/1.01  
% 3.51/1.01  % SZS status Theorem for theBenchmark.p
% 3.51/1.01  
% 3.51/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/1.01  
% 3.51/1.01  fof(f22,conjecture,(
% 3.51/1.01    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f23,negated_conjecture,(
% 3.51/1.01    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.51/1.01    inference(negated_conjecture,[],[f22])).
% 3.51/1.01  
% 3.51/1.01  fof(f25,plain,(
% 3.51/1.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.51/1.01    inference(ennf_transformation,[],[f23])).
% 3.51/1.01  
% 3.51/1.01  fof(f29,plain,(
% 3.51/1.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 3.51/1.01    introduced(choice_axiom,[])).
% 3.51/1.01  
% 3.51/1.01  fof(f30,plain,(
% 3.51/1.01    (k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.51/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).
% 3.51/1.01  
% 3.51/1.01  fof(f55,plain,(
% 3.51/1.01    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.51/1.01    inference(cnf_transformation,[],[f30])).
% 3.51/1.01  
% 3.51/1.01  fof(f21,axiom,(
% 3.51/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f54,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.51/1.01    inference(cnf_transformation,[],[f21])).
% 3.51/1.01  
% 3.51/1.01  fof(f64,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.51/1.01    inference(definition_unfolding,[],[f54,f63])).
% 3.51/1.01  
% 3.51/1.01  fof(f13,axiom,(
% 3.51/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f44,plain,(
% 3.51/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f13])).
% 3.51/1.01  
% 3.51/1.01  fof(f14,axiom,(
% 3.51/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f45,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f14])).
% 3.51/1.01  
% 3.51/1.01  fof(f15,axiom,(
% 3.51/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f46,plain,(
% 3.51/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f15])).
% 3.51/1.01  
% 3.51/1.01  fof(f16,axiom,(
% 3.51/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f47,plain,(
% 3.51/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f16])).
% 3.51/1.01  
% 3.51/1.01  fof(f17,axiom,(
% 3.51/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f48,plain,(
% 3.51/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f17])).
% 3.51/1.01  
% 3.51/1.01  fof(f18,axiom,(
% 3.51/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f49,plain,(
% 3.51/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f18])).
% 3.51/1.01  
% 3.51/1.01  fof(f19,axiom,(
% 3.51/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f50,plain,(
% 3.51/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f19])).
% 3.51/1.01  
% 3.51/1.01  fof(f59,plain,(
% 3.51/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.51/1.01    inference(definition_unfolding,[],[f49,f50])).
% 3.51/1.01  
% 3.51/1.01  fof(f60,plain,(
% 3.51/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.51/1.01    inference(definition_unfolding,[],[f48,f59])).
% 3.51/1.01  
% 3.51/1.01  fof(f61,plain,(
% 3.51/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.51/1.01    inference(definition_unfolding,[],[f47,f60])).
% 3.51/1.01  
% 3.51/1.01  fof(f62,plain,(
% 3.51/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.51/1.01    inference(definition_unfolding,[],[f46,f61])).
% 3.51/1.01  
% 3.51/1.01  fof(f63,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.51/1.01    inference(definition_unfolding,[],[f45,f62])).
% 3.51/1.01  
% 3.51/1.01  fof(f65,plain,(
% 3.51/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.51/1.01    inference(definition_unfolding,[],[f44,f63])).
% 3.51/1.01  
% 3.51/1.01  fof(f77,plain,(
% 3.51/1.01    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 3.51/1.01    inference(definition_unfolding,[],[f55,f64,f65])).
% 3.51/1.01  
% 3.51/1.01  fof(f10,axiom,(
% 3.51/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f41,plain,(
% 3.51/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.51/1.01    inference(cnf_transformation,[],[f10])).
% 3.51/1.01  
% 3.51/1.01  fof(f70,plain,(
% 3.51/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.51/1.01    inference(definition_unfolding,[],[f41,f64])).
% 3.51/1.01  
% 3.51/1.01  fof(f20,axiom,(
% 3.51/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f27,plain,(
% 3.51/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.51/1.01    inference(nnf_transformation,[],[f20])).
% 3.51/1.01  
% 3.51/1.01  fof(f28,plain,(
% 3.51/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.51/1.01    inference(flattening,[],[f27])).
% 3.51/1.01  
% 3.51/1.01  fof(f51,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.51/1.01    inference(cnf_transformation,[],[f28])).
% 3.51/1.01  
% 3.51/1.01  fof(f73,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.51/1.01    inference(definition_unfolding,[],[f51,f65,f65])).
% 3.51/1.01  
% 3.51/1.01  fof(f58,plain,(
% 3.51/1.01    k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1),
% 3.51/1.01    inference(cnf_transformation,[],[f30])).
% 3.51/1.01  
% 3.51/1.01  fof(f74,plain,(
% 3.51/1.01    k1_xboole_0 != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.51/1.01    inference(definition_unfolding,[],[f58,f65])).
% 3.51/1.01  
% 3.51/1.01  fof(f56,plain,(
% 3.51/1.01    k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1),
% 3.51/1.01    inference(cnf_transformation,[],[f30])).
% 3.51/1.01  
% 3.51/1.01  fof(f76,plain,(
% 3.51/1.01    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.51/1.01    inference(definition_unfolding,[],[f56,f65,f65])).
% 3.51/1.01  
% 3.51/1.01  fof(f3,axiom,(
% 3.51/1.01    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f34,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f3])).
% 3.51/1.01  
% 3.51/1.01  fof(f4,axiom,(
% 3.51/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f35,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.51/1.01    inference(cnf_transformation,[],[f4])).
% 3.51/1.01  
% 3.51/1.01  fof(f66,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))) )),
% 3.51/1.01    inference(definition_unfolding,[],[f34,f35,f64])).
% 3.51/1.01  
% 3.51/1.01  fof(f6,axiom,(
% 3.51/1.01    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f37,plain,(
% 3.51/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f6])).
% 3.51/1.01  
% 3.51/1.01  fof(f1,axiom,(
% 3.51/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f31,plain,(
% 3.51/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f1])).
% 3.51/1.01  
% 3.51/1.01  fof(f12,axiom,(
% 3.51/1.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f43,plain,(
% 3.51/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f12])).
% 3.51/1.01  
% 3.51/1.01  fof(f11,axiom,(
% 3.51/1.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f42,plain,(
% 3.51/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f11])).
% 3.51/1.01  
% 3.51/1.01  fof(f9,axiom,(
% 3.51/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f40,plain,(
% 3.51/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.51/1.01    inference(cnf_transformation,[],[f9])).
% 3.51/1.01  
% 3.51/1.01  fof(f7,axiom,(
% 3.51/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f38,plain,(
% 3.51/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.51/1.01    inference(cnf_transformation,[],[f7])).
% 3.51/1.01  
% 3.51/1.01  fof(f8,axiom,(
% 3.51/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.51/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/1.01  
% 3.51/1.01  fof(f39,plain,(
% 3.51/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.51/1.01    inference(cnf_transformation,[],[f8])).
% 3.51/1.01  
% 3.51/1.01  fof(f57,plain,(
% 3.51/1.01    k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1),
% 3.51/1.01    inference(cnf_transformation,[],[f30])).
% 3.51/1.01  
% 3.51/1.01  fof(f75,plain,(
% 3.51/1.01    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k1_xboole_0 != sK1),
% 3.51/1.01    inference(definition_unfolding,[],[f57,f65])).
% 3.51/1.01  
% 3.51/1.01  cnf(c_18,negated_conjecture,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.51/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_9,plain,
% 3.51/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.51/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_497,plain,
% 3.51/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.51/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4114,plain,
% 3.51/1.01      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_18,c_497]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_14,plain,
% 3.51/1.01      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.51/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.51/1.01      | k1_xboole_0 = X0 ),
% 3.51/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_494,plain,
% 3.51/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.51/1.01      | k1_xboole_0 = X1
% 3.51/1.01      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.51/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4322,plain,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 3.51/1.01      | sK1 = k1_xboole_0 ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_4114,c_494]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_15,negated_conjecture,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.51/1.01      | k1_xboole_0 != sK2 ),
% 3.51/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4427,plain,
% 3.51/1.01      ( sK1 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_4322,c_15]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_514,plain,
% 3.51/1.01      ( ~ r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.51/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK2
% 3.51/1.01      | k1_xboole_0 = sK2 ),
% 3.51/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_516,plain,
% 3.51/1.01      ( ~ r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.51/1.01      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
% 3.51/1.01      | k1_xboole_0 = sK2 ),
% 3.51/1.01      inference(instantiation,[status(thm)],[c_514]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_261,plain,( X0 = X0 ),theory(equality) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_704,plain,
% 3.51/1.01      ( sK2 = sK2 ),
% 3.51/1.01      inference(instantiation,[status(thm)],[c_261]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_267,plain,
% 3.51/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.51/1.01      theory(equality) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_544,plain,
% 3.51/1.01      ( ~ r1_tarski(X0,X1)
% 3.51/1.01      | r1_tarski(sK2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 3.51/1.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 3.51/1.01      | sK2 != X0 ),
% 3.51/1.01      inference(instantiation,[status(thm)],[c_267]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_605,plain,
% 3.51/1.01      ( ~ r1_tarski(sK2,X0)
% 3.51/1.01      | r1_tarski(sK2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.51/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
% 3.51/1.01      | sK2 != sK2 ),
% 3.51/1.01      inference(instantiation,[status(thm)],[c_544]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_3747,plain,
% 3.51/1.01      ( r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.51/1.01      | ~ r1_tarski(sK2,sK1)
% 3.51/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != sK1
% 3.51/1.01      | sK2 != sK2 ),
% 3.51/1.01      inference(instantiation,[status(thm)],[c_605]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_3749,plain,
% 3.51/1.01      ( r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.51/1.01      | ~ r1_tarski(sK2,sK1)
% 3.51/1.01      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.51/1.01      | sK2 != sK2 ),
% 3.51/1.01      inference(instantiation,[status(thm)],[c_3747]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_17,negated_conjecture,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.51/1.01      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.51/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4425,plain,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.51/1.01      | sK1 = k1_xboole_0 ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_4322,c_17]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_0,plain,
% 3.51/1.01      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 3.51/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_5,plain,
% 3.51/1.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.51/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1,plain,
% 3.51/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.51/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_259,plain,
% 3.51/1.01      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(X0,X1) ),
% 3.51/1.01      inference(theory_normalisation,[status(thm)],[c_0,c_5,c_1]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_743,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,sK2) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_18,c_259]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_11,plain,
% 3.51/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.51/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_10,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.51/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_849,plain,
% 3.51/1.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_10,c_11]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2557,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_743,c_849]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2744,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_2557,c_10]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_846,plain,
% 3.51/1.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_11,c_10]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2338,plain,
% 3.51/1.01      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_11,c_846]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_8,plain,
% 3.51/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.51/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2409,plain,
% 3.51/1.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.51/1.01      inference(light_normalisation,[status(thm)],[c_2338,c_8]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2746,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)),X0)) = X0 ),
% 3.51/1.01      inference(light_normalisation,[status(thm)],[c_2744,c_2409]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2822,plain,
% 3.51/1.01      ( k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_11,c_2746]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2833,plain,
% 3.51/1.01      ( k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_2822,c_8]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2838,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = X0 ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_2833,c_2746]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_3898,plain,
% 3.51/1.01      ( k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK2)) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_743,c_2838]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2340,plain,
% 3.51/1.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK2)) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_743,c_846]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_956,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_743,c_10]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1016,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_11,c_956]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1018,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1016,c_8]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2344,plain,
% 3.51/1.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_1018,c_846]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_845,plain,
% 3.51/1.01      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1017,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0),X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_956,c_10]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1022,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_10,c_1017]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1031,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1022,c_956]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1686,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_845,c_1031]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1698,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),X0),X1) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1686,c_845]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1079,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_8,c_1031]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1105,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_1079,c_10]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1108,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,X0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),X0) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1105,c_845]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1080,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,X0)),X1) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_10,c_1031]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1339,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,X0)),X1) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1080,c_1108]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1699,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 3.51/1.01      inference(light_normalisation,
% 3.51/1.01                [status(thm)],
% 3.51/1.01                [c_1698,c_1031,c_1108,c_1339]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1993,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_1018,c_1699]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1996,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1993,c_1018]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2455,plain,
% 3.51/1.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 3.51/1.01      inference(light_normalisation,[status(thm)],[c_2344,c_1996]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2460,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_2340,c_2455]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_3918,plain,
% 3.51/1.01      ( k3_xboole_0(sK1,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 3.51/1.01      inference(light_normalisation,[status(thm)],[c_3898,c_2460]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_6,plain,
% 3.51/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.51/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_498,plain,
% 3.51/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.51/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_3980,plain,
% 3.51/1.01      ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_3918,c_498]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4420,plain,
% 3.51/1.01      ( sK1 = k1_xboole_0
% 3.51/1.01      | r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) = iProver_top ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_4322,c_3980]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1081,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_11,c_1031]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1175,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.51/1.01      inference(light_normalisation,[status(thm)],[c_1081,c_1081,c_1108]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1179,plain,
% 3.51/1.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,sK2) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_11,c_1175]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_1185,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(k1_xboole_0,sK2) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1179,c_8,c_1108]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_2621,plain,
% 3.51/1.01      ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = sK2 ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_1185,c_2409]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4430,plain,
% 3.51/1.01      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK1) = iProver_top ),
% 3.51/1.01      inference(light_normalisation,[status(thm)],[c_4420,c_2621]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4437,plain,
% 3.51/1.01      ( r1_tarski(sK2,sK1) | sK1 = k1_xboole_0 ),
% 3.51/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4430]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4438,plain,
% 3.51/1.01      ( sK1 = k1_xboole_0 ),
% 3.51/1.01      inference(global_propositional_subsumption,
% 3.51/1.01                [status(thm)],
% 3.51/1.01                [c_4427,c_15,c_516,c_704,c_3749,c_4322,c_4425,c_4437]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4453,plain,
% 3.51/1.01      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_4438,c_18]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4545,plain,
% 3.51/1.01      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k1_xboole_0,sK2) ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_4453,c_259]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_7,plain,
% 3.51/1.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.51/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_708,plain,
% 3.51/1.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.51/1.01      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4547,plain,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_4545,c_8,c_708,c_2409]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_16,negated_conjecture,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.51/1.01      | k1_xboole_0 != sK1 ),
% 3.51/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4454,plain,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.51/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.51/1.01      inference(demodulation,[status(thm)],[c_4438,c_16]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(c_4456,plain,
% 3.51/1.01      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.51/1.01      inference(equality_resolution_simp,[status(thm)],[c_4454]) ).
% 3.51/1.01  
% 3.51/1.01  cnf(contradiction,plain,
% 3.51/1.01      ( $false ),
% 3.51/1.01      inference(minisat,[status(thm)],[c_4547,c_4456]) ).
% 3.51/1.01  
% 3.51/1.01  
% 3.51/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/1.01  
% 3.51/1.01  ------                               Statistics
% 3.51/1.01  
% 3.51/1.01  ------ General
% 3.51/1.01  
% 3.51/1.01  abstr_ref_over_cycles:                  0
% 3.51/1.01  abstr_ref_under_cycles:                 0
% 3.51/1.01  gc_basic_clause_elim:                   0
% 3.51/1.01  forced_gc_time:                         0
% 3.51/1.01  parsing_time:                           0.008
% 3.51/1.01  unif_index_cands_time:                  0.
% 3.51/1.01  unif_index_add_time:                    0.
% 3.51/1.01  orderings_time:                         0.
% 3.51/1.01  out_proof_time:                         0.012
% 3.51/1.01  total_time:                             0.203
% 3.51/1.01  num_of_symbols:                         40
% 3.51/1.01  num_of_terms:                           7204
% 3.51/1.01  
% 3.51/1.01  ------ Preprocessing
% 3.51/1.01  
% 3.51/1.01  num_of_splits:                          0
% 3.51/1.01  num_of_split_atoms:                     0
% 3.51/1.01  num_of_reused_defs:                     0
% 3.51/1.01  num_eq_ax_congr_red:                    0
% 3.51/1.01  num_of_sem_filtered_clauses:            1
% 3.51/1.01  num_of_subtypes:                        0
% 3.51/1.01  monotx_restored_types:                  0
% 3.51/1.01  sat_num_of_epr_types:                   0
% 3.51/1.01  sat_num_of_non_cyclic_types:            0
% 3.51/1.01  sat_guarded_non_collapsed_types:        0
% 3.51/1.01  num_pure_diseq_elim:                    0
% 3.51/1.01  simp_replaced_by:                       0
% 3.51/1.01  res_preprocessed:                       72
% 3.51/1.01  prep_upred:                             0
% 3.51/1.01  prep_unflattend:                        23
% 3.51/1.01  smt_new_axioms:                         0
% 3.51/1.01  pred_elim_cands:                        1
% 3.51/1.01  pred_elim:                              0
% 3.51/1.01  pred_elim_cl:                           0
% 3.51/1.01  pred_elim_cycles:                       1
% 3.51/1.01  merged_defs:                            6
% 3.51/1.01  merged_defs_ncl:                        0
% 3.51/1.01  bin_hyper_res:                          6
% 3.51/1.01  prep_cycles:                            3
% 3.51/1.01  pred_elim_time:                         0.002
% 3.51/1.01  splitting_time:                         0.
% 3.51/1.01  sem_filter_time:                        0.
% 3.51/1.01  monotx_time:                            0.
% 3.51/1.01  subtype_inf_time:                       0.
% 3.51/1.01  
% 3.51/1.01  ------ Problem properties
% 3.51/1.01  
% 3.51/1.01  clauses:                                19
% 3.51/1.01  conjectures:                            4
% 3.51/1.01  epr:                                    0
% 3.51/1.01  horn:                                   18
% 3.51/1.01  ground:                                 4
% 3.51/1.01  unary:                                  12
% 3.51/1.01  binary:                                 6
% 3.51/1.01  lits:                                   27
% 3.51/1.01  lits_eq:                                19
% 3.51/1.01  fd_pure:                                0
% 3.51/1.01  fd_pseudo:                              0
% 3.51/1.01  fd_cond:                                0
% 3.51/1.01  fd_pseudo_cond:                         1
% 3.51/1.01  ac_symbols:                             1
% 3.51/1.01  
% 3.51/1.01  ------ Propositional Solver
% 3.51/1.01  
% 3.51/1.01  prop_solver_calls:                      26
% 3.51/1.01  prop_fast_solver_calls:                 370
% 3.51/1.01  smt_solver_calls:                       0
% 3.51/1.01  smt_fast_solver_calls:                  0
% 3.51/1.01  prop_num_of_clauses:                    1908
% 3.51/1.01  prop_preprocess_simplified:             4467
% 3.51/1.01  prop_fo_subsumed:                       1
% 3.51/1.01  prop_solver_time:                       0.
% 3.51/1.01  smt_solver_time:                        0.
% 3.51/1.01  smt_fast_solver_time:                   0.
% 3.51/1.01  prop_fast_solver_time:                  0.
% 3.51/1.01  prop_unsat_core_time:                   0.
% 3.51/1.01  
% 3.51/1.01  ------ QBF
% 3.51/1.01  
% 3.51/1.01  qbf_q_res:                              0
% 3.51/1.01  qbf_num_tautologies:                    0
% 3.51/1.01  qbf_prep_cycles:                        0
% 3.51/1.01  
% 3.51/1.01  ------ BMC1
% 3.51/1.01  
% 3.51/1.01  bmc1_current_bound:                     -1
% 3.51/1.01  bmc1_last_solved_bound:                 -1
% 3.51/1.01  bmc1_unsat_core_size:                   -1
% 3.51/1.01  bmc1_unsat_core_parents_size:           -1
% 3.51/1.01  bmc1_merge_next_fun:                    0
% 3.51/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.51/1.01  
% 3.51/1.01  ------ Instantiation
% 3.51/1.01  
% 3.51/1.01  inst_num_of_clauses:                    595
% 3.51/1.01  inst_num_in_passive:                    215
% 3.51/1.01  inst_num_in_active:                     255
% 3.51/1.01  inst_num_in_unprocessed:                125
% 3.51/1.01  inst_num_of_loops:                      300
% 3.51/1.01  inst_num_of_learning_restarts:          0
% 3.51/1.01  inst_num_moves_active_passive:          41
% 3.51/1.01  inst_lit_activity:                      0
% 3.51/1.01  inst_lit_activity_moves:                0
% 3.51/1.01  inst_num_tautologies:                   0
% 3.51/1.01  inst_num_prop_implied:                  0
% 3.51/1.01  inst_num_existing_simplified:           0
% 3.51/1.01  inst_num_eq_res_simplified:             0
% 3.51/1.01  inst_num_child_elim:                    0
% 3.51/1.01  inst_num_of_dismatching_blockings:      245
% 3.51/1.01  inst_num_of_non_proper_insts:           623
% 3.51/1.01  inst_num_of_duplicates:                 0
% 3.51/1.01  inst_inst_num_from_inst_to_res:         0
% 3.51/1.01  inst_dismatching_checking_time:         0.
% 3.51/1.01  
% 3.51/1.01  ------ Resolution
% 3.51/1.01  
% 3.51/1.01  res_num_of_clauses:                     0
% 3.51/1.01  res_num_in_passive:                     0
% 3.51/1.01  res_num_in_active:                      0
% 3.51/1.01  res_num_of_loops:                       75
% 3.51/1.01  res_forward_subset_subsumed:            78
% 3.51/1.01  res_backward_subset_subsumed:           0
% 3.51/1.01  res_forward_subsumed:                   0
% 3.51/1.01  res_backward_subsumed:                  0
% 3.51/1.01  res_forward_subsumption_resolution:     0
% 3.51/1.01  res_backward_subsumption_resolution:    0
% 3.51/1.01  res_clause_to_clause_subsumption:       935
% 3.51/1.01  res_orphan_elimination:                 0
% 3.51/1.01  res_tautology_del:                      93
% 3.51/1.01  res_num_eq_res_simplified:              0
% 3.51/1.01  res_num_sel_changes:                    0
% 3.51/1.01  res_moves_from_active_to_pass:          0
% 3.51/1.01  
% 3.51/1.01  ------ Superposition
% 3.51/1.01  
% 3.51/1.01  sup_time_total:                         0.
% 3.51/1.01  sup_time_generating:                    0.
% 3.51/1.01  sup_time_sim_full:                      0.
% 3.51/1.01  sup_time_sim_immed:                     0.
% 3.51/1.01  
% 3.51/1.01  sup_num_of_clauses:                     172
% 3.51/1.01  sup_num_in_active:                      23
% 3.51/1.01  sup_num_in_passive:                     149
% 3.51/1.01  sup_num_of_loops:                       59
% 3.51/1.01  sup_fw_superposition:                   274
% 3.51/1.01  sup_bw_superposition:                   243
% 3.51/1.01  sup_immediate_simplified:               336
% 3.51/1.01  sup_given_eliminated:                   8
% 3.51/1.01  comparisons_done:                       0
% 3.51/1.01  comparisons_avoided:                    0
% 3.51/1.01  
% 3.51/1.01  ------ Simplifications
% 3.51/1.01  
% 3.51/1.01  
% 3.51/1.01  sim_fw_subset_subsumed:                 1
% 3.51/1.01  sim_bw_subset_subsumed:                 4
% 3.51/1.01  sim_fw_subsumed:                        66
% 3.51/1.01  sim_bw_subsumed:                        4
% 3.51/1.01  sim_fw_subsumption_res:                 0
% 3.51/1.01  sim_bw_subsumption_res:                 0
% 3.51/1.01  sim_tautology_del:                      1
% 3.51/1.01  sim_eq_tautology_del:                   116
% 3.51/1.01  sim_eq_res_simp:                        1
% 3.51/1.01  sim_fw_demodulated:                     268
% 3.51/1.01  sim_bw_demodulated:                     73
% 3.51/1.01  sim_light_normalised:                   224
% 3.51/1.01  sim_joinable_taut:                      1
% 3.51/1.01  sim_joinable_simp:                      0
% 3.51/1.01  sim_ac_normalised:                      0
% 3.51/1.01  sim_smt_subsumption:                    0
% 3.51/1.01  
%------------------------------------------------------------------------------
