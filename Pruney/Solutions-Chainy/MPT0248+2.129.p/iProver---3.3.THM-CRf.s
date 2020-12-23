%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:29 EST 2020

% Result     : Theorem 12.14s
% Output     : CNFRefutation 12.14s
% Verified   : 
% Statistics : Number of formulae       :  129 (3750 expanded)
%              Number of clauses        :   68 ( 738 expanded)
%              Number of leaves         :   19 (1134 expanded)
%              Depth                    :   23
%              Number of atoms          :  222 (5797 expanded)
%              Number of equality atoms :  205 (5628 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK4
        | k1_tarski(sK2) != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_xboole_0 != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_tarski(sK2) != sK3 )
      & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f39])).

fof(f70,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f78])).

fof(f94,plain,(
    k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f70,f58,f79])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f66,f79,f79])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f54,f50,f58])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f73,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,
    ( k1_xboole_0 != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f73,f79])).

fof(f71,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f71,f79,f79])).

fof(f72,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f8,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f52,f58])).

cnf(c_14,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_868,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1134,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_15])).

cnf(c_1676,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1134,c_15])).

cnf(c_1678,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1676,c_1134])).

cnf(c_2096,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_868,c_1678])).

cnf(c_23,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1130,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_15,c_23])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_865,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1292,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_865])).

cnf(c_1295,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1292,c_1130])).

cnf(c_2107,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2096,c_1295])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_879,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12,c_9])).

cnf(c_1137,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_879])).

cnf(c_1135,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_879,c_15])).

cnf(c_1688,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_879,c_1135])).

cnf(c_1700,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1688,c_13])).

cnf(c_1702,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1700,c_1135])).

cnf(c_1918,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1137,c_1702])).

cnf(c_1930,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1918,c_13])).

cnf(c_2392,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)),sK3) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2107,c_1930])).

cnf(c_2393,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,sK4),sK3)) = sK3
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2392,c_1678])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_881,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK3
    | sK4 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20,c_23])).

cnf(c_1128,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK3
    | sK4 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15,c_881])).

cnf(c_2391,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2107,c_1128])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_882,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK3
    | k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK4 ),
    inference(light_normalisation,[status(thm)],[c_22,c_23])).

cnf(c_1127,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK3
    | k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4 ),
    inference(demodulation,[status(thm)],[c_15,c_882])).

cnf(c_2389,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2107,c_1127])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_880,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK4
    | sK3 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21,c_23])).

cnf(c_1129,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15,c_880])).

cnf(c_2486,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2389,c_1129])).

cnf(c_2488,plain,
    ( sK3 != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2107,c_2486])).

cnf(c_11,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_869,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2652,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_869,c_1678])).

cnf(c_2668,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = k3_xboole_0(sK3,X0)
    | k3_xboole_0(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2652,c_1295])).

cnf(c_1940,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1702,c_1930])).

cnf(c_3156,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,X0),k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = sK3
    | k3_xboole_0(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2668,c_1940])).

cnf(c_4823,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0
    | sK3 = sK4 ),
    inference(superposition,[status(thm)],[c_3156,c_1930])).

cnf(c_2381,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)) = k5_xboole_0(sK3,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2107,c_1702])).

cnf(c_2396,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2381,c_879])).

cnf(c_33402,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) = k1_xboole_0
    | sK3 = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4823,c_2396])).

cnf(c_33560,plain,
    ( sK3 = sK4
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_33402,c_13])).

cnf(c_35045,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2393,c_2391,c_2488,c_33560])).

cnf(c_1126,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(demodulation,[status(thm)],[c_15,c_9])).

cnf(c_3163,plain,
    ( k3_xboole_0(sK3,X0) = k1_xboole_0
    | k3_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
    inference(superposition,[status(thm)],[c_2668,c_1126])).

cnf(c_35120,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35045,c_3163])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1760,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1700,c_10])).

cnf(c_2367,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1760,c_1702])).

cnf(c_2374,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_2367,c_13])).

cnf(c_35138,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35120,c_2374])).

cnf(c_1942,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1930,c_1702])).

cnf(c_1948,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_15,c_1942])).

cnf(c_2915,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) != sK4 ),
    inference(demodulation,[status(thm)],[c_1948,c_2486])).

cnf(c_35124,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK4))) != sK4 ),
    inference(demodulation,[status(thm)],[c_35045,c_2915])).

cnf(c_35137,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(k1_xboole_0,sK4)) != sK4 ),
    inference(demodulation,[status(thm)],[c_35124,c_1700])).

cnf(c_35140,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
    inference(demodulation,[status(thm)],[c_35138,c_35137])).

cnf(c_35149,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_35140,c_13])).

cnf(c_35150,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_35149])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 12.14/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.14/1.98  
% 12.14/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.14/1.98  
% 12.14/1.98  ------  iProver source info
% 12.14/1.98  
% 12.14/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.14/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.14/1.98  git: non_committed_changes: false
% 12.14/1.98  git: last_make_outside_of_git: false
% 12.14/1.98  
% 12.14/1.98  ------ 
% 12.14/1.98  
% 12.14/1.98  ------ Input Options
% 12.14/1.98  
% 12.14/1.98  --out_options                           all
% 12.14/1.98  --tptp_safe_out                         true
% 12.14/1.98  --problem_path                          ""
% 12.14/1.98  --include_path                          ""
% 12.14/1.98  --clausifier                            res/vclausify_rel
% 12.14/1.98  --clausifier_options                    ""
% 12.14/1.98  --stdin                                 false
% 12.14/1.98  --stats_out                             all
% 12.14/1.98  
% 12.14/1.98  ------ General Options
% 12.14/1.98  
% 12.14/1.98  --fof                                   false
% 12.14/1.98  --time_out_real                         305.
% 12.14/1.98  --time_out_virtual                      -1.
% 12.14/1.98  --symbol_type_check                     false
% 12.14/1.98  --clausify_out                          false
% 12.14/1.98  --sig_cnt_out                           false
% 12.14/1.98  --trig_cnt_out                          false
% 12.14/1.98  --trig_cnt_out_tolerance                1.
% 12.14/1.98  --trig_cnt_out_sk_spl                   false
% 12.14/1.98  --abstr_cl_out                          false
% 12.14/1.98  
% 12.14/1.98  ------ Global Options
% 12.14/1.98  
% 12.14/1.98  --schedule                              default
% 12.14/1.98  --add_important_lit                     false
% 12.14/1.98  --prop_solver_per_cl                    1000
% 12.14/1.98  --min_unsat_core                        false
% 12.14/1.98  --soft_assumptions                      false
% 12.14/1.98  --soft_lemma_size                       3
% 12.14/1.98  --prop_impl_unit_size                   0
% 12.14/1.98  --prop_impl_unit                        []
% 12.14/1.98  --share_sel_clauses                     true
% 12.14/1.98  --reset_solvers                         false
% 12.14/1.98  --bc_imp_inh                            [conj_cone]
% 12.14/1.98  --conj_cone_tolerance                   3.
% 12.14/1.98  --extra_neg_conj                        none
% 12.14/1.98  --large_theory_mode                     true
% 12.14/1.98  --prolific_symb_bound                   200
% 12.14/1.98  --lt_threshold                          2000
% 12.14/1.98  --clause_weak_htbl                      true
% 12.14/1.98  --gc_record_bc_elim                     false
% 12.14/1.98  
% 12.14/1.98  ------ Preprocessing Options
% 12.14/1.98  
% 12.14/1.98  --preprocessing_flag                    true
% 12.14/1.98  --time_out_prep_mult                    0.1
% 12.14/1.98  --splitting_mode                        input
% 12.14/1.98  --splitting_grd                         true
% 12.14/1.98  --splitting_cvd                         false
% 12.14/1.98  --splitting_cvd_svl                     false
% 12.14/1.98  --splitting_nvd                         32
% 12.14/1.98  --sub_typing                            true
% 12.14/1.98  --prep_gs_sim                           true
% 12.14/1.98  --prep_unflatten                        true
% 12.14/1.98  --prep_res_sim                          true
% 12.14/1.98  --prep_upred                            true
% 12.14/1.98  --prep_sem_filter                       exhaustive
% 12.14/1.98  --prep_sem_filter_out                   false
% 12.14/1.98  --pred_elim                             true
% 12.14/1.98  --res_sim_input                         true
% 12.14/1.98  --eq_ax_congr_red                       true
% 12.14/1.98  --pure_diseq_elim                       true
% 12.14/1.98  --brand_transform                       false
% 12.14/1.98  --non_eq_to_eq                          false
% 12.14/1.98  --prep_def_merge                        true
% 12.14/1.98  --prep_def_merge_prop_impl              false
% 12.14/1.98  --prep_def_merge_mbd                    true
% 12.14/1.98  --prep_def_merge_tr_red                 false
% 12.14/1.98  --prep_def_merge_tr_cl                  false
% 12.14/1.98  --smt_preprocessing                     true
% 12.14/1.98  --smt_ac_axioms                         fast
% 12.14/1.98  --preprocessed_out                      false
% 12.14/1.98  --preprocessed_stats                    false
% 12.14/1.98  
% 12.14/1.98  ------ Abstraction refinement Options
% 12.14/1.98  
% 12.14/1.98  --abstr_ref                             []
% 12.14/1.98  --abstr_ref_prep                        false
% 12.14/1.98  --abstr_ref_until_sat                   false
% 12.14/1.98  --abstr_ref_sig_restrict                funpre
% 12.14/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.14/1.98  --abstr_ref_under                       []
% 12.14/1.98  
% 12.14/1.98  ------ SAT Options
% 12.14/1.98  
% 12.14/1.98  --sat_mode                              false
% 12.14/1.98  --sat_fm_restart_options                ""
% 12.14/1.98  --sat_gr_def                            false
% 12.14/1.98  --sat_epr_types                         true
% 12.14/1.98  --sat_non_cyclic_types                  false
% 12.14/1.98  --sat_finite_models                     false
% 12.14/1.98  --sat_fm_lemmas                         false
% 12.14/1.98  --sat_fm_prep                           false
% 12.14/1.98  --sat_fm_uc_incr                        true
% 12.14/1.98  --sat_out_model                         small
% 12.14/1.98  --sat_out_clauses                       false
% 12.14/1.98  
% 12.14/1.98  ------ QBF Options
% 12.14/1.98  
% 12.14/1.98  --qbf_mode                              false
% 12.14/1.98  --qbf_elim_univ                         false
% 12.14/1.98  --qbf_dom_inst                          none
% 12.14/1.98  --qbf_dom_pre_inst                      false
% 12.14/1.98  --qbf_sk_in                             false
% 12.14/1.98  --qbf_pred_elim                         true
% 12.14/1.98  --qbf_split                             512
% 12.14/1.98  
% 12.14/1.98  ------ BMC1 Options
% 12.14/1.98  
% 12.14/1.98  --bmc1_incremental                      false
% 12.14/1.98  --bmc1_axioms                           reachable_all
% 12.14/1.98  --bmc1_min_bound                        0
% 12.14/1.98  --bmc1_max_bound                        -1
% 12.14/1.98  --bmc1_max_bound_default                -1
% 12.14/1.98  --bmc1_symbol_reachability              true
% 12.14/1.98  --bmc1_property_lemmas                  false
% 12.14/1.98  --bmc1_k_induction                      false
% 12.14/1.98  --bmc1_non_equiv_states                 false
% 12.14/1.98  --bmc1_deadlock                         false
% 12.14/1.98  --bmc1_ucm                              false
% 12.14/1.98  --bmc1_add_unsat_core                   none
% 12.14/1.98  --bmc1_unsat_core_children              false
% 12.14/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.14/1.98  --bmc1_out_stat                         full
% 12.14/1.98  --bmc1_ground_init                      false
% 12.14/1.98  --bmc1_pre_inst_next_state              false
% 12.14/1.98  --bmc1_pre_inst_state                   false
% 12.14/1.98  --bmc1_pre_inst_reach_state             false
% 12.14/1.98  --bmc1_out_unsat_core                   false
% 12.14/1.98  --bmc1_aig_witness_out                  false
% 12.14/1.98  --bmc1_verbose                          false
% 12.14/1.98  --bmc1_dump_clauses_tptp                false
% 12.14/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.14/1.98  --bmc1_dump_file                        -
% 12.14/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.14/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.14/1.98  --bmc1_ucm_extend_mode                  1
% 12.14/1.98  --bmc1_ucm_init_mode                    2
% 12.14/1.98  --bmc1_ucm_cone_mode                    none
% 12.14/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.14/1.98  --bmc1_ucm_relax_model                  4
% 12.14/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.14/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.14/1.98  --bmc1_ucm_layered_model                none
% 12.14/1.98  --bmc1_ucm_max_lemma_size               10
% 12.14/1.98  
% 12.14/1.98  ------ AIG Options
% 12.14/1.98  
% 12.14/1.98  --aig_mode                              false
% 12.14/1.98  
% 12.14/1.98  ------ Instantiation Options
% 12.14/1.98  
% 12.14/1.98  --instantiation_flag                    true
% 12.14/1.98  --inst_sos_flag                         true
% 12.14/1.98  --inst_sos_phase                        true
% 12.14/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.14/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.14/1.98  --inst_lit_sel_side                     num_symb
% 12.14/1.98  --inst_solver_per_active                1400
% 12.14/1.98  --inst_solver_calls_frac                1.
% 12.14/1.98  --inst_passive_queue_type               priority_queues
% 12.14/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.14/1.98  --inst_passive_queues_freq              [25;2]
% 12.14/1.98  --inst_dismatching                      true
% 12.14/1.98  --inst_eager_unprocessed_to_passive     true
% 12.14/1.98  --inst_prop_sim_given                   true
% 12.14/1.98  --inst_prop_sim_new                     false
% 12.14/1.98  --inst_subs_new                         false
% 12.14/1.98  --inst_eq_res_simp                      false
% 12.14/1.98  --inst_subs_given                       false
% 12.14/1.98  --inst_orphan_elimination               true
% 12.14/1.98  --inst_learning_loop_flag               true
% 12.14/1.98  --inst_learning_start                   3000
% 12.14/1.98  --inst_learning_factor                  2
% 12.14/1.98  --inst_start_prop_sim_after_learn       3
% 12.14/1.98  --inst_sel_renew                        solver
% 12.14/1.98  --inst_lit_activity_flag                true
% 12.14/1.98  --inst_restr_to_given                   false
% 12.14/1.98  --inst_activity_threshold               500
% 12.14/1.98  --inst_out_proof                        true
% 12.14/1.98  
% 12.14/1.98  ------ Resolution Options
% 12.14/1.98  
% 12.14/1.98  --resolution_flag                       true
% 12.14/1.98  --res_lit_sel                           adaptive
% 12.14/1.98  --res_lit_sel_side                      none
% 12.14/1.98  --res_ordering                          kbo
% 12.14/1.98  --res_to_prop_solver                    active
% 12.14/1.98  --res_prop_simpl_new                    false
% 12.14/1.98  --res_prop_simpl_given                  true
% 12.14/1.98  --res_passive_queue_type                priority_queues
% 12.14/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.14/1.98  --res_passive_queues_freq               [15;5]
% 12.14/1.98  --res_forward_subs                      full
% 12.14/1.98  --res_backward_subs                     full
% 12.14/1.98  --res_forward_subs_resolution           true
% 12.14/1.98  --res_backward_subs_resolution          true
% 12.14/1.98  --res_orphan_elimination                true
% 12.14/1.98  --res_time_limit                        2.
% 12.14/1.98  --res_out_proof                         true
% 12.14/1.98  
% 12.14/1.98  ------ Superposition Options
% 12.14/1.98  
% 12.14/1.98  --superposition_flag                    true
% 12.14/1.98  --sup_passive_queue_type                priority_queues
% 12.14/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.14/1.98  --sup_passive_queues_freq               [8;1;4]
% 12.14/1.98  --demod_completeness_check              fast
% 12.14/1.98  --demod_use_ground                      true
% 12.14/1.98  --sup_to_prop_solver                    passive
% 12.14/1.98  --sup_prop_simpl_new                    true
% 12.14/1.98  --sup_prop_simpl_given                  true
% 12.14/1.98  --sup_fun_splitting                     true
% 12.14/1.98  --sup_smt_interval                      50000
% 12.14/1.98  
% 12.14/1.98  ------ Superposition Simplification Setup
% 12.14/1.98  
% 12.14/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.14/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.14/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.14/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.14/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.14/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.14/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.14/1.98  --sup_immed_triv                        [TrivRules]
% 12.14/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.14/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.14/1.98  --sup_immed_bw_main                     []
% 12.14/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.14/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.14/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.14/1.98  --sup_input_bw                          []
% 12.14/1.98  
% 12.14/1.98  ------ Combination Options
% 12.14/1.98  
% 12.14/1.98  --comb_res_mult                         3
% 12.14/1.98  --comb_sup_mult                         2
% 12.14/1.98  --comb_inst_mult                        10
% 12.14/1.98  
% 12.14/1.98  ------ Debug Options
% 12.14/1.98  
% 12.14/1.98  --dbg_backtrace                         false
% 12.14/1.98  --dbg_dump_prop_clauses                 false
% 12.14/1.98  --dbg_dump_prop_clauses_file            -
% 12.14/1.98  --dbg_out_stat                          false
% 12.14/1.98  ------ Parsing...
% 12.14/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.14/1.98  
% 12.14/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 12.14/1.98  
% 12.14/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.14/1.98  
% 12.14/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.14/1.98  ------ Proving...
% 12.14/1.98  ------ Problem Properties 
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  clauses                                 24
% 12.14/1.98  conjectures                             4
% 12.14/1.98  EPR                                     1
% 12.14/1.98  Horn                                    21
% 12.14/1.98  unary                                   11
% 12.14/1.98  binary                                  11
% 12.14/1.98  lits                                    39
% 12.14/1.98  lits eq                                 19
% 12.14/1.98  fd_pure                                 0
% 12.14/1.98  fd_pseudo                               0
% 12.14/1.98  fd_cond                                 0
% 12.14/1.98  fd_pseudo_cond                          1
% 12.14/1.98  AC symbols                              0
% 12.14/1.98  
% 12.14/1.98  ------ Schedule dynamic 5 is on 
% 12.14/1.98  
% 12.14/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  ------ 
% 12.14/1.98  Current options:
% 12.14/1.98  ------ 
% 12.14/1.98  
% 12.14/1.98  ------ Input Options
% 12.14/1.98  
% 12.14/1.98  --out_options                           all
% 12.14/1.98  --tptp_safe_out                         true
% 12.14/1.98  --problem_path                          ""
% 12.14/1.98  --include_path                          ""
% 12.14/1.98  --clausifier                            res/vclausify_rel
% 12.14/1.98  --clausifier_options                    ""
% 12.14/1.98  --stdin                                 false
% 12.14/1.98  --stats_out                             all
% 12.14/1.98  
% 12.14/1.98  ------ General Options
% 12.14/1.98  
% 12.14/1.98  --fof                                   false
% 12.14/1.98  --time_out_real                         305.
% 12.14/1.98  --time_out_virtual                      -1.
% 12.14/1.98  --symbol_type_check                     false
% 12.14/1.98  --clausify_out                          false
% 12.14/1.98  --sig_cnt_out                           false
% 12.14/1.98  --trig_cnt_out                          false
% 12.14/1.98  --trig_cnt_out_tolerance                1.
% 12.14/1.98  --trig_cnt_out_sk_spl                   false
% 12.14/1.98  --abstr_cl_out                          false
% 12.14/1.98  
% 12.14/1.98  ------ Global Options
% 12.14/1.98  
% 12.14/1.98  --schedule                              default
% 12.14/1.98  --add_important_lit                     false
% 12.14/1.98  --prop_solver_per_cl                    1000
% 12.14/1.98  --min_unsat_core                        false
% 12.14/1.98  --soft_assumptions                      false
% 12.14/1.98  --soft_lemma_size                       3
% 12.14/1.98  --prop_impl_unit_size                   0
% 12.14/1.98  --prop_impl_unit                        []
% 12.14/1.98  --share_sel_clauses                     true
% 12.14/1.98  --reset_solvers                         false
% 12.14/1.98  --bc_imp_inh                            [conj_cone]
% 12.14/1.98  --conj_cone_tolerance                   3.
% 12.14/1.98  --extra_neg_conj                        none
% 12.14/1.98  --large_theory_mode                     true
% 12.14/1.98  --prolific_symb_bound                   200
% 12.14/1.98  --lt_threshold                          2000
% 12.14/1.98  --clause_weak_htbl                      true
% 12.14/1.98  --gc_record_bc_elim                     false
% 12.14/1.98  
% 12.14/1.98  ------ Preprocessing Options
% 12.14/1.98  
% 12.14/1.98  --preprocessing_flag                    true
% 12.14/1.98  --time_out_prep_mult                    0.1
% 12.14/1.98  --splitting_mode                        input
% 12.14/1.98  --splitting_grd                         true
% 12.14/1.98  --splitting_cvd                         false
% 12.14/1.98  --splitting_cvd_svl                     false
% 12.14/1.98  --splitting_nvd                         32
% 12.14/1.98  --sub_typing                            true
% 12.14/1.98  --prep_gs_sim                           true
% 12.14/1.98  --prep_unflatten                        true
% 12.14/1.98  --prep_res_sim                          true
% 12.14/1.98  --prep_upred                            true
% 12.14/1.98  --prep_sem_filter                       exhaustive
% 12.14/1.98  --prep_sem_filter_out                   false
% 12.14/1.98  --pred_elim                             true
% 12.14/1.98  --res_sim_input                         true
% 12.14/1.98  --eq_ax_congr_red                       true
% 12.14/1.98  --pure_diseq_elim                       true
% 12.14/1.98  --brand_transform                       false
% 12.14/1.98  --non_eq_to_eq                          false
% 12.14/1.98  --prep_def_merge                        true
% 12.14/1.98  --prep_def_merge_prop_impl              false
% 12.14/1.98  --prep_def_merge_mbd                    true
% 12.14/1.98  --prep_def_merge_tr_red                 false
% 12.14/1.98  --prep_def_merge_tr_cl                  false
% 12.14/1.98  --smt_preprocessing                     true
% 12.14/1.98  --smt_ac_axioms                         fast
% 12.14/1.98  --preprocessed_out                      false
% 12.14/1.98  --preprocessed_stats                    false
% 12.14/1.98  
% 12.14/1.98  ------ Abstraction refinement Options
% 12.14/1.98  
% 12.14/1.98  --abstr_ref                             []
% 12.14/1.98  --abstr_ref_prep                        false
% 12.14/1.98  --abstr_ref_until_sat                   false
% 12.14/1.98  --abstr_ref_sig_restrict                funpre
% 12.14/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.14/1.98  --abstr_ref_under                       []
% 12.14/1.98  
% 12.14/1.98  ------ SAT Options
% 12.14/1.98  
% 12.14/1.98  --sat_mode                              false
% 12.14/1.98  --sat_fm_restart_options                ""
% 12.14/1.98  --sat_gr_def                            false
% 12.14/1.98  --sat_epr_types                         true
% 12.14/1.98  --sat_non_cyclic_types                  false
% 12.14/1.98  --sat_finite_models                     false
% 12.14/1.98  --sat_fm_lemmas                         false
% 12.14/1.98  --sat_fm_prep                           false
% 12.14/1.98  --sat_fm_uc_incr                        true
% 12.14/1.98  --sat_out_model                         small
% 12.14/1.98  --sat_out_clauses                       false
% 12.14/1.98  
% 12.14/1.98  ------ QBF Options
% 12.14/1.98  
% 12.14/1.98  --qbf_mode                              false
% 12.14/1.98  --qbf_elim_univ                         false
% 12.14/1.98  --qbf_dom_inst                          none
% 12.14/1.98  --qbf_dom_pre_inst                      false
% 12.14/1.98  --qbf_sk_in                             false
% 12.14/1.98  --qbf_pred_elim                         true
% 12.14/1.98  --qbf_split                             512
% 12.14/1.98  
% 12.14/1.98  ------ BMC1 Options
% 12.14/1.98  
% 12.14/1.98  --bmc1_incremental                      false
% 12.14/1.98  --bmc1_axioms                           reachable_all
% 12.14/1.98  --bmc1_min_bound                        0
% 12.14/1.98  --bmc1_max_bound                        -1
% 12.14/1.98  --bmc1_max_bound_default                -1
% 12.14/1.98  --bmc1_symbol_reachability              true
% 12.14/1.98  --bmc1_property_lemmas                  false
% 12.14/1.98  --bmc1_k_induction                      false
% 12.14/1.98  --bmc1_non_equiv_states                 false
% 12.14/1.98  --bmc1_deadlock                         false
% 12.14/1.98  --bmc1_ucm                              false
% 12.14/1.98  --bmc1_add_unsat_core                   none
% 12.14/1.98  --bmc1_unsat_core_children              false
% 12.14/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.14/1.98  --bmc1_out_stat                         full
% 12.14/1.98  --bmc1_ground_init                      false
% 12.14/1.98  --bmc1_pre_inst_next_state              false
% 12.14/1.98  --bmc1_pre_inst_state                   false
% 12.14/1.98  --bmc1_pre_inst_reach_state             false
% 12.14/1.98  --bmc1_out_unsat_core                   false
% 12.14/1.98  --bmc1_aig_witness_out                  false
% 12.14/1.98  --bmc1_verbose                          false
% 12.14/1.98  --bmc1_dump_clauses_tptp                false
% 12.14/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.14/1.98  --bmc1_dump_file                        -
% 12.14/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.14/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.14/1.98  --bmc1_ucm_extend_mode                  1
% 12.14/1.98  --bmc1_ucm_init_mode                    2
% 12.14/1.98  --bmc1_ucm_cone_mode                    none
% 12.14/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.14/1.98  --bmc1_ucm_relax_model                  4
% 12.14/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.14/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.14/1.98  --bmc1_ucm_layered_model                none
% 12.14/1.98  --bmc1_ucm_max_lemma_size               10
% 12.14/1.98  
% 12.14/1.98  ------ AIG Options
% 12.14/1.98  
% 12.14/1.98  --aig_mode                              false
% 12.14/1.98  
% 12.14/1.98  ------ Instantiation Options
% 12.14/1.98  
% 12.14/1.98  --instantiation_flag                    true
% 12.14/1.98  --inst_sos_flag                         true
% 12.14/1.98  --inst_sos_phase                        true
% 12.14/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.14/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.14/1.98  --inst_lit_sel_side                     none
% 12.14/1.98  --inst_solver_per_active                1400
% 12.14/1.98  --inst_solver_calls_frac                1.
% 12.14/1.98  --inst_passive_queue_type               priority_queues
% 12.14/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.14/1.98  --inst_passive_queues_freq              [25;2]
% 12.14/1.98  --inst_dismatching                      true
% 12.14/1.98  --inst_eager_unprocessed_to_passive     true
% 12.14/1.98  --inst_prop_sim_given                   true
% 12.14/1.98  --inst_prop_sim_new                     false
% 12.14/1.98  --inst_subs_new                         false
% 12.14/1.98  --inst_eq_res_simp                      false
% 12.14/1.98  --inst_subs_given                       false
% 12.14/1.98  --inst_orphan_elimination               true
% 12.14/1.98  --inst_learning_loop_flag               true
% 12.14/1.98  --inst_learning_start                   3000
% 12.14/1.98  --inst_learning_factor                  2
% 12.14/1.98  --inst_start_prop_sim_after_learn       3
% 12.14/1.98  --inst_sel_renew                        solver
% 12.14/1.98  --inst_lit_activity_flag                true
% 12.14/1.98  --inst_restr_to_given                   false
% 12.14/1.98  --inst_activity_threshold               500
% 12.14/1.98  --inst_out_proof                        true
% 12.14/1.98  
% 12.14/1.98  ------ Resolution Options
% 12.14/1.98  
% 12.14/1.98  --resolution_flag                       false
% 12.14/1.98  --res_lit_sel                           adaptive
% 12.14/1.98  --res_lit_sel_side                      none
% 12.14/1.98  --res_ordering                          kbo
% 12.14/1.98  --res_to_prop_solver                    active
% 12.14/1.98  --res_prop_simpl_new                    false
% 12.14/1.98  --res_prop_simpl_given                  true
% 12.14/1.98  --res_passive_queue_type                priority_queues
% 12.14/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.14/1.98  --res_passive_queues_freq               [15;5]
% 12.14/1.98  --res_forward_subs                      full
% 12.14/1.98  --res_backward_subs                     full
% 12.14/1.98  --res_forward_subs_resolution           true
% 12.14/1.98  --res_backward_subs_resolution          true
% 12.14/1.98  --res_orphan_elimination                true
% 12.14/1.98  --res_time_limit                        2.
% 12.14/1.98  --res_out_proof                         true
% 12.14/1.98  
% 12.14/1.98  ------ Superposition Options
% 12.14/1.98  
% 12.14/1.98  --superposition_flag                    true
% 12.14/1.98  --sup_passive_queue_type                priority_queues
% 12.14/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.14/1.98  --sup_passive_queues_freq               [8;1;4]
% 12.14/1.98  --demod_completeness_check              fast
% 12.14/1.98  --demod_use_ground                      true
% 12.14/1.98  --sup_to_prop_solver                    passive
% 12.14/1.98  --sup_prop_simpl_new                    true
% 12.14/1.98  --sup_prop_simpl_given                  true
% 12.14/1.98  --sup_fun_splitting                     true
% 12.14/1.98  --sup_smt_interval                      50000
% 12.14/1.98  
% 12.14/1.98  ------ Superposition Simplification Setup
% 12.14/1.98  
% 12.14/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.14/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.14/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.14/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.14/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.14/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.14/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.14/1.98  --sup_immed_triv                        [TrivRules]
% 12.14/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.14/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.14/1.98  --sup_immed_bw_main                     []
% 12.14/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.14/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.14/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.14/1.98  --sup_input_bw                          []
% 12.14/1.98  
% 12.14/1.98  ------ Combination Options
% 12.14/1.98  
% 12.14/1.98  --comb_res_mult                         3
% 12.14/1.98  --comb_sup_mult                         2
% 12.14/1.98  --comb_inst_mult                        10
% 12.14/1.98  
% 12.14/1.98  ------ Debug Options
% 12.14/1.98  
% 12.14/1.98  --dbg_backtrace                         false
% 12.14/1.98  --dbg_dump_prop_clauses                 false
% 12.14/1.98  --dbg_dump_prop_clauses_file            -
% 12.14/1.98  --dbg_out_stat                          false
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  ------ Proving...
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  % SZS status Theorem for theBenchmark.p
% 12.14/1.98  
% 12.14/1.98   Resolution empty clause
% 12.14/1.98  
% 12.14/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.14/1.98  
% 12.14/1.98  fof(f11,axiom,(
% 12.14/1.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f56,plain,(
% 12.14/1.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.14/1.98    inference(cnf_transformation,[],[f11])).
% 12.14/1.98  
% 12.14/1.98  fof(f13,axiom,(
% 12.14/1.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f58,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f13])).
% 12.14/1.98  
% 12.14/1.98  fof(f86,plain,(
% 12.14/1.98    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 12.14/1.98    inference(definition_unfolding,[],[f56,f58])).
% 12.14/1.98  
% 12.14/1.98  fof(f10,axiom,(
% 12.14/1.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f55,plain,(
% 12.14/1.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.14/1.98    inference(cnf_transformation,[],[f10])).
% 12.14/1.98  
% 12.14/1.98  fof(f12,axiom,(
% 12.14/1.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f57,plain,(
% 12.14/1.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f12])).
% 12.14/1.98  
% 12.14/1.98  fof(f23,conjecture,(
% 12.14/1.98    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f24,negated_conjecture,(
% 12.14/1.98    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 12.14/1.98    inference(negated_conjecture,[],[f23])).
% 12.14/1.98  
% 12.14/1.98  fof(f28,plain,(
% 12.14/1.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 12.14/1.98    inference(ennf_transformation,[],[f24])).
% 12.14/1.98  
% 12.14/1.98  fof(f39,plain,(
% 12.14/1.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 12.14/1.98    introduced(choice_axiom,[])).
% 12.14/1.98  
% 12.14/1.98  fof(f40,plain,(
% 12.14/1.98    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 12.14/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f39])).
% 12.14/1.98  
% 12.14/1.98  fof(f70,plain,(
% 12.14/1.98    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 12.14/1.98    inference(cnf_transformation,[],[f40])).
% 12.14/1.98  
% 12.14/1.98  fof(f14,axiom,(
% 12.14/1.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f59,plain,(
% 12.14/1.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f14])).
% 12.14/1.98  
% 12.14/1.98  fof(f15,axiom,(
% 12.14/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f60,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f15])).
% 12.14/1.98  
% 12.14/1.98  fof(f16,axiom,(
% 12.14/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f61,plain,(
% 12.14/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f16])).
% 12.14/1.98  
% 12.14/1.98  fof(f17,axiom,(
% 12.14/1.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f62,plain,(
% 12.14/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f17])).
% 12.14/1.98  
% 12.14/1.98  fof(f18,axiom,(
% 12.14/1.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f63,plain,(
% 12.14/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f18])).
% 12.14/1.98  
% 12.14/1.98  fof(f19,axiom,(
% 12.14/1.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f64,plain,(
% 12.14/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f19])).
% 12.14/1.98  
% 12.14/1.98  fof(f20,axiom,(
% 12.14/1.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f65,plain,(
% 12.14/1.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 12.14/1.98    inference(cnf_transformation,[],[f20])).
% 12.14/1.98  
% 12.14/1.98  fof(f74,plain,(
% 12.14/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 12.14/1.98    inference(definition_unfolding,[],[f64,f65])).
% 12.14/1.98  
% 12.14/1.98  fof(f75,plain,(
% 12.14/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 12.14/1.98    inference(definition_unfolding,[],[f63,f74])).
% 12.14/1.98  
% 12.14/1.98  fof(f76,plain,(
% 12.14/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 12.14/1.98    inference(definition_unfolding,[],[f62,f75])).
% 12.14/1.98  
% 12.14/1.98  fof(f77,plain,(
% 12.14/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 12.14/1.98    inference(definition_unfolding,[],[f61,f76])).
% 12.14/1.98  
% 12.14/1.98  fof(f78,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 12.14/1.98    inference(definition_unfolding,[],[f60,f77])).
% 12.14/1.98  
% 12.14/1.98  fof(f79,plain,(
% 12.14/1.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 12.14/1.98    inference(definition_unfolding,[],[f59,f78])).
% 12.14/1.98  
% 12.14/1.98  fof(f94,plain,(
% 12.14/1.98    k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 12.14/1.98    inference(definition_unfolding,[],[f70,f58,f79])).
% 12.14/1.98  
% 12.14/1.98  fof(f21,axiom,(
% 12.14/1.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f37,plain,(
% 12.14/1.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 12.14/1.98    inference(nnf_transformation,[],[f21])).
% 12.14/1.98  
% 12.14/1.98  fof(f38,plain,(
% 12.14/1.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 12.14/1.98    inference(flattening,[],[f37])).
% 12.14/1.98  
% 12.14/1.98  fof(f66,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 12.14/1.98    inference(cnf_transformation,[],[f38])).
% 12.14/1.98  
% 12.14/1.98  fof(f89,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 12.14/1.98    inference(definition_unfolding,[],[f66,f79,f79])).
% 12.14/1.98  
% 12.14/1.98  fof(f9,axiom,(
% 12.14/1.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f54,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 12.14/1.98    inference(cnf_transformation,[],[f9])).
% 12.14/1.98  
% 12.14/1.98  fof(f5,axiom,(
% 12.14/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f50,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.14/1.98    inference(cnf_transformation,[],[f5])).
% 12.14/1.98  
% 12.14/1.98  fof(f85,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))))) )),
% 12.14/1.98    inference(definition_unfolding,[],[f54,f50,f58])).
% 12.14/1.98  
% 12.14/1.98  fof(f6,axiom,(
% 12.14/1.98    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f51,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 12.14/1.98    inference(cnf_transformation,[],[f6])).
% 12.14/1.98  
% 12.14/1.98  fof(f82,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0) )),
% 12.14/1.98    inference(definition_unfolding,[],[f51,f58])).
% 12.14/1.98  
% 12.14/1.98  fof(f73,plain,(
% 12.14/1.98    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 12.14/1.98    inference(cnf_transformation,[],[f40])).
% 12.14/1.98  
% 12.14/1.98  fof(f91,plain,(
% 12.14/1.98    k1_xboole_0 != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 12.14/1.98    inference(definition_unfolding,[],[f73,f79])).
% 12.14/1.98  
% 12.14/1.98  fof(f71,plain,(
% 12.14/1.98    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 12.14/1.98    inference(cnf_transformation,[],[f40])).
% 12.14/1.98  
% 12.14/1.98  fof(f93,plain,(
% 12.14/1.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 12.14/1.98    inference(definition_unfolding,[],[f71,f79,f79])).
% 12.14/1.98  
% 12.14/1.98  fof(f72,plain,(
% 12.14/1.98    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 12.14/1.98    inference(cnf_transformation,[],[f40])).
% 12.14/1.98  
% 12.14/1.98  fof(f92,plain,(
% 12.14/1.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 12.14/1.98    inference(definition_unfolding,[],[f72,f79])).
% 12.14/1.98  
% 12.14/1.98  fof(f8,axiom,(
% 12.14/1.98    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f53,plain,(
% 12.14/1.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 12.14/1.98    inference(cnf_transformation,[],[f8])).
% 12.14/1.98  
% 12.14/1.98  fof(f84,plain,(
% 12.14/1.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2)))) )),
% 12.14/1.98    inference(definition_unfolding,[],[f53,f58])).
% 12.14/1.98  
% 12.14/1.98  fof(f7,axiom,(
% 12.14/1.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 12.14/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.14/1.98  
% 12.14/1.98  fof(f52,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 12.14/1.98    inference(cnf_transformation,[],[f7])).
% 12.14/1.98  
% 12.14/1.98  fof(f83,plain,(
% 12.14/1.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0) )),
% 12.14/1.98    inference(definition_unfolding,[],[f52,f58])).
% 12.14/1.98  
% 12.14/1.98  cnf(c_14,plain,
% 12.14/1.98      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
% 12.14/1.98      inference(cnf_transformation,[],[f86]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_868,plain,
% 12.14/1.98      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = iProver_top ),
% 12.14/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_13,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.14/1.98      inference(cnf_transformation,[],[f55]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_15,plain,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 12.14/1.98      inference(cnf_transformation,[],[f57]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1134,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_13,c_15]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1676,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_1134,c_15]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1678,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_1676,c_1134]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2096,plain,
% 12.14/1.98      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_868,c_1678]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_23,negated_conjecture,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 12.14/1.98      inference(cnf_transformation,[],[f94]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1130,plain,
% 12.14/1.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_15,c_23]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_18,plain,
% 12.14/1.98      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 12.14/1.98      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 12.14/1.98      | k1_xboole_0 = X0 ),
% 12.14/1.98      inference(cnf_transformation,[],[f89]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_865,plain,
% 12.14/1.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 12.14/1.98      | k1_xboole_0 = X1
% 12.14/1.98      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 12.14/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1292,plain,
% 12.14/1.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 12.14/1.98      | k1_xboole_0 = X0
% 12.14/1.98      | r1_tarski(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)))) != iProver_top ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_1130,c_865]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1295,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = X0
% 12.14/1.98      | k1_xboole_0 = X0
% 12.14/1.98      | r1_tarski(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)))) != iProver_top ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_1292,c_1130]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2107,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = sK3
% 12.14/1.98      | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2096,c_1295]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_12,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 12.14/1.98      inference(cnf_transformation,[],[f85]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_9,plain,
% 12.14/1.98      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
% 12.14/1.98      inference(cnf_transformation,[],[f82]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_879,plain,
% 12.14/1.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.14/1.98      inference(light_normalisation,[status(thm)],[c_12,c_9]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1137,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_15,c_879]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1135,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_879,c_15]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1688,plain,
% 12.14/1.98      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_879,c_1135]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1700,plain,
% 12.14/1.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 12.14/1.98      inference(light_normalisation,[status(thm)],[c_1688,c_13]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1702,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_1700,c_1135]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1918,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_1137,c_1702]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1930,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_1918,c_13]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2392,plain,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)),sK3) = sK3
% 12.14/1.98      | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2107,c_1930]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2393,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,sK4),sK3)) = sK3
% 12.14/1.98      | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_2392,c_1678]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_20,negated_conjecture,
% 12.14/1.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 12.14/1.98      | k1_xboole_0 != sK4 ),
% 12.14/1.98      inference(cnf_transformation,[],[f91]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_881,plain,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK3
% 12.14/1.98      | sK4 != k1_xboole_0 ),
% 12.14/1.98      inference(light_normalisation,[status(thm)],[c_20,c_23]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1128,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK3
% 12.14/1.98      | sK4 != k1_xboole_0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_15,c_881]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2391,plain,
% 12.14/1.98      ( sK3 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2107,c_1128]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_22,negated_conjecture,
% 12.14/1.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 12.14/1.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 12.14/1.98      inference(cnf_transformation,[],[f93]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_882,plain,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK3
% 12.14/1.98      | k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK4 ),
% 12.14/1.98      inference(light_normalisation,[status(thm)],[c_22,c_23]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1127,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK3
% 12.14/1.98      | k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_15,c_882]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2389,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4
% 12.14/1.98      | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2107,c_1127]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_21,negated_conjecture,
% 12.14/1.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 12.14/1.98      | k1_xboole_0 != sK3 ),
% 12.14/1.98      inference(cnf_transformation,[],[f92]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_880,plain,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != sK4
% 12.14/1.98      | sK3 != k1_xboole_0 ),
% 12.14/1.98      inference(light_normalisation,[status(thm)],[c_21,c_23]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1129,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4
% 12.14/1.98      | sK3 != k1_xboole_0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_15,c_880]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2486,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) != sK4 ),
% 12.14/1.98      inference(global_propositional_subsumption,[status(thm)],[c_2389,c_1129]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2488,plain,
% 12.14/1.98      ( sK3 != sK4 | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2107,c_2486]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_11,plain,
% 12.14/1.98      ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2))) ),
% 12.14/1.98      inference(cnf_transformation,[],[f84]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_869,plain,
% 12.14/1.98      ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2))) = iProver_top ),
% 12.14/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2652,plain,
% 12.14/1.98      ( r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = iProver_top ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_869,c_1678]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2668,plain,
% 12.14/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = k3_xboole_0(sK3,X0)
% 12.14/1.98      | k3_xboole_0(sK3,X0) = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2652,c_1295]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1940,plain,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_1702,c_1930]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_3156,plain,
% 12.14/1.98      ( k5_xboole_0(k3_xboole_0(sK3,X0),k5_xboole_0(sK4,k3_xboole_0(sK3,sK4))) = sK3
% 12.14/1.98      | k3_xboole_0(sK3,X0) = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2668,c_1940]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_4823,plain,
% 12.14/1.98      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 | sK3 = sK4 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_3156,c_1930]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2381,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)) = k5_xboole_0(sK3,sK3)
% 12.14/1.98      | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2107,c_1702]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2396,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k3_xboole_0(sK3,sK4)) = k1_xboole_0
% 12.14/1.98      | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_2381,c_879]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_33402,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k1_xboole_0) = k1_xboole_0
% 12.14/1.98      | sK3 = sK4
% 12.14/1.98      | sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_4823,c_2396]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_33560,plain,
% 12.14/1.98      ( sK3 = sK4 | sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_33402,c_13]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35045,plain,
% 12.14/1.98      ( sK3 = k1_xboole_0 ),
% 12.14/1.98      inference(global_propositional_subsumption,
% 12.14/1.98                [status(thm)],
% 12.14/1.98                [c_2393,c_2391,c_2488,c_33560]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1126,plain,
% 12.14/1.98      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_15,c_9]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_3163,plain,
% 12.14/1.98      ( k3_xboole_0(sK3,X0) = k1_xboole_0
% 12.14/1.98      | k3_xboole_0(sK3,k3_xboole_0(sK3,X0)) = sK3 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_2668,c_1126]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35120,plain,
% 12.14/1.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0
% 12.14/1.98      | k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_35045,c_3163]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_10,plain,
% 12.14/1.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
% 12.14/1.98      inference(cnf_transformation,[],[f83]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1760,plain,
% 12.14/1.98      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_1700,c_10]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2367,plain,
% 12.14/1.98      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_1760,c_1702]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2374,plain,
% 12.14/1.98      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_2367,c_13]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35138,plain,
% 12.14/1.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_35120,c_2374]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1942,plain,
% 12.14/1.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_1930,c_1702]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_1948,plain,
% 12.14/1.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 12.14/1.98      inference(superposition,[status(thm)],[c_15,c_1942]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_2915,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) != sK4 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_1948,c_2486]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35124,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK4))) != sK4 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_35045,c_2915]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35137,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k3_xboole_0(k1_xboole_0,sK4)) != sK4 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_35124,c_1700]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35140,plain,
% 12.14/1.98      ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_35138,c_35137]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35149,plain,
% 12.14/1.98      ( sK4 != sK4 ),
% 12.14/1.98      inference(demodulation,[status(thm)],[c_35140,c_13]) ).
% 12.14/1.98  
% 12.14/1.98  cnf(c_35150,plain,
% 12.14/1.98      ( $false ),
% 12.14/1.98      inference(equality_resolution_simp,[status(thm)],[c_35149]) ).
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 12.14/1.98  
% 12.14/1.98  ------                               Statistics
% 12.14/1.98  
% 12.14/1.98  ------ General
% 12.14/1.98  
% 12.14/1.98  abstr_ref_over_cycles:                  0
% 12.14/1.98  abstr_ref_under_cycles:                 0
% 12.14/1.98  gc_basic_clause_elim:                   0
% 12.14/1.98  forced_gc_time:                         0
% 12.14/1.98  parsing_time:                           0.007
% 12.14/1.98  unif_index_cands_time:                  0.
% 12.14/1.98  unif_index_add_time:                    0.
% 12.14/1.98  orderings_time:                         0.
% 12.14/1.98  out_proof_time:                         0.023
% 12.14/1.98  total_time:                             1.462
% 12.14/1.98  num_of_symbols:                         44
% 12.14/1.98  num_of_terms:                           62773
% 12.14/1.98  
% 12.14/1.98  ------ Preprocessing
% 12.14/1.98  
% 12.14/1.98  num_of_splits:                          0
% 12.14/1.98  num_of_split_atoms:                     0
% 12.14/1.98  num_of_reused_defs:                     0
% 12.14/1.98  num_eq_ax_congr_red:                    12
% 12.14/1.98  num_of_sem_filtered_clauses:            1
% 12.14/1.98  num_of_subtypes:                        0
% 12.14/1.98  monotx_restored_types:                  0
% 12.14/1.98  sat_num_of_epr_types:                   0
% 12.14/1.98  sat_num_of_non_cyclic_types:            0
% 12.14/1.98  sat_guarded_non_collapsed_types:        0
% 12.14/1.98  num_pure_diseq_elim:                    0
% 12.14/1.98  simp_replaced_by:                       0
% 12.14/1.98  res_preprocessed:                       89
% 12.14/1.98  prep_upred:                             0
% 12.14/1.98  prep_unflattend:                        32
% 12.14/1.98  smt_new_axioms:                         0
% 12.14/1.98  pred_elim_cands:                        3
% 12.14/1.98  pred_elim:                              0
% 12.14/1.98  pred_elim_cl:                           0
% 12.14/1.98  pred_elim_cycles:                       2
% 12.14/1.98  merged_defs:                            12
% 12.14/1.98  merged_defs_ncl:                        0
% 12.14/1.98  bin_hyper_res:                          12
% 12.14/1.98  prep_cycles:                            3
% 12.14/1.98  pred_elim_time:                         0.003
% 12.14/1.98  splitting_time:                         0.
% 12.14/1.98  sem_filter_time:                        0.
% 12.14/1.98  monotx_time:                            0.
% 12.14/1.98  subtype_inf_time:                       0.
% 12.14/1.98  
% 12.14/1.98  ------ Problem properties
% 12.14/1.98  
% 12.14/1.98  clauses:                                24
% 12.14/1.98  conjectures:                            4
% 12.14/1.98  epr:                                    1
% 12.14/1.98  horn:                                   21
% 12.14/1.98  ground:                                 4
% 12.14/1.98  unary:                                  11
% 12.14/1.98  binary:                                 11
% 12.14/1.98  lits:                                   39
% 12.14/1.98  lits_eq:                                19
% 12.14/1.98  fd_pure:                                0
% 12.14/1.98  fd_pseudo:                              0
% 12.14/1.98  fd_cond:                                0
% 12.14/1.98  fd_pseudo_cond:                         1
% 12.14/1.98  ac_symbols:                             1
% 12.14/1.98  
% 12.14/1.98  ------ Propositional Solver
% 12.14/1.98  
% 12.14/1.98  prop_solver_calls:                      32
% 12.14/1.98  prop_fast_solver_calls:                 922
% 12.14/1.98  smt_solver_calls:                       0
% 12.14/1.98  smt_fast_solver_calls:                  0
% 12.14/1.98  prop_num_of_clauses:                    13840
% 12.14/1.98  prop_preprocess_simplified:             13535
% 12.14/1.98  prop_fo_subsumed:                       23
% 12.14/1.98  prop_solver_time:                       0.
% 12.14/1.98  smt_solver_time:                        0.
% 12.14/1.98  smt_fast_solver_time:                   0.
% 12.14/1.98  prop_fast_solver_time:                  0.
% 12.14/1.98  prop_unsat_core_time:                   0.
% 12.14/1.98  
% 12.14/1.98  ------ QBF
% 12.14/1.98  
% 12.14/1.98  qbf_q_res:                              0
% 12.14/1.98  qbf_num_tautologies:                    0
% 12.14/1.98  qbf_prep_cycles:                        0
% 12.14/1.98  
% 12.14/1.98  ------ BMC1
% 12.14/1.98  
% 12.14/1.98  bmc1_current_bound:                     -1
% 12.14/1.98  bmc1_last_solved_bound:                 -1
% 12.14/1.98  bmc1_unsat_core_size:                   -1
% 12.14/1.98  bmc1_unsat_core_parents_size:           -1
% 12.14/1.98  bmc1_merge_next_fun:                    0
% 12.14/1.98  bmc1_unsat_core_clauses_time:           0.
% 12.14/1.98  
% 12.14/1.98  ------ Instantiation
% 12.14/1.98  
% 12.14/1.98  inst_num_of_clauses:                    1930
% 12.14/1.98  inst_num_in_passive:                    1224
% 12.14/1.98  inst_num_in_active:                     683
% 12.14/1.98  inst_num_in_unprocessed:                23
% 12.14/1.98  inst_num_of_loops:                      940
% 12.14/1.98  inst_num_of_learning_restarts:          0
% 12.14/1.98  inst_num_moves_active_passive:          251
% 12.14/1.98  inst_lit_activity:                      0
% 12.14/1.98  inst_lit_activity_moves:                0
% 12.14/1.98  inst_num_tautologies:                   0
% 12.14/1.98  inst_num_prop_implied:                  0
% 12.14/1.98  inst_num_existing_simplified:           0
% 12.14/1.98  inst_num_eq_res_simplified:             0
% 12.14/1.98  inst_num_child_elim:                    0
% 12.14/1.98  inst_num_of_dismatching_blockings:      844
% 12.14/1.98  inst_num_of_non_proper_insts:           1946
% 12.14/1.98  inst_num_of_duplicates:                 0
% 12.14/1.98  inst_inst_num_from_inst_to_res:         0
% 12.14/1.98  inst_dismatching_checking_time:         0.
% 12.14/1.98  
% 12.14/1.98  ------ Resolution
% 12.14/1.98  
% 12.14/1.98  res_num_of_clauses:                     0
% 12.14/1.98  res_num_in_passive:                     0
% 12.14/1.98  res_num_in_active:                      0
% 12.14/1.98  res_num_of_loops:                       92
% 12.14/1.98  res_forward_subset_subsumed:            175
% 12.14/1.98  res_backward_subset_subsumed:           2
% 12.14/1.98  res_forward_subsumed:                   0
% 12.14/1.98  res_backward_subsumed:                  0
% 12.14/1.98  res_forward_subsumption_resolution:     0
% 12.14/1.98  res_backward_subsumption_resolution:    0
% 12.14/1.98  res_clause_to_clause_subsumption:       71430
% 12.14/1.98  res_orphan_elimination:                 0
% 12.14/1.98  res_tautology_del:                      155
% 12.14/1.98  res_num_eq_res_simplified:              0
% 12.14/1.98  res_num_sel_changes:                    0
% 12.14/1.98  res_moves_from_active_to_pass:          0
% 12.14/1.98  
% 12.14/1.98  ------ Superposition
% 12.14/1.98  
% 12.14/1.98  sup_time_total:                         0.
% 12.14/1.98  sup_time_generating:                    0.
% 12.14/1.98  sup_time_sim_full:                      0.
% 12.14/1.98  sup_time_sim_immed:                     0.
% 12.14/1.98  
% 12.14/1.98  sup_num_of_clauses:                     4207
% 12.14/1.98  sup_num_in_active:                      62
% 12.14/1.98  sup_num_in_passive:                     4145
% 12.14/1.98  sup_num_of_loops:                       187
% 12.14/1.98  sup_fw_superposition:                   6057
% 12.14/1.98  sup_bw_superposition:                   6951
% 12.14/1.98  sup_immediate_simplified:               7072
% 12.14/1.98  sup_given_eliminated:                   14
% 12.14/1.98  comparisons_done:                       0
% 12.14/1.98  comparisons_avoided:                    238
% 12.14/1.98  
% 12.14/1.98  ------ Simplifications
% 12.14/1.98  
% 12.14/1.98  
% 12.14/1.98  sim_fw_subset_subsumed:                 750
% 12.14/1.98  sim_bw_subset_subsumed:                 110
% 12.14/1.98  sim_fw_subsumed:                        1402
% 12.14/1.98  sim_bw_subsumed:                        245
% 12.14/1.98  sim_fw_subsumption_res:                 0
% 12.14/1.98  sim_bw_subsumption_res:                 0
% 12.14/1.98  sim_tautology_del:                      60
% 12.14/1.98  sim_eq_tautology_del:                   633
% 12.14/1.98  sim_eq_res_simp:                        4
% 12.14/1.98  sim_fw_demodulated:                     6243
% 12.14/1.98  sim_bw_demodulated:                     159
% 12.14/1.98  sim_light_normalised:                   517
% 12.14/1.98  sim_joinable_taut:                      146
% 12.14/1.98  sim_joinable_simp:                      0
% 12.14/1.98  sim_ac_normalised:                      0
% 12.14/1.98  sim_smt_subsumption:                    0
% 12.14/1.98  
%------------------------------------------------------------------------------
