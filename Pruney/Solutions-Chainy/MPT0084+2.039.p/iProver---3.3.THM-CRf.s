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
% DateTime   : Thu Dec  3 11:24:18 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  110 (1048 expanded)
%              Number of clauses        :   74 ( 308 expanded)
%              Number of leaves         :   14 ( 298 expanded)
%              Depth                    :   19
%              Number of atoms          :  167 (1512 expanded)
%              Number of equality atoms :  111 ( 955 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f32])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f36,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f27,f32,f32,f32,f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f33,f32,f32])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f35,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f34,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_88,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_88,c_12])).

cnf(c_155,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_154])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_705,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_155,c_10])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_714,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK0 ),
    inference(demodulation,[status(thm)],[c_705,c_9])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_421,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_6,c_11])).

cnf(c_1941,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_714,c_421])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_420,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_9])).

cnf(c_2020,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1941,c_9,c_10,c_11,c_420])).

cnf(c_733,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_420])).

cnf(c_2284,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_733,c_10])).

cnf(c_2321,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2284,c_9])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_414,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_419,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1455,plain,
    ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_414,c_419])).

cnf(c_1583,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_1455,c_11])).

cnf(c_1588,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_1583,c_9])).

cnf(c_1650,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_10,c_1588])).

cnf(c_1657,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1588,c_10])).

cnf(c_1677,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(demodulation,[status(thm)],[c_1650,c_1657])).

cnf(c_1678,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_1677,c_10,c_1657])).

cnf(c_2372,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_2321,c_1678])).

cnf(c_2399,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = sK0 ),
    inference(demodulation,[status(thm)],[c_2372,c_9,c_1455,c_1657])).

cnf(c_2633,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))) = sK0 ),
    inference(superposition,[status(thm)],[c_11,c_2399])).

cnf(c_3403,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))))) = sK0 ),
    inference(superposition,[status(thm)],[c_2020,c_2633])).

cnf(c_3406,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_2020,c_11])).

cnf(c_3660,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
    inference(demodulation,[status(thm)],[c_3406,c_11])).

cnf(c_3663,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))))) = sK0 ),
    inference(demodulation,[status(thm)],[c_3403,c_3660])).

cnf(c_720,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_155,c_11])).

cnf(c_747,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_720,c_11])).

cnf(c_976,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_747,c_10])).

cnf(c_1944,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)))) ),
    inference(superposition,[status(thm)],[c_976,c_421])).

cnf(c_977,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_976,c_747])).

cnf(c_2016,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1944,c_977])).

cnf(c_986,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_977,c_11])).

cnf(c_1714,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_986])).

cnf(c_1738,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1714,c_977])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_415,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1454,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_415,c_419])).

cnf(c_1739,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1738,c_1454])).

cnf(c_2017,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_2016,c_9,c_10,c_11,c_1739])).

cnf(c_2874,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_2633,c_421])).

cnf(c_2889,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_2874,c_9,c_10,c_11,c_420])).

cnf(c_3664,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_3663,c_10,c_2017,c_2889])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_442,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(sK0,sK1) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_1297,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k1_xboole_0),X0)
    | r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(sK0,sK1) != X0
    | sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1911,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0)
    | r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(sK0,sK1) != sK0
    | sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_1568,plain,
    ( r1_tarski(k4_xboole_0(sK0,X0),sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1570,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_804,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_245,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_478,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_520,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_599,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) != sK0
    | sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_244,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_496,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_430,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_86,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_159,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_86,c_14])).

cnf(c_160,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3664,c_1911,c_1570,c_804,c_599,c_496,c_430,c_160])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.96/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/1.01  
% 3.96/1.01  ------  iProver source info
% 3.96/1.01  
% 3.96/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.96/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/1.01  git: non_committed_changes: false
% 3.96/1.01  git: last_make_outside_of_git: false
% 3.96/1.01  
% 3.96/1.01  ------ 
% 3.96/1.01  
% 3.96/1.01  ------ Input Options
% 3.96/1.01  
% 3.96/1.01  --out_options                           all
% 3.96/1.01  --tptp_safe_out                         true
% 3.96/1.01  --problem_path                          ""
% 3.96/1.01  --include_path                          ""
% 3.96/1.01  --clausifier                            res/vclausify_rel
% 3.96/1.01  --clausifier_options                    ""
% 3.96/1.01  --stdin                                 false
% 3.96/1.01  --stats_out                             all
% 3.96/1.01  
% 3.96/1.01  ------ General Options
% 3.96/1.01  
% 3.96/1.01  --fof                                   false
% 3.96/1.01  --time_out_real                         305.
% 3.96/1.01  --time_out_virtual                      -1.
% 3.96/1.01  --symbol_type_check                     false
% 3.96/1.01  --clausify_out                          false
% 3.96/1.01  --sig_cnt_out                           false
% 3.96/1.01  --trig_cnt_out                          false
% 3.96/1.01  --trig_cnt_out_tolerance                1.
% 3.96/1.01  --trig_cnt_out_sk_spl                   false
% 3.96/1.01  --abstr_cl_out                          false
% 3.96/1.01  
% 3.96/1.01  ------ Global Options
% 3.96/1.01  
% 3.96/1.01  --schedule                              default
% 3.96/1.01  --add_important_lit                     false
% 3.96/1.01  --prop_solver_per_cl                    1000
% 3.96/1.01  --min_unsat_core                        false
% 3.96/1.01  --soft_assumptions                      false
% 3.96/1.01  --soft_lemma_size                       3
% 3.96/1.01  --prop_impl_unit_size                   0
% 3.96/1.01  --prop_impl_unit                        []
% 3.96/1.01  --share_sel_clauses                     true
% 3.96/1.01  --reset_solvers                         false
% 3.96/1.01  --bc_imp_inh                            [conj_cone]
% 3.96/1.01  --conj_cone_tolerance                   3.
% 3.96/1.01  --extra_neg_conj                        none
% 3.96/1.01  --large_theory_mode                     true
% 3.96/1.01  --prolific_symb_bound                   200
% 3.96/1.01  --lt_threshold                          2000
% 3.96/1.01  --clause_weak_htbl                      true
% 3.96/1.01  --gc_record_bc_elim                     false
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing Options
% 3.96/1.01  
% 3.96/1.01  --preprocessing_flag                    true
% 3.96/1.01  --time_out_prep_mult                    0.1
% 3.96/1.01  --splitting_mode                        input
% 3.96/1.01  --splitting_grd                         true
% 3.96/1.01  --splitting_cvd                         false
% 3.96/1.01  --splitting_cvd_svl                     false
% 3.96/1.01  --splitting_nvd                         32
% 3.96/1.01  --sub_typing                            true
% 3.96/1.01  --prep_gs_sim                           true
% 3.96/1.01  --prep_unflatten                        true
% 3.96/1.01  --prep_res_sim                          true
% 3.96/1.01  --prep_upred                            true
% 3.96/1.01  --prep_sem_filter                       exhaustive
% 3.96/1.01  --prep_sem_filter_out                   false
% 3.96/1.01  --pred_elim                             true
% 3.96/1.01  --res_sim_input                         true
% 3.96/1.01  --eq_ax_congr_red                       true
% 3.96/1.01  --pure_diseq_elim                       true
% 3.96/1.01  --brand_transform                       false
% 3.96/1.01  --non_eq_to_eq                          false
% 3.96/1.01  --prep_def_merge                        true
% 3.96/1.01  --prep_def_merge_prop_impl              false
% 3.96/1.01  --prep_def_merge_mbd                    true
% 3.96/1.01  --prep_def_merge_tr_red                 false
% 3.96/1.01  --prep_def_merge_tr_cl                  false
% 3.96/1.01  --smt_preprocessing                     true
% 3.96/1.01  --smt_ac_axioms                         fast
% 3.96/1.01  --preprocessed_out                      false
% 3.96/1.01  --preprocessed_stats                    false
% 3.96/1.01  
% 3.96/1.01  ------ Abstraction refinement Options
% 3.96/1.01  
% 3.96/1.01  --abstr_ref                             []
% 3.96/1.01  --abstr_ref_prep                        false
% 3.96/1.01  --abstr_ref_until_sat                   false
% 3.96/1.01  --abstr_ref_sig_restrict                funpre
% 3.96/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.01  --abstr_ref_under                       []
% 3.96/1.01  
% 3.96/1.01  ------ SAT Options
% 3.96/1.01  
% 3.96/1.01  --sat_mode                              false
% 3.96/1.01  --sat_fm_restart_options                ""
% 3.96/1.01  --sat_gr_def                            false
% 3.96/1.01  --sat_epr_types                         true
% 3.96/1.01  --sat_non_cyclic_types                  false
% 3.96/1.01  --sat_finite_models                     false
% 3.96/1.01  --sat_fm_lemmas                         false
% 3.96/1.01  --sat_fm_prep                           false
% 3.96/1.01  --sat_fm_uc_incr                        true
% 3.96/1.01  --sat_out_model                         small
% 3.96/1.01  --sat_out_clauses                       false
% 3.96/1.01  
% 3.96/1.01  ------ QBF Options
% 3.96/1.01  
% 3.96/1.01  --qbf_mode                              false
% 3.96/1.01  --qbf_elim_univ                         false
% 3.96/1.01  --qbf_dom_inst                          none
% 3.96/1.01  --qbf_dom_pre_inst                      false
% 3.96/1.01  --qbf_sk_in                             false
% 3.96/1.01  --qbf_pred_elim                         true
% 3.96/1.01  --qbf_split                             512
% 3.96/1.01  
% 3.96/1.01  ------ BMC1 Options
% 3.96/1.01  
% 3.96/1.01  --bmc1_incremental                      false
% 3.96/1.01  --bmc1_axioms                           reachable_all
% 3.96/1.01  --bmc1_min_bound                        0
% 3.96/1.01  --bmc1_max_bound                        -1
% 3.96/1.01  --bmc1_max_bound_default                -1
% 3.96/1.01  --bmc1_symbol_reachability              true
% 3.96/1.01  --bmc1_property_lemmas                  false
% 3.96/1.01  --bmc1_k_induction                      false
% 3.96/1.01  --bmc1_non_equiv_states                 false
% 3.96/1.01  --bmc1_deadlock                         false
% 3.96/1.01  --bmc1_ucm                              false
% 3.96/1.01  --bmc1_add_unsat_core                   none
% 3.96/1.01  --bmc1_unsat_core_children              false
% 3.96/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.01  --bmc1_out_stat                         full
% 3.96/1.01  --bmc1_ground_init                      false
% 3.96/1.01  --bmc1_pre_inst_next_state              false
% 3.96/1.01  --bmc1_pre_inst_state                   false
% 3.96/1.01  --bmc1_pre_inst_reach_state             false
% 3.96/1.01  --bmc1_out_unsat_core                   false
% 3.96/1.01  --bmc1_aig_witness_out                  false
% 3.96/1.01  --bmc1_verbose                          false
% 3.96/1.01  --bmc1_dump_clauses_tptp                false
% 3.96/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.01  --bmc1_dump_file                        -
% 3.96/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.01  --bmc1_ucm_extend_mode                  1
% 3.96/1.01  --bmc1_ucm_init_mode                    2
% 3.96/1.01  --bmc1_ucm_cone_mode                    none
% 3.96/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.01  --bmc1_ucm_relax_model                  4
% 3.96/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.01  --bmc1_ucm_layered_model                none
% 3.96/1.01  --bmc1_ucm_max_lemma_size               10
% 3.96/1.01  
% 3.96/1.01  ------ AIG Options
% 3.96/1.01  
% 3.96/1.01  --aig_mode                              false
% 3.96/1.01  
% 3.96/1.01  ------ Instantiation Options
% 3.96/1.01  
% 3.96/1.01  --instantiation_flag                    true
% 3.96/1.01  --inst_sos_flag                         true
% 3.96/1.01  --inst_sos_phase                        true
% 3.96/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel_side                     num_symb
% 3.96/1.01  --inst_solver_per_active                1400
% 3.96/1.01  --inst_solver_calls_frac                1.
% 3.96/1.01  --inst_passive_queue_type               priority_queues
% 3.96/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.01  --inst_passive_queues_freq              [25;2]
% 3.96/1.01  --inst_dismatching                      true
% 3.96/1.01  --inst_eager_unprocessed_to_passive     true
% 3.96/1.01  --inst_prop_sim_given                   true
% 3.96/1.01  --inst_prop_sim_new                     false
% 3.96/1.01  --inst_subs_new                         false
% 3.96/1.01  --inst_eq_res_simp                      false
% 3.96/1.01  --inst_subs_given                       false
% 3.96/1.01  --inst_orphan_elimination               true
% 3.96/1.01  --inst_learning_loop_flag               true
% 3.96/1.01  --inst_learning_start                   3000
% 3.96/1.01  --inst_learning_factor                  2
% 3.96/1.01  --inst_start_prop_sim_after_learn       3
% 3.96/1.01  --inst_sel_renew                        solver
% 3.96/1.01  --inst_lit_activity_flag                true
% 3.96/1.01  --inst_restr_to_given                   false
% 3.96/1.01  --inst_activity_threshold               500
% 3.96/1.01  --inst_out_proof                        true
% 3.96/1.01  
% 3.96/1.01  ------ Resolution Options
% 3.96/1.01  
% 3.96/1.01  --resolution_flag                       true
% 3.96/1.01  --res_lit_sel                           adaptive
% 3.96/1.01  --res_lit_sel_side                      none
% 3.96/1.01  --res_ordering                          kbo
% 3.96/1.01  --res_to_prop_solver                    active
% 3.96/1.01  --res_prop_simpl_new                    false
% 3.96/1.01  --res_prop_simpl_given                  true
% 3.96/1.01  --res_passive_queue_type                priority_queues
% 3.96/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.01  --res_passive_queues_freq               [15;5]
% 3.96/1.01  --res_forward_subs                      full
% 3.96/1.01  --res_backward_subs                     full
% 3.96/1.01  --res_forward_subs_resolution           true
% 3.96/1.01  --res_backward_subs_resolution          true
% 3.96/1.01  --res_orphan_elimination                true
% 3.96/1.01  --res_time_limit                        2.
% 3.96/1.01  --res_out_proof                         true
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Options
% 3.96/1.01  
% 3.96/1.01  --superposition_flag                    true
% 3.96/1.01  --sup_passive_queue_type                priority_queues
% 3.96/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.01  --demod_completeness_check              fast
% 3.96/1.01  --demod_use_ground                      true
% 3.96/1.01  --sup_to_prop_solver                    passive
% 3.96/1.01  --sup_prop_simpl_new                    true
% 3.96/1.01  --sup_prop_simpl_given                  true
% 3.96/1.01  --sup_fun_splitting                     true
% 3.96/1.01  --sup_smt_interval                      50000
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Simplification Setup
% 3.96/1.01  
% 3.96/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.96/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.96/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.96/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.96/1.01  --sup_immed_triv                        [TrivRules]
% 3.96/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_immed_bw_main                     []
% 3.96/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.96/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_input_bw                          []
% 3.96/1.01  
% 3.96/1.01  ------ Combination Options
% 3.96/1.01  
% 3.96/1.01  --comb_res_mult                         3
% 3.96/1.01  --comb_sup_mult                         2
% 3.96/1.01  --comb_inst_mult                        10
% 3.96/1.01  
% 3.96/1.01  ------ Debug Options
% 3.96/1.01  
% 3.96/1.01  --dbg_backtrace                         false
% 3.96/1.01  --dbg_dump_prop_clauses                 false
% 3.96/1.01  --dbg_dump_prop_clauses_file            -
% 3.96/1.01  --dbg_out_stat                          false
% 3.96/1.01  ------ Parsing...
% 3.96/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.01  ------ Proving...
% 3.96/1.01  ------ Problem Properties 
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  clauses                                 14
% 3.96/1.01  conjectures                             1
% 3.96/1.01  EPR                                     1
% 3.96/1.01  Horn                                    14
% 3.96/1.01  unary                                   10
% 3.96/1.01  binary                                  4
% 3.96/1.01  lits                                    18
% 3.96/1.01  lits eq                                 11
% 3.96/1.01  fd_pure                                 0
% 3.96/1.01  fd_pseudo                               0
% 3.96/1.01  fd_cond                                 0
% 3.96/1.01  fd_pseudo_cond                          0
% 3.96/1.01  AC symbols                              0
% 3.96/1.01  
% 3.96/1.01  ------ Schedule dynamic 5 is on 
% 3.96/1.01  
% 3.96/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  ------ 
% 3.96/1.01  Current options:
% 3.96/1.01  ------ 
% 3.96/1.01  
% 3.96/1.01  ------ Input Options
% 3.96/1.01  
% 3.96/1.01  --out_options                           all
% 3.96/1.01  --tptp_safe_out                         true
% 3.96/1.01  --problem_path                          ""
% 3.96/1.01  --include_path                          ""
% 3.96/1.01  --clausifier                            res/vclausify_rel
% 3.96/1.01  --clausifier_options                    ""
% 3.96/1.01  --stdin                                 false
% 3.96/1.01  --stats_out                             all
% 3.96/1.01  
% 3.96/1.01  ------ General Options
% 3.96/1.01  
% 3.96/1.01  --fof                                   false
% 3.96/1.01  --time_out_real                         305.
% 3.96/1.01  --time_out_virtual                      -1.
% 3.96/1.01  --symbol_type_check                     false
% 3.96/1.01  --clausify_out                          false
% 3.96/1.01  --sig_cnt_out                           false
% 3.96/1.01  --trig_cnt_out                          false
% 3.96/1.01  --trig_cnt_out_tolerance                1.
% 3.96/1.01  --trig_cnt_out_sk_spl                   false
% 3.96/1.01  --abstr_cl_out                          false
% 3.96/1.01  
% 3.96/1.01  ------ Global Options
% 3.96/1.01  
% 3.96/1.01  --schedule                              default
% 3.96/1.01  --add_important_lit                     false
% 3.96/1.01  --prop_solver_per_cl                    1000
% 3.96/1.01  --min_unsat_core                        false
% 3.96/1.01  --soft_assumptions                      false
% 3.96/1.01  --soft_lemma_size                       3
% 3.96/1.01  --prop_impl_unit_size                   0
% 3.96/1.01  --prop_impl_unit                        []
% 3.96/1.01  --share_sel_clauses                     true
% 3.96/1.01  --reset_solvers                         false
% 3.96/1.01  --bc_imp_inh                            [conj_cone]
% 3.96/1.01  --conj_cone_tolerance                   3.
% 3.96/1.01  --extra_neg_conj                        none
% 3.96/1.01  --large_theory_mode                     true
% 3.96/1.01  --prolific_symb_bound                   200
% 3.96/1.01  --lt_threshold                          2000
% 3.96/1.01  --clause_weak_htbl                      true
% 3.96/1.01  --gc_record_bc_elim                     false
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing Options
% 3.96/1.01  
% 3.96/1.01  --preprocessing_flag                    true
% 3.96/1.01  --time_out_prep_mult                    0.1
% 3.96/1.01  --splitting_mode                        input
% 3.96/1.01  --splitting_grd                         true
% 3.96/1.01  --splitting_cvd                         false
% 3.96/1.01  --splitting_cvd_svl                     false
% 3.96/1.01  --splitting_nvd                         32
% 3.96/1.01  --sub_typing                            true
% 3.96/1.01  --prep_gs_sim                           true
% 3.96/1.01  --prep_unflatten                        true
% 3.96/1.01  --prep_res_sim                          true
% 3.96/1.01  --prep_upred                            true
% 3.96/1.01  --prep_sem_filter                       exhaustive
% 3.96/1.01  --prep_sem_filter_out                   false
% 3.96/1.01  --pred_elim                             true
% 3.96/1.01  --res_sim_input                         true
% 3.96/1.01  --eq_ax_congr_red                       true
% 3.96/1.01  --pure_diseq_elim                       true
% 3.96/1.01  --brand_transform                       false
% 3.96/1.01  --non_eq_to_eq                          false
% 3.96/1.01  --prep_def_merge                        true
% 3.96/1.01  --prep_def_merge_prop_impl              false
% 3.96/1.01  --prep_def_merge_mbd                    true
% 3.96/1.01  --prep_def_merge_tr_red                 false
% 3.96/1.01  --prep_def_merge_tr_cl                  false
% 3.96/1.01  --smt_preprocessing                     true
% 3.96/1.01  --smt_ac_axioms                         fast
% 3.96/1.01  --preprocessed_out                      false
% 3.96/1.01  --preprocessed_stats                    false
% 3.96/1.01  
% 3.96/1.01  ------ Abstraction refinement Options
% 3.96/1.01  
% 3.96/1.01  --abstr_ref                             []
% 3.96/1.01  --abstr_ref_prep                        false
% 3.96/1.01  --abstr_ref_until_sat                   false
% 3.96/1.01  --abstr_ref_sig_restrict                funpre
% 3.96/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.01  --abstr_ref_under                       []
% 3.96/1.01  
% 3.96/1.01  ------ SAT Options
% 3.96/1.01  
% 3.96/1.01  --sat_mode                              false
% 3.96/1.01  --sat_fm_restart_options                ""
% 3.96/1.01  --sat_gr_def                            false
% 3.96/1.01  --sat_epr_types                         true
% 3.96/1.01  --sat_non_cyclic_types                  false
% 3.96/1.01  --sat_finite_models                     false
% 3.96/1.01  --sat_fm_lemmas                         false
% 3.96/1.01  --sat_fm_prep                           false
% 3.96/1.01  --sat_fm_uc_incr                        true
% 3.96/1.01  --sat_out_model                         small
% 3.96/1.01  --sat_out_clauses                       false
% 3.96/1.01  
% 3.96/1.01  ------ QBF Options
% 3.96/1.01  
% 3.96/1.01  --qbf_mode                              false
% 3.96/1.01  --qbf_elim_univ                         false
% 3.96/1.01  --qbf_dom_inst                          none
% 3.96/1.01  --qbf_dom_pre_inst                      false
% 3.96/1.01  --qbf_sk_in                             false
% 3.96/1.01  --qbf_pred_elim                         true
% 3.96/1.01  --qbf_split                             512
% 3.96/1.01  
% 3.96/1.01  ------ BMC1 Options
% 3.96/1.01  
% 3.96/1.01  --bmc1_incremental                      false
% 3.96/1.01  --bmc1_axioms                           reachable_all
% 3.96/1.01  --bmc1_min_bound                        0
% 3.96/1.01  --bmc1_max_bound                        -1
% 3.96/1.01  --bmc1_max_bound_default                -1
% 3.96/1.01  --bmc1_symbol_reachability              true
% 3.96/1.01  --bmc1_property_lemmas                  false
% 3.96/1.01  --bmc1_k_induction                      false
% 3.96/1.01  --bmc1_non_equiv_states                 false
% 3.96/1.01  --bmc1_deadlock                         false
% 3.96/1.01  --bmc1_ucm                              false
% 3.96/1.01  --bmc1_add_unsat_core                   none
% 3.96/1.01  --bmc1_unsat_core_children              false
% 3.96/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.01  --bmc1_out_stat                         full
% 3.96/1.01  --bmc1_ground_init                      false
% 3.96/1.01  --bmc1_pre_inst_next_state              false
% 3.96/1.01  --bmc1_pre_inst_state                   false
% 3.96/1.01  --bmc1_pre_inst_reach_state             false
% 3.96/1.01  --bmc1_out_unsat_core                   false
% 3.96/1.01  --bmc1_aig_witness_out                  false
% 3.96/1.01  --bmc1_verbose                          false
% 3.96/1.01  --bmc1_dump_clauses_tptp                false
% 3.96/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.01  --bmc1_dump_file                        -
% 3.96/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.01  --bmc1_ucm_extend_mode                  1
% 3.96/1.01  --bmc1_ucm_init_mode                    2
% 3.96/1.01  --bmc1_ucm_cone_mode                    none
% 3.96/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.01  --bmc1_ucm_relax_model                  4
% 3.96/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.01  --bmc1_ucm_layered_model                none
% 3.96/1.01  --bmc1_ucm_max_lemma_size               10
% 3.96/1.01  
% 3.96/1.01  ------ AIG Options
% 3.96/1.01  
% 3.96/1.01  --aig_mode                              false
% 3.96/1.01  
% 3.96/1.01  ------ Instantiation Options
% 3.96/1.01  
% 3.96/1.01  --instantiation_flag                    true
% 3.96/1.01  --inst_sos_flag                         true
% 3.96/1.01  --inst_sos_phase                        true
% 3.96/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel_side                     none
% 3.96/1.01  --inst_solver_per_active                1400
% 3.96/1.01  --inst_solver_calls_frac                1.
% 3.96/1.01  --inst_passive_queue_type               priority_queues
% 3.96/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.01  --inst_passive_queues_freq              [25;2]
% 3.96/1.01  --inst_dismatching                      true
% 3.96/1.01  --inst_eager_unprocessed_to_passive     true
% 3.96/1.01  --inst_prop_sim_given                   true
% 3.96/1.01  --inst_prop_sim_new                     false
% 3.96/1.01  --inst_subs_new                         false
% 3.96/1.01  --inst_eq_res_simp                      false
% 3.96/1.01  --inst_subs_given                       false
% 3.96/1.01  --inst_orphan_elimination               true
% 3.96/1.01  --inst_learning_loop_flag               true
% 3.96/1.01  --inst_learning_start                   3000
% 3.96/1.01  --inst_learning_factor                  2
% 3.96/1.01  --inst_start_prop_sim_after_learn       3
% 3.96/1.01  --inst_sel_renew                        solver
% 3.96/1.01  --inst_lit_activity_flag                true
% 3.96/1.01  --inst_restr_to_given                   false
% 3.96/1.01  --inst_activity_threshold               500
% 3.96/1.01  --inst_out_proof                        true
% 3.96/1.01  
% 3.96/1.01  ------ Resolution Options
% 3.96/1.01  
% 3.96/1.01  --resolution_flag                       false
% 3.96/1.01  --res_lit_sel                           adaptive
% 3.96/1.01  --res_lit_sel_side                      none
% 3.96/1.01  --res_ordering                          kbo
% 3.96/1.01  --res_to_prop_solver                    active
% 3.96/1.01  --res_prop_simpl_new                    false
% 3.96/1.01  --res_prop_simpl_given                  true
% 3.96/1.01  --res_passive_queue_type                priority_queues
% 3.96/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.01  --res_passive_queues_freq               [15;5]
% 3.96/1.01  --res_forward_subs                      full
% 3.96/1.01  --res_backward_subs                     full
% 3.96/1.01  --res_forward_subs_resolution           true
% 3.96/1.01  --res_backward_subs_resolution          true
% 3.96/1.01  --res_orphan_elimination                true
% 3.96/1.01  --res_time_limit                        2.
% 3.96/1.01  --res_out_proof                         true
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Options
% 3.96/1.01  
% 3.96/1.01  --superposition_flag                    true
% 3.96/1.01  --sup_passive_queue_type                priority_queues
% 3.96/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.01  --demod_completeness_check              fast
% 3.96/1.01  --demod_use_ground                      true
% 3.96/1.01  --sup_to_prop_solver                    passive
% 3.96/1.01  --sup_prop_simpl_new                    true
% 3.96/1.01  --sup_prop_simpl_given                  true
% 3.96/1.01  --sup_fun_splitting                     true
% 3.96/1.01  --sup_smt_interval                      50000
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Simplification Setup
% 3.96/1.01  
% 3.96/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.96/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.96/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.96/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.96/1.01  --sup_immed_triv                        [TrivRules]
% 3.96/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_immed_bw_main                     []
% 3.96/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.96/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_input_bw                          []
% 3.96/1.01  
% 3.96/1.01  ------ Combination Options
% 3.96/1.01  
% 3.96/1.01  --comb_res_mult                         3
% 3.96/1.01  --comb_sup_mult                         2
% 3.96/1.01  --comb_inst_mult                        10
% 3.96/1.01  
% 3.96/1.01  ------ Debug Options
% 3.96/1.01  
% 3.96/1.01  --dbg_backtrace                         false
% 3.96/1.01  --dbg_dump_prop_clauses                 false
% 3.96/1.01  --dbg_dump_prop_clauses_file            -
% 3.96/1.01  --dbg_out_stat                          false
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  ------ Proving...
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  % SZS status Theorem for theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  fof(f1,axiom,(
% 3.96/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f17,plain,(
% 3.96/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.96/1.01    inference(nnf_transformation,[],[f1])).
% 3.96/1.01  
% 3.96/1.01  fof(f21,plain,(
% 3.96/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f17])).
% 3.96/1.01  
% 3.96/1.01  fof(f10,axiom,(
% 3.96/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f32,plain,(
% 3.96/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f10])).
% 3.96/1.01  
% 3.96/1.01  fof(f38,plain,(
% 3.96/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.96/1.01    inference(definition_unfolding,[],[f21,f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f12,conjecture,(
% 3.96/1.01    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f13,negated_conjecture,(
% 3.96/1.01    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 3.96/1.01    inference(negated_conjecture,[],[f12])).
% 3.96/1.01  
% 3.96/1.01  fof(f16,plain,(
% 3.96/1.01    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 3.96/1.01    inference(ennf_transformation,[],[f13])).
% 3.96/1.01  
% 3.96/1.01  fof(f19,plain,(
% 3.96/1.01    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 3.96/1.01    introduced(choice_axiom,[])).
% 3.96/1.01  
% 3.96/1.01  fof(f20,plain,(
% 3.96/1.01    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 3.96/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 3.96/1.01  
% 3.96/1.01  fof(f36,plain,(
% 3.96/1.01    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 3.96/1.01    inference(cnf_transformation,[],[f20])).
% 3.96/1.01  
% 3.96/1.01  fof(f43,plain,(
% 3.96/1.01    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 3.96/1.01    inference(definition_unfolding,[],[f36,f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f9,axiom,(
% 3.96/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f31,plain,(
% 3.96/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f9])).
% 3.96/1.01  
% 3.96/1.01  fof(f41,plain,(
% 3.96/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.96/1.01    inference(definition_unfolding,[],[f31,f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f8,axiom,(
% 3.96/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f30,plain,(
% 3.96/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.96/1.01    inference(cnf_transformation,[],[f8])).
% 3.96/1.01  
% 3.96/1.01  fof(f5,axiom,(
% 3.96/1.01    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f27,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f5])).
% 3.96/1.01  
% 3.96/1.01  fof(f39,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 3.96/1.01    inference(definition_unfolding,[],[f27,f32,f32,f32,f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f11,axiom,(
% 3.96/1.01    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f33,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f11])).
% 3.96/1.01  
% 3.96/1.01  fof(f42,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.96/1.01    inference(definition_unfolding,[],[f33,f32,f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f6,axiom,(
% 3.96/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f28,plain,(
% 3.96/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.96/1.01    inference(cnf_transformation,[],[f6])).
% 3.96/1.01  
% 3.96/1.01  fof(f40,plain,(
% 3.96/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.96/1.01    inference(definition_unfolding,[],[f28,f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f35,plain,(
% 3.96/1.01    r1_tarski(sK0,sK2)),
% 3.96/1.01    inference(cnf_transformation,[],[f20])).
% 3.96/1.01  
% 3.96/1.01  fof(f2,axiom,(
% 3.96/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f18,plain,(
% 3.96/1.01    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.96/1.01    inference(nnf_transformation,[],[f2])).
% 3.96/1.01  
% 3.96/1.01  fof(f24,plain,(
% 3.96/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f18])).
% 3.96/1.01  
% 3.96/1.01  fof(f7,axiom,(
% 3.96/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.96/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f29,plain,(
% 3.96/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f7])).
% 3.96/1.01  
% 3.96/1.01  fof(f22,plain,(
% 3.96/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.96/1.01    inference(cnf_transformation,[],[f17])).
% 3.96/1.01  
% 3.96/1.01  fof(f37,plain,(
% 3.96/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.96/1.01    inference(definition_unfolding,[],[f22,f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f34,plain,(
% 3.96/1.01    ~r1_xboole_0(sK0,sK1)),
% 3.96/1.01    inference(cnf_transformation,[],[f20])).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1,plain,
% 3.96/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.96/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_88,plain,
% 3.96/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.96/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.96/1.01      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_12,negated_conjecture,
% 3.96/1.01      ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 3.96/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_154,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.96/1.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
% 3.96/1.01      | sK0 != X0 ),
% 3.96/1.01      inference(resolution_lifted,[status(thm)],[c_88,c_12]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_155,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 3.96/1.01      inference(unflattening,[status(thm)],[c_154]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.96/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_705,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_155,c_10]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_9,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_714,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK0 ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_705,c_9]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_6,plain,
% 3.96/1.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.96/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 3.96/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_421,plain,
% 3.96/1.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_6,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1941,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK0)) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_714,c_421]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_420,plain,
% 3.96/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_7,c_9]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2020,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_1941,c_9,c_10,c_11,c_420]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_733,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_11,c_420]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2284,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_733,c_10]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2321,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_2284,c_9]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_13,negated_conjecture,
% 3.96/1.01      ( r1_tarski(sK0,sK2) ),
% 3.96/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_414,plain,
% 3.96/1.01      ( r1_tarski(sK0,sK2) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2,plain,
% 3.96/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f24]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_419,plain,
% 3.96/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.96/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1455,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_414,c_419]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1583,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_1455,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1588,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_1583,c_9]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1650,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_10,c_1588]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1657,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_1588,c_10]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1677,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_1650,c_1657]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1678,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_1677,c_10,c_1657]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2372,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_2321,c_1678]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2399,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = sK0 ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_2372,c_9,c_1455,c_1657]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2633,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))) = sK0 ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_11,c_2399]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3403,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))))) = sK0 ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_2020,c_2633]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3406,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_2020,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3660,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_3406,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3663,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))))) = sK0 ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_3403,c_3660]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_720,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_155,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_747,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0))))) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_720,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_976,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_747,c_10]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1944,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)))) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_976,c_421]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_977,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_976,c_747]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2016,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k1_xboole_0,X0)) ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_1944,c_977]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_986,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_977,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1714,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_9,c_986]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1738,plain,
% 3.96/1.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_1714,c_977]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_8,plain,
% 3.96/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_415,plain,
% 3.96/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1454,plain,
% 3.96/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_415,c_419]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1739,plain,
% 3.96/1.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_1738,c_1454]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2017,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_2016,c_9,c_10,c_11,c_1739]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2874,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,sK0)) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_2633,c_421]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_2889,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_2874,c_9,c_10,c_11,c_420]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3664,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_3663,c_10,c_2017,c_2889]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_247,plain,
% 3.96/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.96/1.01      theory(equality) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_442,plain,
% 3.96/1.01      ( ~ r1_tarski(X0,X1)
% 3.96/1.01      | r1_tarski(sK0,k4_xboole_0(sK0,sK1))
% 3.96/1.01      | k4_xboole_0(sK0,sK1) != X1
% 3.96/1.01      | sK0 != X0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_247]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1297,plain,
% 3.96/1.01      ( ~ r1_tarski(k4_xboole_0(sK0,k1_xboole_0),X0)
% 3.96/1.01      | r1_tarski(sK0,k4_xboole_0(sK0,sK1))
% 3.96/1.01      | k4_xboole_0(sK0,sK1) != X0
% 3.96/1.01      | sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_442]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1911,plain,
% 3.96/1.01      ( ~ r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0)
% 3.96/1.01      | r1_tarski(sK0,k4_xboole_0(sK0,sK1))
% 3.96/1.01      | k4_xboole_0(sK0,sK1) != sK0
% 3.96/1.01      | sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_1297]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1568,plain,
% 3.96/1.01      ( r1_tarski(k4_xboole_0(sK0,X0),sK0) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1570,plain,
% 3.96/1.01      ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_1568]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_804,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_245,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_478,plain,
% 3.96/1.01      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_245]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_520,plain,
% 3.96/1.01      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_478]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_599,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k1_xboole_0) != sK0
% 3.96/1.01      | sK0 = k4_xboole_0(sK0,k1_xboole_0)
% 3.96/1.01      | sK0 != sK0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_520]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_244,plain,( X0 = X0 ),theory(equality) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_496,plain,
% 3.96/1.01      ( sK0 = sK0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_244]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_430,plain,
% 3.96/1.01      ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK1))
% 3.96/1.01      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_0,plain,
% 3.96/1.01      ( r1_xboole_0(X0,X1)
% 3.96/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_86,plain,
% 3.96/1.01      ( r1_xboole_0(X0,X1)
% 3.96/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.96/1.01      inference(prop_impl,[status(thm)],[c_0]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_14,negated_conjecture,
% 3.96/1.01      ( ~ r1_xboole_0(sK0,sK1) ),
% 3.96/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_159,plain,
% 3.96/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.96/1.01      | sK1 != X1
% 3.96/1.01      | sK0 != X0 ),
% 3.96/1.01      inference(resolution_lifted,[status(thm)],[c_86,c_14]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_160,plain,
% 3.96/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 3.96/1.01      inference(unflattening,[status(thm)],[c_159]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(contradiction,plain,
% 3.96/1.01      ( $false ),
% 3.96/1.01      inference(minisat,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_3664,c_1911,c_1570,c_804,c_599,c_496,c_430,c_160]) ).
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  ------                               Statistics
% 3.96/1.01  
% 3.96/1.01  ------ General
% 3.96/1.01  
% 3.96/1.01  abstr_ref_over_cycles:                  0
% 3.96/1.01  abstr_ref_under_cycles:                 0
% 3.96/1.01  gc_basic_clause_elim:                   0
% 3.96/1.01  forced_gc_time:                         0
% 3.96/1.01  parsing_time:                           0.009
% 3.96/1.01  unif_index_cands_time:                  0.
% 3.96/1.01  unif_index_add_time:                    0.
% 3.96/1.01  orderings_time:                         0.
% 3.96/1.01  out_proof_time:                         0.024
% 3.96/1.01  total_time:                             0.204
% 3.96/1.01  num_of_symbols:                         39
% 3.96/1.01  num_of_terms:                           5696
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing
% 3.96/1.01  
% 3.96/1.01  num_of_splits:                          0
% 3.96/1.01  num_of_split_atoms:                     0
% 3.96/1.01  num_of_reused_defs:                     0
% 3.96/1.01  num_eq_ax_congr_red:                    6
% 3.96/1.01  num_of_sem_filtered_clauses:            1
% 3.96/1.01  num_of_subtypes:                        0
% 3.96/1.01  monotx_restored_types:                  0
% 3.96/1.01  sat_num_of_epr_types:                   0
% 3.96/1.01  sat_num_of_non_cyclic_types:            0
% 3.96/1.01  sat_guarded_non_collapsed_types:        0
% 3.96/1.01  num_pure_diseq_elim:                    0
% 3.96/1.01  simp_replaced_by:                       0
% 3.96/1.01  res_preprocessed:                       66
% 3.96/1.01  prep_upred:                             0
% 3.96/1.01  prep_unflattend:                        4
% 3.96/1.01  smt_new_axioms:                         0
% 3.96/1.01  pred_elim_cands:                        1
% 3.96/1.01  pred_elim:                              1
% 3.96/1.01  pred_elim_cl:                           1
% 3.96/1.01  pred_elim_cycles:                       3
% 3.96/1.01  merged_defs:                            10
% 3.96/1.01  merged_defs_ncl:                        0
% 3.96/1.01  bin_hyper_res:                          10
% 3.96/1.01  prep_cycles:                            4
% 3.96/1.01  pred_elim_time:                         0.
% 3.96/1.01  splitting_time:                         0.
% 3.96/1.01  sem_filter_time:                        0.
% 3.96/1.01  monotx_time:                            0.
% 3.96/1.01  subtype_inf_time:                       0.
% 3.96/1.01  
% 3.96/1.01  ------ Problem properties
% 3.96/1.01  
% 3.96/1.01  clauses:                                14
% 3.96/1.01  conjectures:                            1
% 3.96/1.01  epr:                                    1
% 3.96/1.01  horn:                                   14
% 3.96/1.01  ground:                                 4
% 3.96/1.01  unary:                                  10
% 3.96/1.01  binary:                                 4
% 3.96/1.01  lits:                                   18
% 3.96/1.01  lits_eq:                                11
% 3.96/1.01  fd_pure:                                0
% 3.96/1.01  fd_pseudo:                              0
% 3.96/1.01  fd_cond:                                0
% 3.96/1.01  fd_pseudo_cond:                         0
% 3.96/1.01  ac_symbols:                             0
% 3.96/1.01  
% 3.96/1.01  ------ Propositional Solver
% 3.96/1.01  
% 3.96/1.01  prop_solver_calls:                      33
% 3.96/1.01  prop_fast_solver_calls:                 259
% 3.96/1.01  smt_solver_calls:                       0
% 3.96/1.01  smt_fast_solver_calls:                  0
% 3.96/1.01  prop_num_of_clauses:                    1239
% 3.96/1.01  prop_preprocess_simplified:             3167
% 3.96/1.01  prop_fo_subsumed:                       1
% 3.96/1.01  prop_solver_time:                       0.
% 3.96/1.01  smt_solver_time:                        0.
% 3.96/1.01  smt_fast_solver_time:                   0.
% 3.96/1.01  prop_fast_solver_time:                  0.
% 3.96/1.01  prop_unsat_core_time:                   0.
% 3.96/1.01  
% 3.96/1.01  ------ QBF
% 3.96/1.01  
% 3.96/1.01  qbf_q_res:                              0
% 3.96/1.01  qbf_num_tautologies:                    0
% 3.96/1.01  qbf_prep_cycles:                        0
% 3.96/1.01  
% 3.96/1.01  ------ BMC1
% 3.96/1.01  
% 3.96/1.01  bmc1_current_bound:                     -1
% 3.96/1.01  bmc1_last_solved_bound:                 -1
% 3.96/1.01  bmc1_unsat_core_size:                   -1
% 3.96/1.01  bmc1_unsat_core_parents_size:           -1
% 3.96/1.01  bmc1_merge_next_fun:                    0
% 3.96/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.96/1.01  
% 3.96/1.01  ------ Instantiation
% 3.96/1.01  
% 3.96/1.01  inst_num_of_clauses:                    489
% 3.96/1.02  inst_num_in_passive:                    275
% 3.96/1.02  inst_num_in_active:                     213
% 3.96/1.02  inst_num_in_unprocessed:                1
% 3.96/1.02  inst_num_of_loops:                      230
% 3.96/1.02  inst_num_of_learning_restarts:          0
% 3.96/1.02  inst_num_moves_active_passive:          12
% 3.96/1.02  inst_lit_activity:                      0
% 3.96/1.02  inst_lit_activity_moves:                0
% 3.96/1.02  inst_num_tautologies:                   0
% 3.96/1.02  inst_num_prop_implied:                  0
% 3.96/1.02  inst_num_existing_simplified:           0
% 3.96/1.02  inst_num_eq_res_simplified:             0
% 3.96/1.02  inst_num_child_elim:                    0
% 3.96/1.02  inst_num_of_dismatching_blockings:      136
% 3.96/1.02  inst_num_of_non_proper_insts:           462
% 3.96/1.02  inst_num_of_duplicates:                 0
% 3.96/1.02  inst_inst_num_from_inst_to_res:         0
% 3.96/1.02  inst_dismatching_checking_time:         0.
% 3.96/1.02  
% 3.96/1.02  ------ Resolution
% 3.96/1.02  
% 3.96/1.02  res_num_of_clauses:                     0
% 3.96/1.02  res_num_in_passive:                     0
% 3.96/1.02  res_num_in_active:                      0
% 3.96/1.02  res_num_of_loops:                       70
% 3.96/1.02  res_forward_subset_subsumed:            108
% 3.96/1.02  res_backward_subset_subsumed:           0
% 3.96/1.02  res_forward_subsumed:                   0
% 3.96/1.02  res_backward_subsumed:                  0
% 3.96/1.02  res_forward_subsumption_resolution:     0
% 3.96/1.02  res_backward_subsumption_resolution:    0
% 3.96/1.02  res_clause_to_clause_subsumption:       732
% 3.96/1.02  res_orphan_elimination:                 0
% 3.96/1.02  res_tautology_del:                      70
% 3.96/1.02  res_num_eq_res_simplified:              1
% 3.96/1.02  res_num_sel_changes:                    0
% 3.96/1.02  res_moves_from_active_to_pass:          0
% 3.96/1.02  
% 3.96/1.02  ------ Superposition
% 3.96/1.02  
% 3.96/1.02  sup_time_total:                         0.
% 3.96/1.02  sup_time_generating:                    0.
% 3.96/1.02  sup_time_sim_full:                      0.
% 3.96/1.02  sup_time_sim_immed:                     0.
% 3.96/1.02  
% 3.96/1.02  sup_num_of_clauses:                     105
% 3.96/1.02  sup_num_in_active:                      34
% 3.96/1.02  sup_num_in_passive:                     71
% 3.96/1.02  sup_num_of_loops:                       45
% 3.96/1.02  sup_fw_superposition:                   296
% 3.96/1.02  sup_bw_superposition:                   260
% 3.96/1.02  sup_immediate_simplified:               469
% 3.96/1.02  sup_given_eliminated:                   9
% 3.96/1.02  comparisons_done:                       0
% 3.96/1.02  comparisons_avoided:                    0
% 3.96/1.02  
% 3.96/1.02  ------ Simplifications
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  sim_fw_subset_subsumed:                 1
% 3.96/1.02  sim_bw_subset_subsumed:                 0
% 3.96/1.02  sim_fw_subsumed:                        57
% 3.96/1.02  sim_bw_subsumed:                        4
% 3.96/1.02  sim_fw_subsumption_res:                 0
% 3.96/1.02  sim_bw_subsumption_res:                 0
% 3.96/1.02  sim_tautology_del:                      0
% 3.96/1.02  sim_eq_tautology_del:                   262
% 3.96/1.02  sim_eq_res_simp:                        0
% 3.96/1.02  sim_fw_demodulated:                     509
% 3.96/1.02  sim_bw_demodulated:                     18
% 3.96/1.02  sim_light_normalised:                   206
% 3.96/1.02  sim_joinable_taut:                      0
% 3.96/1.02  sim_joinable_simp:                      0
% 3.96/1.02  sim_ac_normalised:                      0
% 3.96/1.02  sim_smt_subsumption:                    0
% 3.96/1.02  
%------------------------------------------------------------------------------
