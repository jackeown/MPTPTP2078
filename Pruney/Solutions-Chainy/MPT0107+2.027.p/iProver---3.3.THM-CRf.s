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
% DateTime   : Thu Dec  3 11:25:22 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  169 (50162 expanded)
%              Number of clauses        :  145 (18063 expanded)
%              Number of leaves         :    9 (14436 expanded)
%              Depth                    :   31
%              Number of atoms          :  170 (50163 expanded)
%              Number of equality atoms :  169 (50162 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f30,f30])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f9,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17])).

fof(f32,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(definition_unfolding,[],[f32,f26,f30])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_420,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_363,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_448,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[status(thm)],[c_420,c_363])).

cnf(c_449,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_448,c_420])).

cnf(c_1203,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_449,c_1])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_495,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_510,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_495,c_8])).

cnf(c_623,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_420,c_510])).

cnf(c_629,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_623,c_449])).

cnf(c_1211,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1203,c_629])).

cnf(c_1212,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1211,c_420,c_510])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_190,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_0,c_9])).

cnf(c_7398,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1212,c_190])).

cnf(c_7414,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7398,c_8,c_1212])).

cnf(c_422,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_363,c_9])).

cnf(c_1746,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_422,c_9])).

cnf(c_489,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_737,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_489])).

cnf(c_765,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_737,c_489])).

cnf(c_766,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_765,c_9])).

cnf(c_492,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_363,c_10])).

cnf(c_748,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_492,c_489])).

cnf(c_429,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_760,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_748,c_9,c_429])).

cnf(c_3596,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_363,c_760])).

cnf(c_4113,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_766,c_3596])).

cnf(c_4551,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1746,c_4113])).

cnf(c_7564,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_7414,c_4551])).

cnf(c_423,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_363,c_9])).

cnf(c_2004,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_363,c_423])).

cnf(c_742,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_363,c_489])).

cnf(c_761,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_742,c_492])).

cnf(c_762,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_761,c_9,c_429])).

cnf(c_624,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_510,c_9])).

cnf(c_1417,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_762,c_624])).

cnf(c_1420,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1417,c_9])).

cnf(c_2075,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2004,c_492,c_1420])).

cnf(c_7853,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_7564,c_2075])).

cnf(c_1416,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_762,c_9])).

cnf(c_7909,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7853,c_1416])).

cnf(c_7375,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4551,c_190])).

cnf(c_7448,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7375,c_7414])).

cnf(c_480,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_429,c_363])).

cnf(c_481,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_480,c_429])).

cnf(c_1285,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_481,c_1])).

cnf(c_622,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_429,c_510])).

cnf(c_630,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_622,c_481])).

cnf(c_1290,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0))) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1285,c_630])).

cnf(c_1291,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1290,c_429,c_510])).

cnf(c_7449,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7448,c_510,c_1291])).

cnf(c_7395,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4113,c_190])).

cnf(c_7417,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7395,c_510])).

cnf(c_4303,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4113,c_423])).

cnf(c_7875,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7564,c_4303])).

cnf(c_7878,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7564,c_2075])).

cnf(c_7886,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7564,c_363])).

cnf(c_7896,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_7875,c_7878,c_7886])).

cnf(c_8660,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7449,c_7417,c_7449,c_7896])).

cnf(c_8664,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8660,c_190])).

cnf(c_32900,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7909,c_8664])).

cnf(c_7836,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7564,c_760])).

cnf(c_7844,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_7564,c_510])).

cnf(c_7921,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_7836,c_7844,c_7909])).

cnf(c_7388,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1746,c_190])).

cnf(c_7428,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_7388,c_7414])).

cnf(c_7429,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7428,c_510])).

cnf(c_8662,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_8660,c_7429])).

cnf(c_8825,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_492,c_8662])).

cnf(c_33105,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_32900,c_7921,c_8825])).

cnf(c_418,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_33905,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_33105,c_418])).

cnf(c_9753,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X1)) ),
    inference(superposition,[status(thm)],[c_418,c_766])).

cnf(c_501,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_505,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_501,c_9])).

cnf(c_14450,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8660,c_505])).

cnf(c_14682,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_14450,c_10])).

cnf(c_14730,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_14682])).

cnf(c_15366,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_14730,c_418])).

cnf(c_9648,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_418])).

cnf(c_15398,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_15366,c_9,c_9648])).

cnf(c_427,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_431,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_427,c_9])).

cnf(c_13895,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_766,c_431])).

cnf(c_426,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_14019,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_431,c_426])).

cnf(c_14120,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) ),
    inference(demodulation,[status(thm)],[c_13895,c_14019])).

cnf(c_626,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_510,c_9])).

cnf(c_628,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_626,c_9])).

cnf(c_14121,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_14120,c_628])).

cnf(c_15399,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_15398,c_9,c_14121])).

cnf(c_29895,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_15399,c_426])).

cnf(c_4093,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_766,c_9])).

cnf(c_9698,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X1)) ),
    inference(superposition,[status(thm)],[c_418,c_4093])).

cnf(c_29976,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_29895,c_9,c_9698,c_14019])).

cnf(c_7828,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7564,c_9])).

cnf(c_29977,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_29976,c_7828,c_14730])).

cnf(c_32892,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_8664])).

cnf(c_33109,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_32892,c_9])).

cnf(c_33110,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_33109,c_14730])).

cnf(c_33944,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_33905,c_9753,c_29977,c_33110])).

cnf(c_15286,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_14730])).

cnf(c_15463,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_15286,c_489])).

cnf(c_4059,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_766])).

cnf(c_4156,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X0)) ),
    inference(demodulation,[status(thm)],[c_4059,c_766])).

cnf(c_425,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_9,c_9])).

cnf(c_432,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_425,c_9])).

cnf(c_4157,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(demodulation,[status(thm)],[c_4156,c_9,c_432])).

cnf(c_15464,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_15463,c_9,c_4157])).

cnf(c_30355,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_10,c_15464])).

cnf(c_30366,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_431,c_15464])).

cnf(c_30367,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_426,c_15464])).

cnf(c_30619,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X2)) ),
    inference(light_normalisation,[status(thm)],[c_30367,c_14019])).

cnf(c_491,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_10])).

cnf(c_512,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_491,c_9])).

cnf(c_21594,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_512,c_9])).

cnf(c_14473,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_9,c_505])).

cnf(c_14659,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_14473,c_14019])).

cnf(c_14660,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_14659,c_9])).

cnf(c_21610,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(light_normalisation,[status(thm)],[c_21594,c_14660])).

cnf(c_30620,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_30619,c_21610,c_29977])).

cnf(c_30621,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_30366,c_30620])).

cnf(c_30637,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_30355,c_15464,c_30621])).

cnf(c_32933,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7886,c_8664])).

cnf(c_7883,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_7564,c_762])).

cnf(c_8819,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_363,c_8662])).

cnf(c_33070,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_32933,c_7883,c_8819])).

cnf(c_33180,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_766,c_33070])).

cnf(c_33945,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_33944,c_1291,c_30637,c_33180])).

cnf(c_7847,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7564,c_766])).

cnf(c_16021,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_7847])).

cnf(c_34473,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_16021,c_29977])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_191,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK1))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_11,c_9,c_10])).

cnf(c_15989,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_7847,c_191])).

cnf(c_34476,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_34473,c_15989])).

cnf(c_37082,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_33945,c_34476])).

cnf(c_8274,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_7417])).

cnf(c_8320,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_8274,c_7828])).

cnf(c_37083,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_37082,c_8320,c_8660])).

cnf(c_37084,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_37083])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:48:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 11.60/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.60/2.01  
% 11.60/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.60/2.01  
% 11.60/2.01  ------  iProver source info
% 11.60/2.01  
% 11.60/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.60/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.60/2.01  git: non_committed_changes: false
% 11.60/2.01  git: last_make_outside_of_git: false
% 11.60/2.01  
% 11.60/2.01  ------ 
% 11.60/2.01  
% 11.60/2.01  ------ Input Options
% 11.60/2.01  
% 11.60/2.01  --out_options                           all
% 11.60/2.01  --tptp_safe_out                         true
% 11.60/2.01  --problem_path                          ""
% 11.60/2.01  --include_path                          ""
% 11.60/2.01  --clausifier                            res/vclausify_rel
% 11.60/2.01  --clausifier_options                    ""
% 11.60/2.01  --stdin                                 false
% 11.60/2.01  --stats_out                             all
% 11.60/2.01  
% 11.60/2.01  ------ General Options
% 11.60/2.01  
% 11.60/2.01  --fof                                   false
% 11.60/2.01  --time_out_real                         305.
% 11.60/2.01  --time_out_virtual                      -1.
% 11.60/2.01  --symbol_type_check                     false
% 11.60/2.01  --clausify_out                          false
% 11.60/2.01  --sig_cnt_out                           false
% 11.60/2.01  --trig_cnt_out                          false
% 11.60/2.01  --trig_cnt_out_tolerance                1.
% 11.60/2.01  --trig_cnt_out_sk_spl                   false
% 11.60/2.01  --abstr_cl_out                          false
% 11.60/2.01  
% 11.60/2.01  ------ Global Options
% 11.60/2.01  
% 11.60/2.01  --schedule                              default
% 11.60/2.01  --add_important_lit                     false
% 11.60/2.01  --prop_solver_per_cl                    1000
% 11.60/2.01  --min_unsat_core                        false
% 11.60/2.01  --soft_assumptions                      false
% 11.60/2.01  --soft_lemma_size                       3
% 11.60/2.01  --prop_impl_unit_size                   0
% 11.60/2.01  --prop_impl_unit                        []
% 11.60/2.01  --share_sel_clauses                     true
% 11.60/2.01  --reset_solvers                         false
% 11.60/2.01  --bc_imp_inh                            [conj_cone]
% 11.60/2.01  --conj_cone_tolerance                   3.
% 11.60/2.01  --extra_neg_conj                        none
% 11.60/2.01  --large_theory_mode                     true
% 11.60/2.01  --prolific_symb_bound                   200
% 11.60/2.01  --lt_threshold                          2000
% 11.60/2.01  --clause_weak_htbl                      true
% 11.60/2.01  --gc_record_bc_elim                     false
% 11.60/2.01  
% 11.60/2.01  ------ Preprocessing Options
% 11.60/2.01  
% 11.60/2.01  --preprocessing_flag                    true
% 11.60/2.01  --time_out_prep_mult                    0.1
% 11.60/2.01  --splitting_mode                        input
% 11.60/2.01  --splitting_grd                         true
% 11.60/2.01  --splitting_cvd                         false
% 11.60/2.01  --splitting_cvd_svl                     false
% 11.60/2.01  --splitting_nvd                         32
% 11.60/2.01  --sub_typing                            true
% 11.60/2.01  --prep_gs_sim                           true
% 11.60/2.01  --prep_unflatten                        true
% 11.60/2.01  --prep_res_sim                          true
% 11.60/2.01  --prep_upred                            true
% 11.60/2.01  --prep_sem_filter                       exhaustive
% 11.60/2.01  --prep_sem_filter_out                   false
% 11.60/2.01  --pred_elim                             true
% 11.60/2.01  --res_sim_input                         true
% 11.60/2.01  --eq_ax_congr_red                       true
% 11.60/2.01  --pure_diseq_elim                       true
% 11.60/2.01  --brand_transform                       false
% 11.60/2.01  --non_eq_to_eq                          false
% 11.60/2.01  --prep_def_merge                        true
% 11.60/2.01  --prep_def_merge_prop_impl              false
% 11.60/2.01  --prep_def_merge_mbd                    true
% 11.60/2.01  --prep_def_merge_tr_red                 false
% 11.60/2.01  --prep_def_merge_tr_cl                  false
% 11.60/2.01  --smt_preprocessing                     true
% 11.60/2.01  --smt_ac_axioms                         fast
% 11.60/2.01  --preprocessed_out                      false
% 11.60/2.01  --preprocessed_stats                    false
% 11.60/2.01  
% 11.60/2.01  ------ Abstraction refinement Options
% 11.60/2.01  
% 11.60/2.01  --abstr_ref                             []
% 11.60/2.01  --abstr_ref_prep                        false
% 11.60/2.01  --abstr_ref_until_sat                   false
% 11.60/2.01  --abstr_ref_sig_restrict                funpre
% 11.60/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.60/2.01  --abstr_ref_under                       []
% 11.60/2.01  
% 11.60/2.01  ------ SAT Options
% 11.60/2.01  
% 11.60/2.01  --sat_mode                              false
% 11.60/2.01  --sat_fm_restart_options                ""
% 11.60/2.01  --sat_gr_def                            false
% 11.60/2.01  --sat_epr_types                         true
% 11.60/2.01  --sat_non_cyclic_types                  false
% 11.60/2.01  --sat_finite_models                     false
% 11.60/2.01  --sat_fm_lemmas                         false
% 11.60/2.01  --sat_fm_prep                           false
% 11.60/2.01  --sat_fm_uc_incr                        true
% 11.60/2.01  --sat_out_model                         small
% 11.60/2.01  --sat_out_clauses                       false
% 11.60/2.01  
% 11.60/2.01  ------ QBF Options
% 11.60/2.01  
% 11.60/2.01  --qbf_mode                              false
% 11.60/2.01  --qbf_elim_univ                         false
% 11.60/2.01  --qbf_dom_inst                          none
% 11.60/2.01  --qbf_dom_pre_inst                      false
% 11.60/2.01  --qbf_sk_in                             false
% 11.60/2.01  --qbf_pred_elim                         true
% 11.60/2.01  --qbf_split                             512
% 11.60/2.01  
% 11.60/2.01  ------ BMC1 Options
% 11.60/2.01  
% 11.60/2.01  --bmc1_incremental                      false
% 11.60/2.01  --bmc1_axioms                           reachable_all
% 11.60/2.01  --bmc1_min_bound                        0
% 11.60/2.01  --bmc1_max_bound                        -1
% 11.60/2.01  --bmc1_max_bound_default                -1
% 11.60/2.01  --bmc1_symbol_reachability              true
% 11.60/2.01  --bmc1_property_lemmas                  false
% 11.60/2.01  --bmc1_k_induction                      false
% 11.60/2.01  --bmc1_non_equiv_states                 false
% 11.60/2.01  --bmc1_deadlock                         false
% 11.60/2.01  --bmc1_ucm                              false
% 11.60/2.01  --bmc1_add_unsat_core                   none
% 11.60/2.01  --bmc1_unsat_core_children              false
% 11.60/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.60/2.01  --bmc1_out_stat                         full
% 11.60/2.01  --bmc1_ground_init                      false
% 11.60/2.01  --bmc1_pre_inst_next_state              false
% 11.60/2.01  --bmc1_pre_inst_state                   false
% 11.60/2.01  --bmc1_pre_inst_reach_state             false
% 11.60/2.01  --bmc1_out_unsat_core                   false
% 11.60/2.01  --bmc1_aig_witness_out                  false
% 11.60/2.01  --bmc1_verbose                          false
% 11.60/2.01  --bmc1_dump_clauses_tptp                false
% 11.60/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.60/2.01  --bmc1_dump_file                        -
% 11.60/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.60/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.60/2.01  --bmc1_ucm_extend_mode                  1
% 11.60/2.01  --bmc1_ucm_init_mode                    2
% 11.60/2.01  --bmc1_ucm_cone_mode                    none
% 11.60/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.60/2.01  --bmc1_ucm_relax_model                  4
% 11.60/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.60/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.60/2.01  --bmc1_ucm_layered_model                none
% 11.60/2.01  --bmc1_ucm_max_lemma_size               10
% 11.60/2.01  
% 11.60/2.01  ------ AIG Options
% 11.60/2.01  
% 11.60/2.01  --aig_mode                              false
% 11.60/2.01  
% 11.60/2.01  ------ Instantiation Options
% 11.60/2.01  
% 11.60/2.01  --instantiation_flag                    true
% 11.60/2.01  --inst_sos_flag                         true
% 11.60/2.01  --inst_sos_phase                        true
% 11.60/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.60/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.60/2.01  --inst_lit_sel_side                     num_symb
% 11.60/2.01  --inst_solver_per_active                1400
% 11.60/2.01  --inst_solver_calls_frac                1.
% 11.60/2.01  --inst_passive_queue_type               priority_queues
% 11.60/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.60/2.01  --inst_passive_queues_freq              [25;2]
% 11.60/2.01  --inst_dismatching                      true
% 11.60/2.01  --inst_eager_unprocessed_to_passive     true
% 11.60/2.01  --inst_prop_sim_given                   true
% 11.60/2.01  --inst_prop_sim_new                     false
% 11.60/2.01  --inst_subs_new                         false
% 11.60/2.01  --inst_eq_res_simp                      false
% 11.60/2.01  --inst_subs_given                       false
% 11.60/2.01  --inst_orphan_elimination               true
% 11.60/2.01  --inst_learning_loop_flag               true
% 11.60/2.01  --inst_learning_start                   3000
% 11.60/2.01  --inst_learning_factor                  2
% 11.60/2.01  --inst_start_prop_sim_after_learn       3
% 11.60/2.01  --inst_sel_renew                        solver
% 11.60/2.01  --inst_lit_activity_flag                true
% 11.60/2.01  --inst_restr_to_given                   false
% 11.60/2.01  --inst_activity_threshold               500
% 11.60/2.01  --inst_out_proof                        true
% 11.60/2.01  
% 11.60/2.01  ------ Resolution Options
% 11.60/2.01  
% 11.60/2.01  --resolution_flag                       true
% 11.60/2.01  --res_lit_sel                           adaptive
% 11.60/2.01  --res_lit_sel_side                      none
% 11.60/2.01  --res_ordering                          kbo
% 11.60/2.01  --res_to_prop_solver                    active
% 11.60/2.01  --res_prop_simpl_new                    false
% 11.60/2.01  --res_prop_simpl_given                  true
% 11.60/2.01  --res_passive_queue_type                priority_queues
% 11.60/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.60/2.01  --res_passive_queues_freq               [15;5]
% 11.60/2.01  --res_forward_subs                      full
% 11.60/2.01  --res_backward_subs                     full
% 11.60/2.01  --res_forward_subs_resolution           true
% 11.60/2.01  --res_backward_subs_resolution          true
% 11.60/2.01  --res_orphan_elimination                true
% 11.60/2.01  --res_time_limit                        2.
% 11.60/2.01  --res_out_proof                         true
% 11.60/2.01  
% 11.60/2.01  ------ Superposition Options
% 11.60/2.01  
% 11.60/2.01  --superposition_flag                    true
% 11.60/2.01  --sup_passive_queue_type                priority_queues
% 11.60/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.60/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.60/2.01  --demod_completeness_check              fast
% 11.60/2.01  --demod_use_ground                      true
% 11.60/2.01  --sup_to_prop_solver                    passive
% 11.60/2.01  --sup_prop_simpl_new                    true
% 11.60/2.01  --sup_prop_simpl_given                  true
% 11.60/2.01  --sup_fun_splitting                     true
% 11.60/2.01  --sup_smt_interval                      50000
% 11.60/2.01  
% 11.60/2.01  ------ Superposition Simplification Setup
% 11.60/2.01  
% 11.60/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.60/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.60/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.60/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.60/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.60/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.60/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.60/2.01  --sup_immed_triv                        [TrivRules]
% 11.60/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/2.01  --sup_immed_bw_main                     []
% 11.60/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.60/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.60/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/2.01  --sup_input_bw                          []
% 11.60/2.01  
% 11.60/2.01  ------ Combination Options
% 11.60/2.01  
% 11.60/2.01  --comb_res_mult                         3
% 11.60/2.01  --comb_sup_mult                         2
% 11.60/2.01  --comb_inst_mult                        10
% 11.60/2.01  
% 11.60/2.01  ------ Debug Options
% 11.60/2.01  
% 11.60/2.01  --dbg_backtrace                         false
% 11.60/2.01  --dbg_dump_prop_clauses                 false
% 11.60/2.01  --dbg_dump_prop_clauses_file            -
% 11.60/2.01  --dbg_out_stat                          false
% 11.60/2.01  ------ Parsing...
% 11.60/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.60/2.01  
% 11.60/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.60/2.01  
% 11.60/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.60/2.01  
% 11.60/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.60/2.01  ------ Proving...
% 11.60/2.01  ------ Problem Properties 
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  clauses                                 12
% 11.60/2.01  conjectures                             1
% 11.60/2.01  EPR                                     0
% 11.60/2.01  Horn                                    8
% 11.60/2.01  unary                                   6
% 11.60/2.01  binary                                  2
% 11.60/2.01  lits                                    23
% 11.60/2.01  lits eq                                 9
% 11.60/2.01  fd_pure                                 0
% 11.60/2.01  fd_pseudo                               0
% 11.60/2.01  fd_cond                                 0
% 11.60/2.01  fd_pseudo_cond                          3
% 11.60/2.01  AC symbols                              0
% 11.60/2.01  
% 11.60/2.01  ------ Schedule dynamic 5 is on 
% 11.60/2.01  
% 11.60/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  ------ 
% 11.60/2.01  Current options:
% 11.60/2.01  ------ 
% 11.60/2.01  
% 11.60/2.01  ------ Input Options
% 11.60/2.01  
% 11.60/2.01  --out_options                           all
% 11.60/2.01  --tptp_safe_out                         true
% 11.60/2.01  --problem_path                          ""
% 11.60/2.01  --include_path                          ""
% 11.60/2.01  --clausifier                            res/vclausify_rel
% 11.60/2.01  --clausifier_options                    ""
% 11.60/2.01  --stdin                                 false
% 11.60/2.01  --stats_out                             all
% 11.60/2.01  
% 11.60/2.01  ------ General Options
% 11.60/2.01  
% 11.60/2.01  --fof                                   false
% 11.60/2.01  --time_out_real                         305.
% 11.60/2.01  --time_out_virtual                      -1.
% 11.60/2.01  --symbol_type_check                     false
% 11.60/2.01  --clausify_out                          false
% 11.60/2.01  --sig_cnt_out                           false
% 11.60/2.01  --trig_cnt_out                          false
% 11.60/2.01  --trig_cnt_out_tolerance                1.
% 11.60/2.01  --trig_cnt_out_sk_spl                   false
% 11.60/2.01  --abstr_cl_out                          false
% 11.60/2.01  
% 11.60/2.01  ------ Global Options
% 11.60/2.01  
% 11.60/2.01  --schedule                              default
% 11.60/2.01  --add_important_lit                     false
% 11.60/2.01  --prop_solver_per_cl                    1000
% 11.60/2.01  --min_unsat_core                        false
% 11.60/2.01  --soft_assumptions                      false
% 11.60/2.01  --soft_lemma_size                       3
% 11.60/2.01  --prop_impl_unit_size                   0
% 11.60/2.01  --prop_impl_unit                        []
% 11.60/2.01  --share_sel_clauses                     true
% 11.60/2.01  --reset_solvers                         false
% 11.60/2.01  --bc_imp_inh                            [conj_cone]
% 11.60/2.01  --conj_cone_tolerance                   3.
% 11.60/2.01  --extra_neg_conj                        none
% 11.60/2.01  --large_theory_mode                     true
% 11.60/2.01  --prolific_symb_bound                   200
% 11.60/2.01  --lt_threshold                          2000
% 11.60/2.01  --clause_weak_htbl                      true
% 11.60/2.01  --gc_record_bc_elim                     false
% 11.60/2.01  
% 11.60/2.01  ------ Preprocessing Options
% 11.60/2.01  
% 11.60/2.01  --preprocessing_flag                    true
% 11.60/2.01  --time_out_prep_mult                    0.1
% 11.60/2.01  --splitting_mode                        input
% 11.60/2.01  --splitting_grd                         true
% 11.60/2.01  --splitting_cvd                         false
% 11.60/2.01  --splitting_cvd_svl                     false
% 11.60/2.01  --splitting_nvd                         32
% 11.60/2.01  --sub_typing                            true
% 11.60/2.01  --prep_gs_sim                           true
% 11.60/2.01  --prep_unflatten                        true
% 11.60/2.01  --prep_res_sim                          true
% 11.60/2.01  --prep_upred                            true
% 11.60/2.01  --prep_sem_filter                       exhaustive
% 11.60/2.01  --prep_sem_filter_out                   false
% 11.60/2.01  --pred_elim                             true
% 11.60/2.01  --res_sim_input                         true
% 11.60/2.01  --eq_ax_congr_red                       true
% 11.60/2.01  --pure_diseq_elim                       true
% 11.60/2.01  --brand_transform                       false
% 11.60/2.01  --non_eq_to_eq                          false
% 11.60/2.01  --prep_def_merge                        true
% 11.60/2.01  --prep_def_merge_prop_impl              false
% 11.60/2.01  --prep_def_merge_mbd                    true
% 11.60/2.01  --prep_def_merge_tr_red                 false
% 11.60/2.01  --prep_def_merge_tr_cl                  false
% 11.60/2.01  --smt_preprocessing                     true
% 11.60/2.01  --smt_ac_axioms                         fast
% 11.60/2.01  --preprocessed_out                      false
% 11.60/2.01  --preprocessed_stats                    false
% 11.60/2.01  
% 11.60/2.01  ------ Abstraction refinement Options
% 11.60/2.01  
% 11.60/2.01  --abstr_ref                             []
% 11.60/2.01  --abstr_ref_prep                        false
% 11.60/2.01  --abstr_ref_until_sat                   false
% 11.60/2.01  --abstr_ref_sig_restrict                funpre
% 11.60/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.60/2.01  --abstr_ref_under                       []
% 11.60/2.01  
% 11.60/2.01  ------ SAT Options
% 11.60/2.01  
% 11.60/2.01  --sat_mode                              false
% 11.60/2.01  --sat_fm_restart_options                ""
% 11.60/2.01  --sat_gr_def                            false
% 11.60/2.01  --sat_epr_types                         true
% 11.60/2.01  --sat_non_cyclic_types                  false
% 11.60/2.01  --sat_finite_models                     false
% 11.60/2.01  --sat_fm_lemmas                         false
% 11.60/2.01  --sat_fm_prep                           false
% 11.60/2.01  --sat_fm_uc_incr                        true
% 11.60/2.01  --sat_out_model                         small
% 11.60/2.01  --sat_out_clauses                       false
% 11.60/2.01  
% 11.60/2.01  ------ QBF Options
% 11.60/2.01  
% 11.60/2.01  --qbf_mode                              false
% 11.60/2.01  --qbf_elim_univ                         false
% 11.60/2.01  --qbf_dom_inst                          none
% 11.60/2.01  --qbf_dom_pre_inst                      false
% 11.60/2.01  --qbf_sk_in                             false
% 11.60/2.01  --qbf_pred_elim                         true
% 11.60/2.01  --qbf_split                             512
% 11.60/2.01  
% 11.60/2.01  ------ BMC1 Options
% 11.60/2.01  
% 11.60/2.01  --bmc1_incremental                      false
% 11.60/2.01  --bmc1_axioms                           reachable_all
% 11.60/2.01  --bmc1_min_bound                        0
% 11.60/2.01  --bmc1_max_bound                        -1
% 11.60/2.01  --bmc1_max_bound_default                -1
% 11.60/2.01  --bmc1_symbol_reachability              true
% 11.60/2.01  --bmc1_property_lemmas                  false
% 11.60/2.01  --bmc1_k_induction                      false
% 11.60/2.01  --bmc1_non_equiv_states                 false
% 11.60/2.01  --bmc1_deadlock                         false
% 11.60/2.01  --bmc1_ucm                              false
% 11.60/2.01  --bmc1_add_unsat_core                   none
% 11.60/2.01  --bmc1_unsat_core_children              false
% 11.60/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.60/2.01  --bmc1_out_stat                         full
% 11.60/2.01  --bmc1_ground_init                      false
% 11.60/2.01  --bmc1_pre_inst_next_state              false
% 11.60/2.01  --bmc1_pre_inst_state                   false
% 11.60/2.01  --bmc1_pre_inst_reach_state             false
% 11.60/2.01  --bmc1_out_unsat_core                   false
% 11.60/2.01  --bmc1_aig_witness_out                  false
% 11.60/2.01  --bmc1_verbose                          false
% 11.60/2.01  --bmc1_dump_clauses_tptp                false
% 11.60/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.60/2.01  --bmc1_dump_file                        -
% 11.60/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.60/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.60/2.01  --bmc1_ucm_extend_mode                  1
% 11.60/2.01  --bmc1_ucm_init_mode                    2
% 11.60/2.01  --bmc1_ucm_cone_mode                    none
% 11.60/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.60/2.01  --bmc1_ucm_relax_model                  4
% 11.60/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.60/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.60/2.01  --bmc1_ucm_layered_model                none
% 11.60/2.01  --bmc1_ucm_max_lemma_size               10
% 11.60/2.01  
% 11.60/2.01  ------ AIG Options
% 11.60/2.01  
% 11.60/2.01  --aig_mode                              false
% 11.60/2.01  
% 11.60/2.01  ------ Instantiation Options
% 11.60/2.01  
% 11.60/2.01  --instantiation_flag                    true
% 11.60/2.01  --inst_sos_flag                         true
% 11.60/2.01  --inst_sos_phase                        true
% 11.60/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.60/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.60/2.01  --inst_lit_sel_side                     none
% 11.60/2.01  --inst_solver_per_active                1400
% 11.60/2.01  --inst_solver_calls_frac                1.
% 11.60/2.01  --inst_passive_queue_type               priority_queues
% 11.60/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.60/2.01  --inst_passive_queues_freq              [25;2]
% 11.60/2.01  --inst_dismatching                      true
% 11.60/2.01  --inst_eager_unprocessed_to_passive     true
% 11.60/2.01  --inst_prop_sim_given                   true
% 11.60/2.01  --inst_prop_sim_new                     false
% 11.60/2.01  --inst_subs_new                         false
% 11.60/2.01  --inst_eq_res_simp                      false
% 11.60/2.01  --inst_subs_given                       false
% 11.60/2.01  --inst_orphan_elimination               true
% 11.60/2.01  --inst_learning_loop_flag               true
% 11.60/2.01  --inst_learning_start                   3000
% 11.60/2.01  --inst_learning_factor                  2
% 11.60/2.01  --inst_start_prop_sim_after_learn       3
% 11.60/2.01  --inst_sel_renew                        solver
% 11.60/2.01  --inst_lit_activity_flag                true
% 11.60/2.01  --inst_restr_to_given                   false
% 11.60/2.01  --inst_activity_threshold               500
% 11.60/2.01  --inst_out_proof                        true
% 11.60/2.01  
% 11.60/2.01  ------ Resolution Options
% 11.60/2.01  
% 11.60/2.01  --resolution_flag                       false
% 11.60/2.01  --res_lit_sel                           adaptive
% 11.60/2.01  --res_lit_sel_side                      none
% 11.60/2.01  --res_ordering                          kbo
% 11.60/2.01  --res_to_prop_solver                    active
% 11.60/2.01  --res_prop_simpl_new                    false
% 11.60/2.01  --res_prop_simpl_given                  true
% 11.60/2.01  --res_passive_queue_type                priority_queues
% 11.60/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.60/2.01  --res_passive_queues_freq               [15;5]
% 11.60/2.01  --res_forward_subs                      full
% 11.60/2.01  --res_backward_subs                     full
% 11.60/2.01  --res_forward_subs_resolution           true
% 11.60/2.01  --res_backward_subs_resolution          true
% 11.60/2.01  --res_orphan_elimination                true
% 11.60/2.01  --res_time_limit                        2.
% 11.60/2.01  --res_out_proof                         true
% 11.60/2.01  
% 11.60/2.01  ------ Superposition Options
% 11.60/2.01  
% 11.60/2.01  --superposition_flag                    true
% 11.60/2.01  --sup_passive_queue_type                priority_queues
% 11.60/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.60/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.60/2.01  --demod_completeness_check              fast
% 11.60/2.01  --demod_use_ground                      true
% 11.60/2.01  --sup_to_prop_solver                    passive
% 11.60/2.01  --sup_prop_simpl_new                    true
% 11.60/2.01  --sup_prop_simpl_given                  true
% 11.60/2.01  --sup_fun_splitting                     true
% 11.60/2.01  --sup_smt_interval                      50000
% 11.60/2.01  
% 11.60/2.01  ------ Superposition Simplification Setup
% 11.60/2.01  
% 11.60/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.60/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.60/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.60/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.60/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.60/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.60/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.60/2.01  --sup_immed_triv                        [TrivRules]
% 11.60/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/2.01  --sup_immed_bw_main                     []
% 11.60/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.60/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.60/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.60/2.01  --sup_input_bw                          []
% 11.60/2.01  
% 11.60/2.01  ------ Combination Options
% 11.60/2.01  
% 11.60/2.01  --comb_res_mult                         3
% 11.60/2.01  --comb_sup_mult                         2
% 11.60/2.01  --comb_inst_mult                        10
% 11.60/2.01  
% 11.60/2.01  ------ Debug Options
% 11.60/2.01  
% 11.60/2.01  --dbg_backtrace                         false
% 11.60/2.01  --dbg_dump_prop_clauses                 false
% 11.60/2.01  --dbg_dump_prop_clauses_file            -
% 11.60/2.01  --dbg_out_stat                          false
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  ------ Proving...
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  % SZS status Theorem for theBenchmark.p
% 11.60/2.01  
% 11.60/2.01   Resolution empty clause
% 11.60/2.01  
% 11.60/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.60/2.01  
% 11.60/2.01  fof(f4,axiom,(
% 11.60/2.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f27,plain,(
% 11.60/2.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.60/2.01    inference(cnf_transformation,[],[f4])).
% 11.60/2.01  
% 11.60/2.01  fof(f5,axiom,(
% 11.60/2.01    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f28,plain,(
% 11.60/2.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.60/2.01    inference(cnf_transformation,[],[f5])).
% 11.60/2.01  
% 11.60/2.01  fof(f1,axiom,(
% 11.60/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f19,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.60/2.01    inference(cnf_transformation,[],[f1])).
% 11.60/2.01  
% 11.60/2.01  fof(f7,axiom,(
% 11.60/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f30,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.60/2.01    inference(cnf_transformation,[],[f7])).
% 11.60/2.01  
% 11.60/2.01  fof(f34,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.60/2.01    inference(definition_unfolding,[],[f19,f30,f30])).
% 11.60/2.01  
% 11.60/2.01  fof(f6,axiom,(
% 11.60/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f29,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.60/2.01    inference(cnf_transformation,[],[f6])).
% 11.60/2.01  
% 11.60/2.01  fof(f35,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.60/2.01    inference(definition_unfolding,[],[f29,f30])).
% 11.60/2.01  
% 11.60/2.01  fof(f8,axiom,(
% 11.60/2.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f31,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.60/2.01    inference(cnf_transformation,[],[f8])).
% 11.60/2.01  
% 11.60/2.01  fof(f3,axiom,(
% 11.60/2.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f26,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 11.60/2.01    inference(cnf_transformation,[],[f3])).
% 11.60/2.01  
% 11.60/2.01  fof(f33,plain,(
% 11.60/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 11.60/2.01    inference(definition_unfolding,[],[f31,f26])).
% 11.60/2.01  
% 11.60/2.01  fof(f9,conjecture,(
% 11.60/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.60/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.60/2.01  
% 11.60/2.01  fof(f10,negated_conjecture,(
% 11.60/2.01    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.60/2.01    inference(negated_conjecture,[],[f9])).
% 11.60/2.01  
% 11.60/2.01  fof(f11,plain,(
% 11.60/2.01    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.60/2.01    inference(ennf_transformation,[],[f10])).
% 11.60/2.01  
% 11.60/2.01  fof(f17,plain,(
% 11.60/2.01    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 11.60/2.01    introduced(choice_axiom,[])).
% 11.60/2.01  
% 11.60/2.01  fof(f18,plain,(
% 11.60/2.01    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 11.60/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17])).
% 11.60/2.01  
% 11.60/2.01  fof(f32,plain,(
% 11.60/2.01    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 11.60/2.01    inference(cnf_transformation,[],[f18])).
% 11.60/2.01  
% 11.60/2.01  fof(f36,plain,(
% 11.60/2.01    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 11.60/2.01    inference(definition_unfolding,[],[f32,f26,f30])).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.60/2.01      inference(cnf_transformation,[],[f27]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_9,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.60/2.01      inference(cnf_transformation,[],[f28]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_420,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(cnf_transformation,[],[f34]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_363,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_448,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_420,c_363]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_449,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_448,c_420]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1203,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_449,c_1]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_10,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(cnf_transformation,[],[f35]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_495,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_510,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_495,c_8]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_623,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_420,c_510]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_629,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_623,c_449]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1211,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_1203,c_629]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1212,plain,
% 11.60/2.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_1211,c_420,c_510]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_0,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(X0,X1) ),
% 11.60/2.01      inference(cnf_transformation,[],[f33]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_190,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_0,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7398,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1212,c_190]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7414,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_7398,c_8,c_1212]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_422,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_363,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1746,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_422,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_489,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_10]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_737,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_489]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_765,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_737,c_489]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_766,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_765,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_492,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_363,c_10]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_748,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_492,c_489]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_429,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_760,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_748,c_9,c_429]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_3596,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_363,c_760]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_4113,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_766,c_3596]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_4551,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1746,c_4113]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7564,plain,
% 11.60/2.01      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_7414,c_4551]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_423,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_363,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_2004,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_363,c_423]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_742,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_363,c_489]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_761,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_742,c_492]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_762,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_761,c_9,c_429]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_624,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_510,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1417,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_762,c_624]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1420,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_1417,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_2075,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_2004,c_492,c_1420]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7853,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_2075]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1416,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_762,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7909,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_7853,c_1416]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7375,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_4551,c_190]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7448,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_7375,c_7414]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_480,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_429,c_363]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_481,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_480,c_429]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1285,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_481,c_1]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_622,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_429,c_510]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_630,plain,
% 11.60/2.01      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_622,c_481]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1290,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0))) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_1285,c_630]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_1291,plain,
% 11.60/2.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_1290,c_429,c_510]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7449,plain,
% 11.60/2.01      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) = X0 ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_7448,c_510,c_1291]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7395,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_4113,c_190]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7417,plain,
% 11.60/2.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_7395,c_510]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_4303,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_4113,c_423]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7875,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),X0) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_4303]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7878,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_2075]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7886,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_363]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7896,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_7875,c_7878,c_7886]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8660,plain,
% 11.60/2.01      ( k2_xboole_0(X0,X0) = X0 ),
% 11.60/2.01      inference(light_normalisation,
% 11.60/2.01                [status(thm)],
% 11.60/2.01                [c_7449,c_7417,c_7449,c_7896]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8664,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_8660,c_190]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_32900,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7909,c_8664]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7836,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_760]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7844,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_510]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7921,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_7836,c_7844,c_7909]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7388,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = k2_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1746,c_190]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7428,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_7388,c_7414]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7429,plain,
% 11.60/2.01      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_7428,c_510]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8662,plain,
% 11.60/2.01      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_8660,c_7429]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8825,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_492,c_8662]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33105,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(X0,X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_32900,c_7921,c_8825]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_418,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33905,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_33105,c_418]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_9753,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_418,c_766]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_501,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_505,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_501,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14450,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_8660,c_505]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14682,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_14450,c_10]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14730,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_14682]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_15366,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_14730,c_418]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_9648,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_418]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_15398,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_15366,c_9,c_9648]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_427,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_431,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_427,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_13895,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_766,c_431]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_426,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14019,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_431,c_426]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14120,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_13895,c_14019]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_626,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_510,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_628,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_626,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14121,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_14120,c_628]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_15399,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_15398,c_9,c_14121]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_29895,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_15399,c_426]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_4093,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_766,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_9698,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_418,c_4093]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_29976,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_29895,c_9,c_9698,c_14019]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7828,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_29977,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_29976,c_7828,c_14730]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_32892,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_8664]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33109,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_32892,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33110,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_33109,c_14730]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33944,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(light_normalisation,
% 11.60/2.01                [status(thm)],
% 11.60/2.01                [c_33905,c_9753,c_29977,c_33110]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_15286,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_14730]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_15463,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_15286,c_489]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_4059,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_766]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_4156,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_4059,c_766]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_425,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_432,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_425,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_4157,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_4156,c_9,c_432]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_15464,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_15463,c_9,c_4157]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_30355,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_10,c_15464]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_30366,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X2)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_431,c_15464]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_30367,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X2)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_426,c_15464]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_30619,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X2)) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_30367,c_14019]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_491,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_10]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_512,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_491,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_21594,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_512,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14473,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_505]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14659,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_14473,c_14019]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_14660,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_14659,c_9]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_21610,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_21594,c_14660]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_30620,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_30619,c_21610,c_29977]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_30621,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_30366,c_30620]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_30637,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_30355,c_15464,c_30621]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_32933,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7886,c_8664]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7883,plain,
% 11.60/2.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_762]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8819,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_363,c_8662]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33070,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_32933,c_7883,c_8819]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33180,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_766,c_33070]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_33945,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_33944,c_1291,c_30637,c_33180]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_7847,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_7564,c_766]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_16021,plain,
% 11.60/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_1,c_7847]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_34473,plain,
% 11.60/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_16021,c_29977]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_11,negated_conjecture,
% 11.60/2.01      ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
% 11.60/2.01      inference(cnf_transformation,[],[f36]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_191,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK1))) != k4_xboole_0(sK1,sK2) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_11,c_9,c_10]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_15989,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK1,sK2) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_7847,c_191]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_34476,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))) != k4_xboole_0(sK1,sK2) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_34473,c_15989]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_37082,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_33945,c_34476]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8274,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(superposition,[status(thm)],[c_9,c_7417]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_8320,plain,
% 11.60/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 11.60/2.01      inference(light_normalisation,[status(thm)],[c_8274,c_7828]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_37083,plain,
% 11.60/2.01      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 11.60/2.01      inference(demodulation,[status(thm)],[c_37082,c_8320,c_8660]) ).
% 11.60/2.01  
% 11.60/2.01  cnf(c_37084,plain,
% 11.60/2.01      ( $false ),
% 11.60/2.01      inference(equality_resolution_simp,[status(thm)],[c_37083]) ).
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.60/2.01  
% 11.60/2.01  ------                               Statistics
% 11.60/2.01  
% 11.60/2.01  ------ General
% 11.60/2.01  
% 11.60/2.01  abstr_ref_over_cycles:                  0
% 11.60/2.01  abstr_ref_under_cycles:                 0
% 11.60/2.01  gc_basic_clause_elim:                   0
% 11.60/2.01  forced_gc_time:                         0
% 11.60/2.01  parsing_time:                           0.01
% 11.60/2.01  unif_index_cands_time:                  0.
% 11.60/2.01  unif_index_add_time:                    0.
% 11.60/2.01  orderings_time:                         0.
% 11.60/2.01  out_proof_time:                         0.011
% 11.60/2.01  total_time:                             1.181
% 11.60/2.01  num_of_symbols:                         38
% 11.60/2.01  num_of_terms:                           52239
% 11.60/2.01  
% 11.60/2.01  ------ Preprocessing
% 11.60/2.01  
% 11.60/2.01  num_of_splits:                          0
% 11.60/2.01  num_of_split_atoms:                     0
% 11.60/2.01  num_of_reused_defs:                     0
% 11.60/2.01  num_eq_ax_congr_red:                    6
% 11.60/2.01  num_of_sem_filtered_clauses:            1
% 11.60/2.01  num_of_subtypes:                        0
% 11.60/2.01  monotx_restored_types:                  0
% 11.60/2.01  sat_num_of_epr_types:                   0
% 11.60/2.01  sat_num_of_non_cyclic_types:            0
% 11.60/2.01  sat_guarded_non_collapsed_types:        0
% 11.60/2.01  num_pure_diseq_elim:                    0
% 11.60/2.01  simp_replaced_by:                       0
% 11.60/2.01  res_preprocessed:                       47
% 11.60/2.01  prep_upred:                             0
% 11.60/2.01  prep_unflattend:                        0
% 11.60/2.01  smt_new_axioms:                         0
% 11.60/2.01  pred_elim_cands:                        1
% 11.60/2.01  pred_elim:                              0
% 11.60/2.01  pred_elim_cl:                           0
% 11.60/2.01  pred_elim_cycles:                       1
% 11.60/2.01  merged_defs:                            0
% 11.60/2.01  merged_defs_ncl:                        0
% 11.60/2.01  bin_hyper_res:                          0
% 11.60/2.01  prep_cycles:                            3
% 11.60/2.01  pred_elim_time:                         0.
% 11.60/2.01  splitting_time:                         0.
% 11.60/2.01  sem_filter_time:                        0.
% 11.60/2.01  monotx_time:                            0.
% 11.60/2.01  subtype_inf_time:                       0.
% 11.60/2.01  
% 11.60/2.01  ------ Problem properties
% 11.60/2.01  
% 11.60/2.01  clauses:                                12
% 11.60/2.01  conjectures:                            1
% 11.60/2.01  epr:                                    0
% 11.60/2.01  horn:                                   8
% 11.60/2.01  ground:                                 1
% 11.60/2.01  unary:                                  6
% 11.60/2.01  binary:                                 2
% 11.60/2.01  lits:                                   23
% 11.60/2.01  lits_eq:                                9
% 11.60/2.01  fd_pure:                                0
% 11.60/2.01  fd_pseudo:                              0
% 11.60/2.01  fd_cond:                                0
% 11.60/2.01  fd_pseudo_cond:                         3
% 11.60/2.01  ac_symbols:                             0
% 11.60/2.01  
% 11.60/2.01  ------ Propositional Solver
% 11.60/2.01  
% 11.60/2.01  prop_solver_calls:                      27
% 11.60/2.01  prop_fast_solver_calls:                 398
% 11.60/2.01  smt_solver_calls:                       0
% 11.60/2.01  smt_fast_solver_calls:                  0
% 11.60/2.01  prop_num_of_clauses:                    8749
% 11.60/2.01  prop_preprocess_simplified:             10933
% 11.60/2.01  prop_fo_subsumed:                       1
% 11.60/2.01  prop_solver_time:                       0.
% 11.60/2.01  smt_solver_time:                        0.
% 11.60/2.01  smt_fast_solver_time:                   0.
% 11.60/2.01  prop_fast_solver_time:                  0.
% 11.60/2.01  prop_unsat_core_time:                   0.
% 11.60/2.01  
% 11.60/2.01  ------ QBF
% 11.60/2.01  
% 11.60/2.01  qbf_q_res:                              0
% 11.60/2.01  qbf_num_tautologies:                    0
% 11.60/2.01  qbf_prep_cycles:                        0
% 11.60/2.01  
% 11.60/2.01  ------ BMC1
% 11.60/2.01  
% 11.60/2.01  bmc1_current_bound:                     -1
% 11.60/2.01  bmc1_last_solved_bound:                 -1
% 11.60/2.01  bmc1_unsat_core_size:                   -1
% 11.60/2.01  bmc1_unsat_core_parents_size:           -1
% 11.60/2.01  bmc1_merge_next_fun:                    0
% 11.60/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.60/2.01  
% 11.60/2.01  ------ Instantiation
% 11.60/2.01  
% 11.60/2.01  inst_num_of_clauses:                    1650
% 11.60/2.01  inst_num_in_passive:                    449
% 11.60/2.01  inst_num_in_active:                     612
% 11.60/2.01  inst_num_in_unprocessed:                589
% 11.60/2.01  inst_num_of_loops:                      710
% 11.60/2.01  inst_num_of_learning_restarts:          0
% 11.60/2.01  inst_num_moves_active_passive:          95
% 11.60/2.01  inst_lit_activity:                      0
% 11.60/2.01  inst_lit_activity_moves:                0
% 11.60/2.01  inst_num_tautologies:                   0
% 11.60/2.01  inst_num_prop_implied:                  0
% 11.60/2.01  inst_num_existing_simplified:           0
% 11.60/2.01  inst_num_eq_res_simplified:             0
% 11.60/2.01  inst_num_child_elim:                    0
% 11.60/2.01  inst_num_of_dismatching_blockings:      4163
% 11.60/2.01  inst_num_of_non_proper_insts:           3433
% 11.60/2.01  inst_num_of_duplicates:                 0
% 11.60/2.01  inst_inst_num_from_inst_to_res:         0
% 11.60/2.01  inst_dismatching_checking_time:         0.
% 11.60/2.01  
% 11.60/2.01  ------ Resolution
% 11.60/2.01  
% 11.60/2.01  res_num_of_clauses:                     0
% 11.60/2.01  res_num_in_passive:                     0
% 11.60/2.01  res_num_in_active:                      0
% 11.60/2.01  res_num_of_loops:                       50
% 11.60/2.01  res_forward_subset_subsumed:            135
% 11.60/2.01  res_backward_subset_subsumed:           0
% 11.60/2.01  res_forward_subsumed:                   0
% 11.60/2.01  res_backward_subsumed:                  0
% 11.60/2.01  res_forward_subsumption_resolution:     0
% 11.60/2.01  res_backward_subsumption_resolution:    0
% 11.60/2.01  res_clause_to_clause_subsumption:       38044
% 11.60/2.01  res_orphan_elimination:                 0
% 11.60/2.01  res_tautology_del:                      132
% 11.60/2.01  res_num_eq_res_simplified:              0
% 11.60/2.01  res_num_sel_changes:                    0
% 11.60/2.01  res_moves_from_active_to_pass:          0
% 11.60/2.01  
% 11.60/2.01  ------ Superposition
% 11.60/2.01  
% 11.60/2.01  sup_time_total:                         0.
% 11.60/2.01  sup_time_generating:                    0.
% 11.60/2.01  sup_time_sim_full:                      0.
% 11.60/2.01  sup_time_sim_immed:                     0.
% 11.60/2.01  
% 11.60/2.01  sup_num_of_clauses:                     2054
% 11.60/2.01  sup_num_in_active:                      111
% 11.60/2.01  sup_num_in_passive:                     1943
% 11.60/2.01  sup_num_of_loops:                       141
% 11.60/2.01  sup_fw_superposition:                   6231
% 11.60/2.01  sup_bw_superposition:                   5154
% 11.60/2.01  sup_immediate_simplified:               7448
% 11.60/2.01  sup_given_eliminated:                   3
% 11.60/2.01  comparisons_done:                       0
% 11.60/2.01  comparisons_avoided:                    0
% 11.60/2.01  
% 11.60/2.01  ------ Simplifications
% 11.60/2.01  
% 11.60/2.01  
% 11.60/2.01  sim_fw_subset_subsumed:                 68
% 11.60/2.01  sim_bw_subset_subsumed:                 6
% 11.60/2.01  sim_fw_subsumed:                        643
% 11.60/2.01  sim_bw_subsumed:                        68
% 11.60/2.01  sim_fw_subsumption_res:                 0
% 11.60/2.01  sim_bw_subsumption_res:                 0
% 11.60/2.01  sim_tautology_del:                      75
% 11.60/2.01  sim_eq_tautology_del:                   1976
% 11.60/2.01  sim_eq_res_simp:                        1
% 11.60/2.01  sim_fw_demodulated:                     4415
% 11.60/2.01  sim_bw_demodulated:                     58
% 11.60/2.01  sim_light_normalised:                   3930
% 11.60/2.01  sim_joinable_taut:                      0
% 11.60/2.01  sim_joinable_simp:                      0
% 11.60/2.01  sim_ac_normalised:                      0
% 11.60/2.01  sim_smt_subsumption:                    0
% 11.60/2.01  
%------------------------------------------------------------------------------
