%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:58 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  145 (33301 expanded)
%              Number of clauses        :  120 (12319 expanded)
%              Number of leaves         :   10 (9611 expanded)
%              Depth                    :   38
%              Number of atoms          :  146 (33302 expanded)
%              Number of equality atoms :  145 (33301 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f15,f20,f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f22,f16,f16,f20])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_5,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_25,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_93,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25,c_5])).

cnf(c_192,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25,c_93])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_202,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_192,c_4])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_33,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_25,c_2])).

cnf(c_53,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_203,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_202,c_2,c_33,c_53])).

cnf(c_224,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_203,c_53])).

cnf(c_225,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_224,c_3])).

cnf(c_256,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_225,c_25])).

cnf(c_339,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_256,c_4])).

cnf(c_344,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_339,c_2])).

cnf(c_380,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_344])).

cnf(c_434,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_380,c_4])).

cnf(c_27,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_276,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_225,c_27])).

cnf(c_102,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_116,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_102,c_0])).

cnf(c_124,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_116,c_2])).

cnf(c_290,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_276,c_3,c_124])).

cnf(c_308,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_290,c_203])).

cnf(c_445,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_434,c_4,c_308])).

cnf(c_755,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_445])).

cnf(c_1387,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_755,c_2])).

cnf(c_1391,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1387,c_290])).

cnf(c_390,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_344,c_2])).

cnf(c_392,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_390,c_290])).

cnf(c_527,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_392])).

cnf(c_336,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_256,c_4])).

cnf(c_348,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_336,c_308])).

cnf(c_1008,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_527,c_348])).

cnf(c_51,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_4565,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1008,c_51])).

cnf(c_4677,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4565,c_290])).

cnf(c_5357,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X2),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4677,c_755])).

cnf(c_5371,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5357,c_4])).

cnf(c_13771,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1391,c_5371])).

cnf(c_90,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_25769,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_13771,c_90])).

cnf(c_995,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_527])).

cnf(c_1030,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_995,c_527])).

cnf(c_1732,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1030,c_0])).

cnf(c_537,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_392,c_0])).

cnf(c_5339,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_4677,c_537])).

cnf(c_5377,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_5339,c_4677])).

cnf(c_41,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_5725,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_5377,c_41])).

cnf(c_5739,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5725,c_3,c_344])).

cnf(c_5829,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5739,c_1])).

cnf(c_5843,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5829,c_3,c_348])).

cnf(c_6064,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1008,c_5843])).

cnf(c_1013,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_527,c_0])).

cnf(c_1432,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1013,c_537])).

cnf(c_1446,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1432,c_1013])).

cnf(c_6130,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_6064,c_1446])).

cnf(c_4541,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_380,c_51])).

cnf(c_4708,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4541,c_290])).

cnf(c_4709,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_4708,c_4])).

cnf(c_11674,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4709,c_344])).

cnf(c_52,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_56,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_52,c_4])).

cnf(c_411,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_348,c_2])).

cnf(c_413,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_411,c_290])).

cnf(c_580,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_413])).

cnf(c_1152,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_580])).

cnf(c_379,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_344])).

cnf(c_499,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_379,c_2])).

cnf(c_501,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_499,c_290])).

cnf(c_1190,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1152,c_501])).

cnf(c_4579,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_1190,c_51])).

cnf(c_4580,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_1030,c_51])).

cnf(c_4670,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_4580,c_51])).

cnf(c_4671,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_4579,c_4670])).

cnf(c_7643,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_56,c_4671])).

cnf(c_438,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_380,c_2])).

cnf(c_441,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_438,c_290])).

cnf(c_7799,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = X0 ),
    inference(superposition,[status(thm)],[c_7643,c_441])).

cnf(c_24329,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_11674,c_7799])).

cnf(c_473,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_379])).

cnf(c_21514,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0)))),k1_xboole_0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_473,c_90])).

cnf(c_6034,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_5843])).

cnf(c_5783,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1190,c_5739])).

cnf(c_5869,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_5783,c_5843])).

cnf(c_5890,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_5869])).

cnf(c_6236,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_1190,c_5890])).

cnf(c_6985,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_6236,c_5843])).

cnf(c_6989,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_6236,c_1732])).

cnf(c_7002,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_6989,c_4671])).

cnf(c_7005,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_6985,c_7002])).

cnf(c_21559,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_21514,c_6034,c_7005])).

cnf(c_24394,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_24329,c_3,c_256,c_21559])).

cnf(c_5821,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_5739,c_4])).

cnf(c_5848,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_5821,c_4])).

cnf(c_24395,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_24394,c_5848])).

cnf(c_25862,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_25769,c_1732,c_6130,c_24395])).

cnf(c_5965,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5869,c_4])).

cnf(c_5971,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5965,c_4670])).

cnf(c_596,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_413,c_0])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_23,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6,c_4])).

cnf(c_24,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_23])).

cnf(c_1191,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_596,c_24])).

cnf(c_19532,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5971,c_1191])).

cnf(c_1602,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_1008,c_41])).

cnf(c_1608,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
    inference(demodulation,[status(thm)],[c_1602,c_1008])).

cnf(c_306,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_290,c_0])).

cnf(c_1609,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_1608,c_3,c_4,c_306])).

cnf(c_8277,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1609,c_2])).

cnf(c_5950,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_5869,c_4])).

cnf(c_15656,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_5950,c_1030])).

cnf(c_19533,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_19532,c_8277,c_15656])).

cnf(c_32307,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_25862,c_19533])).

cnf(c_32308,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_32307,c_1190])).

cnf(c_32309,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_32308])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.55/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/1.50  
% 7.55/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.50  
% 7.55/1.50  ------  iProver source info
% 7.55/1.50  
% 7.55/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.50  git: non_committed_changes: false
% 7.55/1.50  git: last_make_outside_of_git: false
% 7.55/1.50  
% 7.55/1.50  ------ 
% 7.55/1.50  
% 7.55/1.50  ------ Input Options
% 7.55/1.50  
% 7.55/1.50  --out_options                           all
% 7.55/1.50  --tptp_safe_out                         true
% 7.55/1.50  --problem_path                          ""
% 7.55/1.50  --include_path                          ""
% 7.55/1.50  --clausifier                            res/vclausify_rel
% 7.55/1.50  --clausifier_options                    --mode clausify
% 7.55/1.50  --stdin                                 false
% 7.55/1.50  --stats_out                             all
% 7.55/1.50  
% 7.55/1.50  ------ General Options
% 7.55/1.50  
% 7.55/1.50  --fof                                   false
% 7.55/1.50  --time_out_real                         305.
% 7.55/1.50  --time_out_virtual                      -1.
% 7.55/1.50  --symbol_type_check                     false
% 7.55/1.50  --clausify_out                          false
% 7.55/1.50  --sig_cnt_out                           false
% 7.55/1.50  --trig_cnt_out                          false
% 7.55/1.50  --trig_cnt_out_tolerance                1.
% 7.55/1.50  --trig_cnt_out_sk_spl                   false
% 7.55/1.50  --abstr_cl_out                          false
% 7.55/1.50  
% 7.55/1.50  ------ Global Options
% 7.55/1.50  
% 7.55/1.50  --schedule                              default
% 7.55/1.50  --add_important_lit                     false
% 7.55/1.50  --prop_solver_per_cl                    1000
% 7.55/1.50  --min_unsat_core                        false
% 7.55/1.50  --soft_assumptions                      false
% 7.55/1.50  --soft_lemma_size                       3
% 7.55/1.50  --prop_impl_unit_size                   0
% 7.55/1.50  --prop_impl_unit                        []
% 7.55/1.50  --share_sel_clauses                     true
% 7.55/1.50  --reset_solvers                         false
% 7.55/1.50  --bc_imp_inh                            [conj_cone]
% 7.55/1.50  --conj_cone_tolerance                   3.
% 7.55/1.50  --extra_neg_conj                        none
% 7.55/1.50  --large_theory_mode                     true
% 7.55/1.50  --prolific_symb_bound                   200
% 7.55/1.50  --lt_threshold                          2000
% 7.55/1.50  --clause_weak_htbl                      true
% 7.55/1.50  --gc_record_bc_elim                     false
% 7.55/1.50  
% 7.55/1.50  ------ Preprocessing Options
% 7.55/1.50  
% 7.55/1.50  --preprocessing_flag                    true
% 7.55/1.50  --time_out_prep_mult                    0.1
% 7.55/1.50  --splitting_mode                        input
% 7.55/1.50  --splitting_grd                         true
% 7.55/1.50  --splitting_cvd                         false
% 7.55/1.50  --splitting_cvd_svl                     false
% 7.55/1.50  --splitting_nvd                         32
% 7.55/1.50  --sub_typing                            true
% 7.55/1.50  --prep_gs_sim                           true
% 7.55/1.50  --prep_unflatten                        true
% 7.55/1.50  --prep_res_sim                          true
% 7.55/1.50  --prep_upred                            true
% 7.55/1.50  --prep_sem_filter                       exhaustive
% 7.55/1.50  --prep_sem_filter_out                   false
% 7.55/1.50  --pred_elim                             true
% 7.55/1.50  --res_sim_input                         true
% 7.55/1.50  --eq_ax_congr_red                       true
% 7.55/1.50  --pure_diseq_elim                       true
% 7.55/1.50  --brand_transform                       false
% 7.55/1.50  --non_eq_to_eq                          false
% 7.55/1.50  --prep_def_merge                        true
% 7.55/1.50  --prep_def_merge_prop_impl              false
% 7.55/1.50  --prep_def_merge_mbd                    true
% 7.55/1.50  --prep_def_merge_tr_red                 false
% 7.55/1.50  --prep_def_merge_tr_cl                  false
% 7.55/1.50  --smt_preprocessing                     true
% 7.55/1.50  --smt_ac_axioms                         fast
% 7.55/1.50  --preprocessed_out                      false
% 7.55/1.50  --preprocessed_stats                    false
% 7.55/1.50  
% 7.55/1.50  ------ Abstraction refinement Options
% 7.55/1.50  
% 7.55/1.50  --abstr_ref                             []
% 7.55/1.50  --abstr_ref_prep                        false
% 7.55/1.50  --abstr_ref_until_sat                   false
% 7.55/1.50  --abstr_ref_sig_restrict                funpre
% 7.55/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.50  --abstr_ref_under                       []
% 7.55/1.50  
% 7.55/1.50  ------ SAT Options
% 7.55/1.50  
% 7.55/1.50  --sat_mode                              false
% 7.55/1.50  --sat_fm_restart_options                ""
% 7.55/1.50  --sat_gr_def                            false
% 7.55/1.50  --sat_epr_types                         true
% 7.55/1.50  --sat_non_cyclic_types                  false
% 7.55/1.50  --sat_finite_models                     false
% 7.55/1.50  --sat_fm_lemmas                         false
% 7.55/1.50  --sat_fm_prep                           false
% 7.55/1.50  --sat_fm_uc_incr                        true
% 7.55/1.50  --sat_out_model                         small
% 7.55/1.50  --sat_out_clauses                       false
% 7.55/1.50  
% 7.55/1.50  ------ QBF Options
% 7.55/1.50  
% 7.55/1.50  --qbf_mode                              false
% 7.55/1.50  --qbf_elim_univ                         false
% 7.55/1.50  --qbf_dom_inst                          none
% 7.55/1.50  --qbf_dom_pre_inst                      false
% 7.55/1.50  --qbf_sk_in                             false
% 7.55/1.50  --qbf_pred_elim                         true
% 7.55/1.50  --qbf_split                             512
% 7.55/1.50  
% 7.55/1.50  ------ BMC1 Options
% 7.55/1.50  
% 7.55/1.50  --bmc1_incremental                      false
% 7.55/1.50  --bmc1_axioms                           reachable_all
% 7.55/1.50  --bmc1_min_bound                        0
% 7.55/1.50  --bmc1_max_bound                        -1
% 7.55/1.50  --bmc1_max_bound_default                -1
% 7.55/1.50  --bmc1_symbol_reachability              true
% 7.55/1.50  --bmc1_property_lemmas                  false
% 7.55/1.50  --bmc1_k_induction                      false
% 7.55/1.50  --bmc1_non_equiv_states                 false
% 7.55/1.50  --bmc1_deadlock                         false
% 7.55/1.50  --bmc1_ucm                              false
% 7.55/1.50  --bmc1_add_unsat_core                   none
% 7.55/1.50  --bmc1_unsat_core_children              false
% 7.55/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.50  --bmc1_out_stat                         full
% 7.55/1.50  --bmc1_ground_init                      false
% 7.55/1.50  --bmc1_pre_inst_next_state              false
% 7.55/1.50  --bmc1_pre_inst_state                   false
% 7.55/1.50  --bmc1_pre_inst_reach_state             false
% 7.55/1.50  --bmc1_out_unsat_core                   false
% 7.55/1.50  --bmc1_aig_witness_out                  false
% 7.55/1.50  --bmc1_verbose                          false
% 7.55/1.50  --bmc1_dump_clauses_tptp                false
% 7.55/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.50  --bmc1_dump_file                        -
% 7.55/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.50  --bmc1_ucm_extend_mode                  1
% 7.55/1.50  --bmc1_ucm_init_mode                    2
% 7.55/1.50  --bmc1_ucm_cone_mode                    none
% 7.55/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.50  --bmc1_ucm_relax_model                  4
% 7.55/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.50  --bmc1_ucm_layered_model                none
% 7.55/1.50  --bmc1_ucm_max_lemma_size               10
% 7.55/1.50  
% 7.55/1.50  ------ AIG Options
% 7.55/1.50  
% 7.55/1.50  --aig_mode                              false
% 7.55/1.50  
% 7.55/1.50  ------ Instantiation Options
% 7.55/1.50  
% 7.55/1.50  --instantiation_flag                    true
% 7.55/1.50  --inst_sos_flag                         false
% 7.55/1.50  --inst_sos_phase                        true
% 7.55/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.50  --inst_lit_sel_side                     num_symb
% 7.55/1.50  --inst_solver_per_active                1400
% 7.55/1.50  --inst_solver_calls_frac                1.
% 7.55/1.50  --inst_passive_queue_type               priority_queues
% 7.55/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.50  --inst_passive_queues_freq              [25;2]
% 7.55/1.50  --inst_dismatching                      true
% 7.55/1.50  --inst_eager_unprocessed_to_passive     true
% 7.55/1.50  --inst_prop_sim_given                   true
% 7.55/1.50  --inst_prop_sim_new                     false
% 7.55/1.50  --inst_subs_new                         false
% 7.55/1.50  --inst_eq_res_simp                      false
% 7.55/1.50  --inst_subs_given                       false
% 7.55/1.50  --inst_orphan_elimination               true
% 7.55/1.50  --inst_learning_loop_flag               true
% 7.55/1.50  --inst_learning_start                   3000
% 7.55/1.50  --inst_learning_factor                  2
% 7.55/1.50  --inst_start_prop_sim_after_learn       3
% 7.55/1.50  --inst_sel_renew                        solver
% 7.55/1.50  --inst_lit_activity_flag                true
% 7.55/1.50  --inst_restr_to_given                   false
% 7.55/1.50  --inst_activity_threshold               500
% 7.55/1.50  --inst_out_proof                        true
% 7.55/1.50  
% 7.55/1.50  ------ Resolution Options
% 7.55/1.50  
% 7.55/1.50  --resolution_flag                       true
% 7.55/1.50  --res_lit_sel                           adaptive
% 7.55/1.50  --res_lit_sel_side                      none
% 7.55/1.50  --res_ordering                          kbo
% 7.55/1.50  --res_to_prop_solver                    active
% 7.55/1.50  --res_prop_simpl_new                    false
% 7.55/1.50  --res_prop_simpl_given                  true
% 7.55/1.50  --res_passive_queue_type                priority_queues
% 7.55/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.50  --res_passive_queues_freq               [15;5]
% 7.55/1.50  --res_forward_subs                      full
% 7.55/1.50  --res_backward_subs                     full
% 7.55/1.50  --res_forward_subs_resolution           true
% 7.55/1.50  --res_backward_subs_resolution          true
% 7.55/1.50  --res_orphan_elimination                true
% 7.55/1.50  --res_time_limit                        2.
% 7.55/1.50  --res_out_proof                         true
% 7.55/1.50  
% 7.55/1.50  ------ Superposition Options
% 7.55/1.50  
% 7.55/1.50  --superposition_flag                    true
% 7.55/1.50  --sup_passive_queue_type                priority_queues
% 7.55/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.50  --demod_completeness_check              fast
% 7.55/1.50  --demod_use_ground                      true
% 7.55/1.50  --sup_to_prop_solver                    passive
% 7.55/1.50  --sup_prop_simpl_new                    true
% 7.55/1.50  --sup_prop_simpl_given                  true
% 7.55/1.50  --sup_fun_splitting                     false
% 7.55/1.50  --sup_smt_interval                      50000
% 7.55/1.50  
% 7.55/1.50  ------ Superposition Simplification Setup
% 7.55/1.50  
% 7.55/1.50  --sup_indices_passive                   []
% 7.55/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.50  --sup_full_bw                           [BwDemod]
% 7.55/1.50  --sup_immed_triv                        [TrivRules]
% 7.55/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.50  --sup_immed_bw_main                     []
% 7.55/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.50  
% 7.55/1.50  ------ Combination Options
% 7.55/1.50  
% 7.55/1.50  --comb_res_mult                         3
% 7.55/1.50  --comb_sup_mult                         2
% 7.55/1.50  --comb_inst_mult                        10
% 7.55/1.50  
% 7.55/1.50  ------ Debug Options
% 7.55/1.50  
% 7.55/1.50  --dbg_backtrace                         false
% 7.55/1.50  --dbg_dump_prop_clauses                 false
% 7.55/1.50  --dbg_dump_prop_clauses_file            -
% 7.55/1.50  --dbg_out_stat                          false
% 7.55/1.50  ------ Parsing...
% 7.55/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.50  
% 7.55/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.55/1.50  
% 7.55/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.50  
% 7.55/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.55/1.50  ------ Proving...
% 7.55/1.50  ------ Problem Properties 
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  clauses                                 7
% 7.55/1.50  conjectures                             1
% 7.55/1.50  EPR                                     0
% 7.55/1.50  Horn                                    7
% 7.55/1.50  unary                                   7
% 7.55/1.50  binary                                  0
% 7.55/1.50  lits                                    7
% 7.55/1.50  lits eq                                 7
% 7.55/1.50  fd_pure                                 0
% 7.55/1.50  fd_pseudo                               0
% 7.55/1.50  fd_cond                                 0
% 7.55/1.50  fd_pseudo_cond                          0
% 7.55/1.50  AC symbols                              0
% 7.55/1.50  
% 7.55/1.50  ------ Schedule UEQ
% 7.55/1.50  
% 7.55/1.50  ------ pure equality problem: resolution off 
% 7.55/1.50  
% 7.55/1.50  ------ Option_UEQ Time Limit: Unbounded
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  ------ 
% 7.55/1.50  Current options:
% 7.55/1.50  ------ 
% 7.55/1.50  
% 7.55/1.50  ------ Input Options
% 7.55/1.50  
% 7.55/1.50  --out_options                           all
% 7.55/1.50  --tptp_safe_out                         true
% 7.55/1.50  --problem_path                          ""
% 7.55/1.50  --include_path                          ""
% 7.55/1.50  --clausifier                            res/vclausify_rel
% 7.55/1.50  --clausifier_options                    --mode clausify
% 7.55/1.50  --stdin                                 false
% 7.55/1.50  --stats_out                             all
% 7.55/1.50  
% 7.55/1.50  ------ General Options
% 7.55/1.50  
% 7.55/1.50  --fof                                   false
% 7.55/1.50  --time_out_real                         305.
% 7.55/1.50  --time_out_virtual                      -1.
% 7.55/1.50  --symbol_type_check                     false
% 7.55/1.50  --clausify_out                          false
% 7.55/1.50  --sig_cnt_out                           false
% 7.55/1.50  --trig_cnt_out                          false
% 7.55/1.50  --trig_cnt_out_tolerance                1.
% 7.55/1.50  --trig_cnt_out_sk_spl                   false
% 7.55/1.50  --abstr_cl_out                          false
% 7.55/1.50  
% 7.55/1.50  ------ Global Options
% 7.55/1.50  
% 7.55/1.50  --schedule                              default
% 7.55/1.50  --add_important_lit                     false
% 7.55/1.50  --prop_solver_per_cl                    1000
% 7.55/1.50  --min_unsat_core                        false
% 7.55/1.50  --soft_assumptions                      false
% 7.55/1.50  --soft_lemma_size                       3
% 7.55/1.50  --prop_impl_unit_size                   0
% 7.55/1.50  --prop_impl_unit                        []
% 7.55/1.50  --share_sel_clauses                     true
% 7.55/1.50  --reset_solvers                         false
% 7.55/1.50  --bc_imp_inh                            [conj_cone]
% 7.55/1.50  --conj_cone_tolerance                   3.
% 7.55/1.50  --extra_neg_conj                        none
% 7.55/1.50  --large_theory_mode                     true
% 7.55/1.50  --prolific_symb_bound                   200
% 7.55/1.50  --lt_threshold                          2000
% 7.55/1.50  --clause_weak_htbl                      true
% 7.55/1.50  --gc_record_bc_elim                     false
% 7.55/1.50  
% 7.55/1.50  ------ Preprocessing Options
% 7.55/1.50  
% 7.55/1.50  --preprocessing_flag                    true
% 7.55/1.50  --time_out_prep_mult                    0.1
% 7.55/1.50  --splitting_mode                        input
% 7.55/1.50  --splitting_grd                         true
% 7.55/1.50  --splitting_cvd                         false
% 7.55/1.50  --splitting_cvd_svl                     false
% 7.55/1.50  --splitting_nvd                         32
% 7.55/1.50  --sub_typing                            true
% 7.55/1.50  --prep_gs_sim                           true
% 7.55/1.50  --prep_unflatten                        true
% 7.55/1.50  --prep_res_sim                          true
% 7.55/1.50  --prep_upred                            true
% 7.55/1.50  --prep_sem_filter                       exhaustive
% 7.55/1.50  --prep_sem_filter_out                   false
% 7.55/1.50  --pred_elim                             true
% 7.55/1.50  --res_sim_input                         true
% 7.55/1.50  --eq_ax_congr_red                       true
% 7.55/1.50  --pure_diseq_elim                       true
% 7.55/1.50  --brand_transform                       false
% 7.55/1.50  --non_eq_to_eq                          false
% 7.55/1.50  --prep_def_merge                        true
% 7.55/1.50  --prep_def_merge_prop_impl              false
% 7.55/1.50  --prep_def_merge_mbd                    true
% 7.55/1.50  --prep_def_merge_tr_red                 false
% 7.55/1.50  --prep_def_merge_tr_cl                  false
% 7.55/1.50  --smt_preprocessing                     true
% 7.55/1.50  --smt_ac_axioms                         fast
% 7.55/1.50  --preprocessed_out                      false
% 7.55/1.50  --preprocessed_stats                    false
% 7.55/1.50  
% 7.55/1.50  ------ Abstraction refinement Options
% 7.55/1.50  
% 7.55/1.50  --abstr_ref                             []
% 7.55/1.50  --abstr_ref_prep                        false
% 7.55/1.50  --abstr_ref_until_sat                   false
% 7.55/1.50  --abstr_ref_sig_restrict                funpre
% 7.55/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.50  --abstr_ref_under                       []
% 7.55/1.50  
% 7.55/1.50  ------ SAT Options
% 7.55/1.50  
% 7.55/1.50  --sat_mode                              false
% 7.55/1.50  --sat_fm_restart_options                ""
% 7.55/1.50  --sat_gr_def                            false
% 7.55/1.50  --sat_epr_types                         true
% 7.55/1.50  --sat_non_cyclic_types                  false
% 7.55/1.50  --sat_finite_models                     false
% 7.55/1.50  --sat_fm_lemmas                         false
% 7.55/1.50  --sat_fm_prep                           false
% 7.55/1.50  --sat_fm_uc_incr                        true
% 7.55/1.50  --sat_out_model                         small
% 7.55/1.50  --sat_out_clauses                       false
% 7.55/1.50  
% 7.55/1.50  ------ QBF Options
% 7.55/1.50  
% 7.55/1.50  --qbf_mode                              false
% 7.55/1.50  --qbf_elim_univ                         false
% 7.55/1.50  --qbf_dom_inst                          none
% 7.55/1.50  --qbf_dom_pre_inst                      false
% 7.55/1.50  --qbf_sk_in                             false
% 7.55/1.50  --qbf_pred_elim                         true
% 7.55/1.50  --qbf_split                             512
% 7.55/1.50  
% 7.55/1.50  ------ BMC1 Options
% 7.55/1.50  
% 7.55/1.50  --bmc1_incremental                      false
% 7.55/1.50  --bmc1_axioms                           reachable_all
% 7.55/1.50  --bmc1_min_bound                        0
% 7.55/1.50  --bmc1_max_bound                        -1
% 7.55/1.50  --bmc1_max_bound_default                -1
% 7.55/1.50  --bmc1_symbol_reachability              true
% 7.55/1.50  --bmc1_property_lemmas                  false
% 7.55/1.50  --bmc1_k_induction                      false
% 7.55/1.50  --bmc1_non_equiv_states                 false
% 7.55/1.50  --bmc1_deadlock                         false
% 7.55/1.50  --bmc1_ucm                              false
% 7.55/1.50  --bmc1_add_unsat_core                   none
% 7.55/1.50  --bmc1_unsat_core_children              false
% 7.55/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.50  --bmc1_out_stat                         full
% 7.55/1.50  --bmc1_ground_init                      false
% 7.55/1.50  --bmc1_pre_inst_next_state              false
% 7.55/1.50  --bmc1_pre_inst_state                   false
% 7.55/1.50  --bmc1_pre_inst_reach_state             false
% 7.55/1.50  --bmc1_out_unsat_core                   false
% 7.55/1.50  --bmc1_aig_witness_out                  false
% 7.55/1.50  --bmc1_verbose                          false
% 7.55/1.50  --bmc1_dump_clauses_tptp                false
% 7.55/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.50  --bmc1_dump_file                        -
% 7.55/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.50  --bmc1_ucm_extend_mode                  1
% 7.55/1.50  --bmc1_ucm_init_mode                    2
% 7.55/1.50  --bmc1_ucm_cone_mode                    none
% 7.55/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.50  --bmc1_ucm_relax_model                  4
% 7.55/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.50  --bmc1_ucm_layered_model                none
% 7.55/1.50  --bmc1_ucm_max_lemma_size               10
% 7.55/1.50  
% 7.55/1.50  ------ AIG Options
% 7.55/1.50  
% 7.55/1.50  --aig_mode                              false
% 7.55/1.50  
% 7.55/1.50  ------ Instantiation Options
% 7.55/1.50  
% 7.55/1.50  --instantiation_flag                    false
% 7.55/1.50  --inst_sos_flag                         false
% 7.55/1.50  --inst_sos_phase                        true
% 7.55/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.50  --inst_lit_sel_side                     num_symb
% 7.55/1.50  --inst_solver_per_active                1400
% 7.55/1.50  --inst_solver_calls_frac                1.
% 7.55/1.50  --inst_passive_queue_type               priority_queues
% 7.55/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.50  --inst_passive_queues_freq              [25;2]
% 7.55/1.50  --inst_dismatching                      true
% 7.55/1.50  --inst_eager_unprocessed_to_passive     true
% 7.55/1.50  --inst_prop_sim_given                   true
% 7.55/1.50  --inst_prop_sim_new                     false
% 7.55/1.50  --inst_subs_new                         false
% 7.55/1.50  --inst_eq_res_simp                      false
% 7.55/1.50  --inst_subs_given                       false
% 7.55/1.50  --inst_orphan_elimination               true
% 7.55/1.50  --inst_learning_loop_flag               true
% 7.55/1.50  --inst_learning_start                   3000
% 7.55/1.50  --inst_learning_factor                  2
% 7.55/1.50  --inst_start_prop_sim_after_learn       3
% 7.55/1.50  --inst_sel_renew                        solver
% 7.55/1.50  --inst_lit_activity_flag                true
% 7.55/1.50  --inst_restr_to_given                   false
% 7.55/1.50  --inst_activity_threshold               500
% 7.55/1.50  --inst_out_proof                        true
% 7.55/1.50  
% 7.55/1.50  ------ Resolution Options
% 7.55/1.50  
% 7.55/1.50  --resolution_flag                       false
% 7.55/1.50  --res_lit_sel                           adaptive
% 7.55/1.50  --res_lit_sel_side                      none
% 7.55/1.50  --res_ordering                          kbo
% 7.55/1.50  --res_to_prop_solver                    active
% 7.55/1.50  --res_prop_simpl_new                    false
% 7.55/1.50  --res_prop_simpl_given                  true
% 7.55/1.50  --res_passive_queue_type                priority_queues
% 7.55/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.50  --res_passive_queues_freq               [15;5]
% 7.55/1.50  --res_forward_subs                      full
% 7.55/1.50  --res_backward_subs                     full
% 7.55/1.50  --res_forward_subs_resolution           true
% 7.55/1.50  --res_backward_subs_resolution          true
% 7.55/1.50  --res_orphan_elimination                true
% 7.55/1.50  --res_time_limit                        2.
% 7.55/1.50  --res_out_proof                         true
% 7.55/1.50  
% 7.55/1.50  ------ Superposition Options
% 7.55/1.50  
% 7.55/1.50  --superposition_flag                    true
% 7.55/1.50  --sup_passive_queue_type                priority_queues
% 7.55/1.50  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.50  --demod_completeness_check              fast
% 7.55/1.50  --demod_use_ground                      true
% 7.55/1.50  --sup_to_prop_solver                    active
% 7.55/1.50  --sup_prop_simpl_new                    false
% 7.55/1.50  --sup_prop_simpl_given                  false
% 7.55/1.50  --sup_fun_splitting                     true
% 7.55/1.50  --sup_smt_interval                      10000
% 7.55/1.50  
% 7.55/1.50  ------ Superposition Simplification Setup
% 7.55/1.50  
% 7.55/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.55/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.55/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.50  --sup_full_triv                         [TrivRules]
% 7.55/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.55/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.55/1.50  --sup_immed_triv                        [TrivRules]
% 7.55/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.50  --sup_immed_bw_main                     []
% 7.55/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.55/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.50  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.55/1.50  
% 7.55/1.50  ------ Combination Options
% 7.55/1.50  
% 7.55/1.50  --comb_res_mult                         1
% 7.55/1.50  --comb_sup_mult                         1
% 7.55/1.50  --comb_inst_mult                        1000000
% 7.55/1.50  
% 7.55/1.50  ------ Debug Options
% 7.55/1.50  
% 7.55/1.50  --dbg_backtrace                         false
% 7.55/1.50  --dbg_dump_prop_clauses                 false
% 7.55/1.50  --dbg_dump_prop_clauses_file            -
% 7.55/1.50  --dbg_out_stat                          false
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  ------ Proving...
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  % SZS status Theorem for theBenchmark.p
% 7.55/1.50  
% 7.55/1.50   Resolution empty clause
% 7.55/1.50  
% 7.55/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.50  
% 7.55/1.50  fof(f1,axiom,(
% 7.55/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f14,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.55/1.50    inference(cnf_transformation,[],[f1])).
% 7.55/1.50  
% 7.55/1.50  fof(f8,axiom,(
% 7.55/1.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f21,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.55/1.50    inference(cnf_transformation,[],[f8])).
% 7.55/1.50  
% 7.55/1.50  fof(f7,axiom,(
% 7.55/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f20,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.55/1.50    inference(cnf_transformation,[],[f7])).
% 7.55/1.50  
% 7.55/1.50  fof(f24,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.55/1.50    inference(definition_unfolding,[],[f21,f20])).
% 7.55/1.50  
% 7.55/1.50  fof(f5,axiom,(
% 7.55/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f18,plain,(
% 7.55/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.55/1.50    inference(cnf_transformation,[],[f5])).
% 7.55/1.50  
% 7.55/1.50  fof(f2,axiom,(
% 7.55/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f15,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.55/1.50    inference(cnf_transformation,[],[f2])).
% 7.55/1.50  
% 7.55/1.50  fof(f23,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.55/1.50    inference(definition_unfolding,[],[f15,f20,f20])).
% 7.55/1.50  
% 7.55/1.50  fof(f6,axiom,(
% 7.55/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f19,plain,(
% 7.55/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.55/1.50    inference(cnf_transformation,[],[f6])).
% 7.55/1.50  
% 7.55/1.50  fof(f4,axiom,(
% 7.55/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f17,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.55/1.50    inference(cnf_transformation,[],[f4])).
% 7.55/1.50  
% 7.55/1.50  fof(f9,conjecture,(
% 7.55/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f10,negated_conjecture,(
% 7.55/1.50    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.55/1.50    inference(negated_conjecture,[],[f9])).
% 7.55/1.50  
% 7.55/1.50  fof(f11,plain,(
% 7.55/1.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.55/1.50    inference(ennf_transformation,[],[f10])).
% 7.55/1.50  
% 7.55/1.50  fof(f12,plain,(
% 7.55/1.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.55/1.50    introduced(choice_axiom,[])).
% 7.55/1.50  
% 7.55/1.50  fof(f13,plain,(
% 7.55/1.50    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.55/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 7.55/1.50  
% 7.55/1.50  fof(f22,plain,(
% 7.55/1.50    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.55/1.50    inference(cnf_transformation,[],[f13])).
% 7.55/1.50  
% 7.55/1.50  fof(f3,axiom,(
% 7.55/1.50    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.55/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.50  
% 7.55/1.50  fof(f16,plain,(
% 7.55/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.55/1.50    inference(cnf_transformation,[],[f3])).
% 7.55/1.50  
% 7.55/1.50  fof(f25,plain,(
% 7.55/1.50    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 7.55/1.50    inference(definition_unfolding,[],[f22,f16,f16,f20])).
% 7.55/1.50  
% 7.55/1.50  cnf(c_0,plain,
% 7.55/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(cnf_transformation,[],[f14]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.55/1.50      inference(cnf_transformation,[],[f24]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_3,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.55/1.50      inference(cnf_transformation,[],[f18]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.55/1.50      inference(cnf_transformation,[],[f23]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_25,plain,
% 7.55/1.50      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_93,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_25,c_5]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_192,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_25,c_93]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.55/1.50      inference(cnf_transformation,[],[f19]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_202,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_192,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_2,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(cnf_transformation,[],[f17]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_33,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_25,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_53,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_203,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k1_xboole_0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_202,c_2,c_33,c_53]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_224,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_203,c_53]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_225,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_224,c_3]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_256,plain,
% 7.55/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_225,c_25]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_339,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_256,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_344,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_339,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_380,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_5,c_344]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_434,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_380,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_27,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_276,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_225,c_27]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_102,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_116,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_102,c_0]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_124,plain,
% 7.55/1.50      ( k2_xboole_0(X0,X0) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_116,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_290,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_276,c_3,c_124]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_308,plain,
% 7.55/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_290,c_203]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_445,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_434,c_4,c_308]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_755,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_0,c_445]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1387,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_755,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1391,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_1387,c_290]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_390,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_344,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_392,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_390,c_290]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_527,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_0,c_392]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_336,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_256,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_348,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_336,c_308]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1008,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_527,c_348]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_51,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4565,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1008,c_51]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4677,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_4565,c_290]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5357,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X2),X0) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4677,c_755]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5371,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_5357,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_13771,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1391,c_5371]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_90,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_25769,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0),k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(X2,X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_13771,c_90]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_995,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_2,c_527]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1030,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_995,c_527]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1732,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1030,c_0]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_537,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_392,c_0]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5339,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4677,c_537]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5377,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_5339,c_4677]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_41,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5725,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_5377,c_41]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5739,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_5725,c_3,c_344]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5829,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_5739,c_1]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5843,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_5829,c_3,c_348]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_6064,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1008,c_5843]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1013,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_527,c_0]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1432,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1013,c_537]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1446,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_1432,c_1013]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_6130,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_6064,c_1446]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4541,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_380,c_51]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4708,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_4541,c_290]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4709,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_4708,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_11674,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),X1) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4709,c_344]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_52,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_56,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_52,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_411,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_348,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_413,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_411,c_290]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_580,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_0,c_413]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1152,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_2,c_580]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_379,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_2,c_344]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_499,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_379,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_501,plain,
% 7.55/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_499,c_290]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1190,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_1152,c_501]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4579,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1190,c_51]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4580,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1030,c_51]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4670,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_4580,c_51]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_4671,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_4579,c_4670]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_7643,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_56,c_4671]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_438,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_380,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_441,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_438,c_290]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_7799,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_7643,c_441]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_24329,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_11674,c_7799]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_473,plain,
% 7.55/1.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4,c_379]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_21514,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0)))),k1_xboole_0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_473,c_90]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_6034,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4,c_5843]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5783,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1190,c_5739]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5869,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_5783,c_5843]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5890,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_4,c_5869]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_6236,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1190,c_5890]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_6985,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_6236,c_5843]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_6989,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_6236,c_1732]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_7002,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_6989,c_4671]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_7005,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_6985,c_7002]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_21559,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_21514,c_6034,c_7005]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_24394,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_24329,c_3,c_256,c_21559]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5821,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_5739,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5848,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_5821,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_24395,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.55/1.50      inference(light_normalisation,[status(thm)],[c_24394,c_5848]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_25862,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_25769,c_1732,c_6130,c_24395]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5965,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_5869,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5971,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_5965,c_4670]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_596,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_413,c_0]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_6,negated_conjecture,
% 7.55/1.50      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 7.55/1.50      inference(cnf_transformation,[],[f25]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_23,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_6,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_24,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_0,c_23]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1191,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_596,c_24]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_19532,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_5971,c_1191]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1602,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1008,c_41]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1608,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_1602,c_1008]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_306,plain,
% 7.55/1.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_290,c_0]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_1609,plain,
% 7.55/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_1608,c_3,c_4,c_306]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_8277,plain,
% 7.55/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_1609,c_2]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_5950,plain,
% 7.55/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_5869,c_4]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_15656,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.55/1.50      inference(superposition,[status(thm)],[c_5950,c_1030]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_19533,plain,
% 7.55/1.50      ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_19532,c_8277,c_15656]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_32307,plain,
% 7.55/1.50      ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) != k2_xboole_0(sK0,sK1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_25862,c_19533]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_32308,plain,
% 7.55/1.50      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 7.55/1.50      inference(demodulation,[status(thm)],[c_32307,c_1190]) ).
% 7.55/1.50  
% 7.55/1.50  cnf(c_32309,plain,
% 7.55/1.50      ( $false ),
% 7.55/1.50      inference(equality_resolution_simp,[status(thm)],[c_32308]) ).
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.50  
% 7.55/1.50  ------                               Statistics
% 7.55/1.50  
% 7.55/1.50  ------ General
% 7.55/1.50  
% 7.55/1.50  abstr_ref_over_cycles:                  0
% 7.55/1.50  abstr_ref_under_cycles:                 0
% 7.55/1.50  gc_basic_clause_elim:                   0
% 7.55/1.50  forced_gc_time:                         0
% 7.55/1.50  parsing_time:                           0.008
% 7.55/1.50  unif_index_cands_time:                  0.
% 7.55/1.50  unif_index_add_time:                    0.
% 7.55/1.50  orderings_time:                         0.
% 7.55/1.50  out_proof_time:                         0.007
% 7.55/1.50  total_time:                             0.873
% 7.55/1.50  num_of_symbols:                         38
% 7.55/1.50  num_of_terms:                           43722
% 7.55/1.50  
% 7.55/1.50  ------ Preprocessing
% 7.55/1.50  
% 7.55/1.50  num_of_splits:                          0
% 7.55/1.50  num_of_split_atoms:                     2
% 7.55/1.50  num_of_reused_defs:                     6
% 7.55/1.50  num_eq_ax_congr_red:                    0
% 7.55/1.50  num_of_sem_filtered_clauses:            0
% 7.55/1.50  num_of_subtypes:                        0
% 7.55/1.50  monotx_restored_types:                  0
% 7.55/1.50  sat_num_of_epr_types:                   0
% 7.55/1.50  sat_num_of_non_cyclic_types:            0
% 7.55/1.50  sat_guarded_non_collapsed_types:        0
% 7.55/1.50  num_pure_diseq_elim:                    0
% 7.55/1.50  simp_replaced_by:                       0
% 7.55/1.50  res_preprocessed:                       18
% 7.55/1.50  prep_upred:                             0
% 7.55/1.50  prep_unflattend:                        0
% 7.55/1.50  smt_new_axioms:                         0
% 7.55/1.50  pred_elim_cands:                        0
% 7.55/1.50  pred_elim:                              0
% 7.55/1.50  pred_elim_cl:                           0
% 7.55/1.50  pred_elim_cycles:                       0
% 7.55/1.50  merged_defs:                            0
% 7.55/1.50  merged_defs_ncl:                        0
% 7.55/1.50  bin_hyper_res:                          0
% 7.55/1.50  prep_cycles:                            2
% 7.55/1.50  pred_elim_time:                         0.
% 7.55/1.50  splitting_time:                         0.
% 7.55/1.50  sem_filter_time:                        0.
% 7.55/1.50  monotx_time:                            0.001
% 7.55/1.50  subtype_inf_time:                       0.
% 7.55/1.50  
% 7.55/1.50  ------ Problem properties
% 7.55/1.50  
% 7.55/1.50  clauses:                                7
% 7.55/1.50  conjectures:                            1
% 7.55/1.50  epr:                                    0
% 7.55/1.50  horn:                                   7
% 7.55/1.50  ground:                                 1
% 7.55/1.50  unary:                                  7
% 7.55/1.50  binary:                                 0
% 7.55/1.50  lits:                                   7
% 7.55/1.50  lits_eq:                                7
% 7.55/1.50  fd_pure:                                0
% 7.55/1.50  fd_pseudo:                              0
% 7.55/1.50  fd_cond:                                0
% 7.55/1.50  fd_pseudo_cond:                         0
% 7.55/1.50  ac_symbols:                             0
% 7.55/1.50  
% 7.55/1.50  ------ Propositional Solver
% 7.55/1.50  
% 7.55/1.50  prop_solver_calls:                      13
% 7.55/1.50  prop_fast_solver_calls:                 48
% 7.55/1.50  smt_solver_calls:                       0
% 7.55/1.50  smt_fast_solver_calls:                  0
% 7.55/1.50  prop_num_of_clauses:                    299
% 7.55/1.50  prop_preprocess_simplified:             304
% 7.55/1.50  prop_fo_subsumed:                       0
% 7.55/1.50  prop_solver_time:                       0.
% 7.55/1.50  smt_solver_time:                        0.
% 7.55/1.50  smt_fast_solver_time:                   0.
% 7.55/1.50  prop_fast_solver_time:                  0.
% 7.55/1.50  prop_unsat_core_time:                   0.
% 7.55/1.50  
% 7.55/1.50  ------ QBF
% 7.55/1.50  
% 7.55/1.50  qbf_q_res:                              0
% 7.55/1.50  qbf_num_tautologies:                    0
% 7.55/1.50  qbf_prep_cycles:                        0
% 7.55/1.50  
% 7.55/1.50  ------ BMC1
% 7.55/1.50  
% 7.55/1.50  bmc1_current_bound:                     -1
% 7.55/1.50  bmc1_last_solved_bound:                 -1
% 7.55/1.50  bmc1_unsat_core_size:                   -1
% 7.55/1.50  bmc1_unsat_core_parents_size:           -1
% 7.55/1.50  bmc1_merge_next_fun:                    0
% 7.55/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.55/1.50  
% 7.55/1.50  ------ Instantiation
% 7.55/1.50  
% 7.55/1.50  inst_num_of_clauses:                    0
% 7.55/1.50  inst_num_in_passive:                    0
% 7.55/1.50  inst_num_in_active:                     0
% 7.55/1.50  inst_num_in_unprocessed:                0
% 7.55/1.50  inst_num_of_loops:                      0
% 7.55/1.50  inst_num_of_learning_restarts:          0
% 7.55/1.50  inst_num_moves_active_passive:          0
% 7.55/1.50  inst_lit_activity:                      0
% 7.55/1.50  inst_lit_activity_moves:                0
% 7.55/1.50  inst_num_tautologies:                   0
% 7.55/1.50  inst_num_prop_implied:                  0
% 7.55/1.50  inst_num_existing_simplified:           0
% 7.55/1.50  inst_num_eq_res_simplified:             0
% 7.55/1.50  inst_num_child_elim:                    0
% 7.55/1.50  inst_num_of_dismatching_blockings:      0
% 7.55/1.50  inst_num_of_non_proper_insts:           0
% 7.55/1.50  inst_num_of_duplicates:                 0
% 7.55/1.50  inst_inst_num_from_inst_to_res:         0
% 7.55/1.50  inst_dismatching_checking_time:         0.
% 7.55/1.50  
% 7.55/1.50  ------ Resolution
% 7.55/1.50  
% 7.55/1.50  res_num_of_clauses:                     0
% 7.55/1.50  res_num_in_passive:                     0
% 7.55/1.50  res_num_in_active:                      0
% 7.55/1.50  res_num_of_loops:                       20
% 7.55/1.50  res_forward_subset_subsumed:            0
% 7.55/1.50  res_backward_subset_subsumed:           0
% 7.55/1.50  res_forward_subsumed:                   0
% 7.55/1.50  res_backward_subsumed:                  0
% 7.55/1.50  res_forward_subsumption_resolution:     0
% 7.55/1.50  res_backward_subsumption_resolution:    0
% 7.55/1.50  res_clause_to_clause_subsumption:       69610
% 7.55/1.50  res_orphan_elimination:                 0
% 7.55/1.50  res_tautology_del:                      0
% 7.55/1.50  res_num_eq_res_simplified:              0
% 7.55/1.50  res_num_sel_changes:                    0
% 7.55/1.50  res_moves_from_active_to_pass:          0
% 7.55/1.50  
% 7.55/1.50  ------ Superposition
% 7.55/1.50  
% 7.55/1.50  sup_time_total:                         0.
% 7.55/1.50  sup_time_generating:                    0.
% 7.55/1.50  sup_time_sim_full:                      0.
% 7.55/1.50  sup_time_sim_immed:                     0.
% 7.55/1.50  
% 7.55/1.50  sup_num_of_clauses:                     2833
% 7.55/1.50  sup_num_in_active:                      145
% 7.55/1.50  sup_num_in_passive:                     2688
% 7.55/1.50  sup_num_of_loops:                       179
% 7.55/1.50  sup_fw_superposition:                   13318
% 7.55/1.50  sup_bw_superposition:                   9578
% 7.55/1.50  sup_immediate_simplified:               9763
% 7.55/1.50  sup_given_eliminated:                   4
% 7.55/1.50  comparisons_done:                       0
% 7.55/1.50  comparisons_avoided:                    0
% 7.55/1.50  
% 7.55/1.50  ------ Simplifications
% 7.55/1.50  
% 7.55/1.50  
% 7.55/1.50  sim_fw_subset_subsumed:                 0
% 7.55/1.50  sim_bw_subset_subsumed:                 0
% 7.55/1.50  sim_fw_subsumed:                        1842
% 7.55/1.50  sim_bw_subsumed:                        41
% 7.55/1.50  sim_fw_subsumption_res:                 0
% 7.55/1.50  sim_bw_subsumption_res:                 0
% 7.55/1.50  sim_tautology_del:                      0
% 7.55/1.50  sim_eq_tautology_del:                   2808
% 7.55/1.50  sim_eq_res_simp:                        0
% 7.55/1.50  sim_fw_demodulated:                     5671
% 7.55/1.50  sim_bw_demodulated:                     69
% 7.55/1.50  sim_light_normalised:                   3533
% 7.55/1.50  sim_joinable_taut:                      0
% 7.55/1.50  sim_joinable_simp:                      0
% 7.55/1.50  sim_ac_normalised:                      0
% 7.55/1.50  sim_smt_subsumption:                    0
% 7.55/1.50  
%------------------------------------------------------------------------------
