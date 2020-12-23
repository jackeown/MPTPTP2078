%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:14 EST 2020

% Result     : Theorem 23.79s
% Output     : CNFRefutation 23.79s
% Verified   : 
% Statistics : Number of formulae       :   95 (4342 expanded)
%              Number of clauses        :   65 ( 907 expanded)
%              Number of leaves         :   11 (1335 expanded)
%              Depth                    :   28
%              Number of atoms          :   96 (4343 expanded)
%              Number of equality atoms :   95 (4342 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f16,f25,f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f15,f20,f20])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f24,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f24,f25])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_311,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_511,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_311,c_3])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_508,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_311,c_2])).

cnf(c_1001,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_511,c_508])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1021,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1001,c_1])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1024,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1001,c_0])).

cnf(c_1051,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1021,c_1024])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1053,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1051,c_2,c_5,c_508])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1498,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1053,c_6])).

cnf(c_1500,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_1498,c_5])).

cnf(c_1528,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_1500,c_3])).

cnf(c_1541,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1528,c_2])).

cnf(c_1824,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1500,c_1541])).

cnf(c_1858,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1824,c_2])).

cnf(c_445,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_450,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_445,c_3])).

cnf(c_3145,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X1) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_450])).

cnf(c_3260,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3145,c_3])).

cnf(c_3261,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3260,c_2])).

cnf(c_4814,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_508,c_3261])).

cnf(c_4864,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_3261,c_0])).

cnf(c_4998,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(demodulation,[status(thm)],[c_4814,c_4864])).

cnf(c_164,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_4855,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3261,c_164])).

cnf(c_5001,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k1_xboole_0,X2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4998,c_4855])).

cnf(c_5004,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5001,c_450])).

cnf(c_704,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_508,c_1])).

cnf(c_713,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_704,c_508])).

cnf(c_715,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_713,c_2,c_5,c_508])).

cnf(c_5005,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5004,c_2,c_450,c_715])).

cnf(c_5146,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_5005])).

cnf(c_6388,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_5146])).

cnf(c_9482,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(k4_xboole_0(X1,X0),X2))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3261,c_6388])).

cnf(c_9698,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9482,c_450])).

cnf(c_9699,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9698,c_2,c_5005])).

cnf(c_9804,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1858,c_9699])).

cnf(c_9891,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9699,c_1])).

cnf(c_9942,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(demodulation,[status(thm)],[c_9891,c_1,c_5])).

cnf(c_10066,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9804,c_9942])).

cnf(c_10069,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10066,c_5])).

cnf(c_16733,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_10069,c_1])).

cnf(c_16791,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_16733,c_1])).

cnf(c_162,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_3171,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_450,c_162])).

cnf(c_3193,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3171,c_450])).

cnf(c_3175,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_450,c_508])).

cnf(c_3194,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3193,c_3175])).

cnf(c_3196,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3194,c_5])).

cnf(c_9881,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9699,c_3196])).

cnf(c_9959,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9881,c_5,c_450])).

cnf(c_10903,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9959,c_0])).

cnf(c_10969,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10903,c_2,c_9699])).

cnf(c_11283,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)),X2)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10969,c_3261])).

cnf(c_11294,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11283,c_2])).

cnf(c_16792,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_16791,c_5,c_508,c_11294])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_70774,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_16792,c_7])).

cnf(c_70776,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_70774])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:06:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 23.79/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.79/3.49  
% 23.79/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.79/3.49  
% 23.79/3.49  ------  iProver source info
% 23.79/3.49  
% 23.79/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.79/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.79/3.49  git: non_committed_changes: false
% 23.79/3.49  git: last_make_outside_of_git: false
% 23.79/3.49  
% 23.79/3.49  ------ 
% 23.79/3.49  
% 23.79/3.49  ------ Input Options
% 23.79/3.49  
% 23.79/3.49  --out_options                           all
% 23.79/3.49  --tptp_safe_out                         true
% 23.79/3.49  --problem_path                          ""
% 23.79/3.49  --include_path                          ""
% 23.79/3.49  --clausifier                            res/vclausify_rel
% 23.79/3.49  --clausifier_options                    --mode clausify
% 23.79/3.49  --stdin                                 false
% 23.79/3.49  --stats_out                             sel
% 23.79/3.49  
% 23.79/3.49  ------ General Options
% 23.79/3.49  
% 23.79/3.49  --fof                                   false
% 23.79/3.49  --time_out_real                         604.99
% 23.79/3.49  --time_out_virtual                      -1.
% 23.79/3.49  --symbol_type_check                     false
% 23.79/3.49  --clausify_out                          false
% 23.79/3.49  --sig_cnt_out                           false
% 23.79/3.49  --trig_cnt_out                          false
% 23.79/3.49  --trig_cnt_out_tolerance                1.
% 23.79/3.49  --trig_cnt_out_sk_spl                   false
% 23.79/3.49  --abstr_cl_out                          false
% 23.79/3.49  
% 23.79/3.49  ------ Global Options
% 23.79/3.49  
% 23.79/3.49  --schedule                              none
% 23.79/3.49  --add_important_lit                     false
% 23.79/3.49  --prop_solver_per_cl                    1000
% 23.79/3.49  --min_unsat_core                        false
% 23.79/3.49  --soft_assumptions                      false
% 23.79/3.49  --soft_lemma_size                       3
% 23.79/3.49  --prop_impl_unit_size                   0
% 23.79/3.49  --prop_impl_unit                        []
% 23.79/3.49  --share_sel_clauses                     true
% 23.79/3.49  --reset_solvers                         false
% 23.79/3.49  --bc_imp_inh                            [conj_cone]
% 23.79/3.49  --conj_cone_tolerance                   3.
% 23.79/3.49  --extra_neg_conj                        none
% 23.79/3.49  --large_theory_mode                     true
% 23.79/3.49  --prolific_symb_bound                   200
% 23.79/3.49  --lt_threshold                          2000
% 23.79/3.49  --clause_weak_htbl                      true
% 23.79/3.49  --gc_record_bc_elim                     false
% 23.79/3.49  
% 23.79/3.49  ------ Preprocessing Options
% 23.79/3.49  
% 23.79/3.49  --preprocessing_flag                    true
% 23.79/3.49  --time_out_prep_mult                    0.1
% 23.79/3.49  --splitting_mode                        input
% 23.79/3.49  --splitting_grd                         true
% 23.79/3.49  --splitting_cvd                         false
% 23.79/3.49  --splitting_cvd_svl                     false
% 23.79/3.49  --splitting_nvd                         32
% 23.79/3.49  --sub_typing                            true
% 23.79/3.49  --prep_gs_sim                           false
% 23.79/3.49  --prep_unflatten                        true
% 23.79/3.49  --prep_res_sim                          true
% 23.79/3.49  --prep_upred                            true
% 23.79/3.49  --prep_sem_filter                       exhaustive
% 23.79/3.49  --prep_sem_filter_out                   false
% 23.79/3.49  --pred_elim                             false
% 23.79/3.49  --res_sim_input                         true
% 23.79/3.49  --eq_ax_congr_red                       true
% 23.79/3.49  --pure_diseq_elim                       true
% 23.79/3.49  --brand_transform                       false
% 23.79/3.49  --non_eq_to_eq                          false
% 23.79/3.49  --prep_def_merge                        true
% 23.79/3.49  --prep_def_merge_prop_impl              false
% 23.79/3.49  --prep_def_merge_mbd                    true
% 23.79/3.49  --prep_def_merge_tr_red                 false
% 23.79/3.49  --prep_def_merge_tr_cl                  false
% 23.79/3.49  --smt_preprocessing                     true
% 23.79/3.49  --smt_ac_axioms                         fast
% 23.79/3.49  --preprocessed_out                      false
% 23.79/3.49  --preprocessed_stats                    false
% 23.79/3.49  
% 23.79/3.49  ------ Abstraction refinement Options
% 23.79/3.49  
% 23.79/3.49  --abstr_ref                             []
% 23.79/3.49  --abstr_ref_prep                        false
% 23.79/3.49  --abstr_ref_until_sat                   false
% 23.79/3.49  --abstr_ref_sig_restrict                funpre
% 23.79/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.79/3.49  --abstr_ref_under                       []
% 23.79/3.49  
% 23.79/3.49  ------ SAT Options
% 23.79/3.49  
% 23.79/3.49  --sat_mode                              false
% 23.79/3.49  --sat_fm_restart_options                ""
% 23.79/3.49  --sat_gr_def                            false
% 23.79/3.49  --sat_epr_types                         true
% 23.79/3.49  --sat_non_cyclic_types                  false
% 23.79/3.49  --sat_finite_models                     false
% 23.79/3.49  --sat_fm_lemmas                         false
% 23.79/3.49  --sat_fm_prep                           false
% 23.79/3.49  --sat_fm_uc_incr                        true
% 23.79/3.49  --sat_out_model                         small
% 23.79/3.49  --sat_out_clauses                       false
% 23.79/3.49  
% 23.79/3.49  ------ QBF Options
% 23.79/3.49  
% 23.79/3.49  --qbf_mode                              false
% 23.79/3.49  --qbf_elim_univ                         false
% 23.79/3.49  --qbf_dom_inst                          none
% 23.79/3.49  --qbf_dom_pre_inst                      false
% 23.79/3.49  --qbf_sk_in                             false
% 23.79/3.49  --qbf_pred_elim                         true
% 23.79/3.49  --qbf_split                             512
% 23.79/3.49  
% 23.79/3.49  ------ BMC1 Options
% 23.79/3.49  
% 23.79/3.49  --bmc1_incremental                      false
% 23.79/3.49  --bmc1_axioms                           reachable_all
% 23.79/3.49  --bmc1_min_bound                        0
% 23.79/3.49  --bmc1_max_bound                        -1
% 23.79/3.49  --bmc1_max_bound_default                -1
% 23.79/3.49  --bmc1_symbol_reachability              true
% 23.79/3.49  --bmc1_property_lemmas                  false
% 23.79/3.49  --bmc1_k_induction                      false
% 23.79/3.49  --bmc1_non_equiv_states                 false
% 23.79/3.49  --bmc1_deadlock                         false
% 23.79/3.49  --bmc1_ucm                              false
% 23.79/3.49  --bmc1_add_unsat_core                   none
% 23.79/3.49  --bmc1_unsat_core_children              false
% 23.79/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.79/3.49  --bmc1_out_stat                         full
% 23.79/3.49  --bmc1_ground_init                      false
% 23.79/3.49  --bmc1_pre_inst_next_state              false
% 23.79/3.49  --bmc1_pre_inst_state                   false
% 23.79/3.49  --bmc1_pre_inst_reach_state             false
% 23.79/3.49  --bmc1_out_unsat_core                   false
% 23.79/3.49  --bmc1_aig_witness_out                  false
% 23.79/3.49  --bmc1_verbose                          false
% 23.79/3.49  --bmc1_dump_clauses_tptp                false
% 23.79/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.79/3.49  --bmc1_dump_file                        -
% 23.79/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.79/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.79/3.49  --bmc1_ucm_extend_mode                  1
% 23.79/3.49  --bmc1_ucm_init_mode                    2
% 23.79/3.49  --bmc1_ucm_cone_mode                    none
% 23.79/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.79/3.49  --bmc1_ucm_relax_model                  4
% 23.79/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.79/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.79/3.49  --bmc1_ucm_layered_model                none
% 23.79/3.49  --bmc1_ucm_max_lemma_size               10
% 23.79/3.49  
% 23.79/3.49  ------ AIG Options
% 23.79/3.49  
% 23.79/3.49  --aig_mode                              false
% 23.79/3.49  
% 23.79/3.49  ------ Instantiation Options
% 23.79/3.49  
% 23.79/3.49  --instantiation_flag                    true
% 23.79/3.49  --inst_sos_flag                         false
% 23.79/3.49  --inst_sos_phase                        true
% 23.79/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.79/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.79/3.49  --inst_lit_sel_side                     num_symb
% 23.79/3.49  --inst_solver_per_active                1400
% 23.79/3.49  --inst_solver_calls_frac                1.
% 23.79/3.49  --inst_passive_queue_type               priority_queues
% 23.79/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.79/3.49  --inst_passive_queues_freq              [25;2]
% 23.79/3.49  --inst_dismatching                      true
% 23.79/3.49  --inst_eager_unprocessed_to_passive     true
% 23.79/3.49  --inst_prop_sim_given                   true
% 23.79/3.49  --inst_prop_sim_new                     false
% 23.79/3.49  --inst_subs_new                         false
% 23.79/3.49  --inst_eq_res_simp                      false
% 23.79/3.49  --inst_subs_given                       false
% 23.79/3.49  --inst_orphan_elimination               true
% 23.79/3.49  --inst_learning_loop_flag               true
% 23.79/3.49  --inst_learning_start                   3000
% 23.79/3.49  --inst_learning_factor                  2
% 23.79/3.49  --inst_start_prop_sim_after_learn       3
% 23.79/3.49  --inst_sel_renew                        solver
% 23.79/3.49  --inst_lit_activity_flag                true
% 23.79/3.49  --inst_restr_to_given                   false
% 23.79/3.49  --inst_activity_threshold               500
% 23.79/3.49  --inst_out_proof                        true
% 23.79/3.49  
% 23.79/3.49  ------ Resolution Options
% 23.79/3.49  
% 23.79/3.49  --resolution_flag                       true
% 23.79/3.49  --res_lit_sel                           adaptive
% 23.79/3.49  --res_lit_sel_side                      none
% 23.79/3.49  --res_ordering                          kbo
% 23.79/3.49  --res_to_prop_solver                    active
% 23.79/3.49  --res_prop_simpl_new                    false
% 23.79/3.49  --res_prop_simpl_given                  true
% 23.79/3.49  --res_passive_queue_type                priority_queues
% 23.79/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.79/3.49  --res_passive_queues_freq               [15;5]
% 23.79/3.49  --res_forward_subs                      full
% 23.79/3.49  --res_backward_subs                     full
% 23.79/3.49  --res_forward_subs_resolution           true
% 23.79/3.49  --res_backward_subs_resolution          true
% 23.79/3.49  --res_orphan_elimination                true
% 23.79/3.49  --res_time_limit                        2.
% 23.79/3.49  --res_out_proof                         true
% 23.79/3.49  
% 23.79/3.49  ------ Superposition Options
% 23.79/3.49  
% 23.79/3.49  --superposition_flag                    true
% 23.79/3.49  --sup_passive_queue_type                priority_queues
% 23.79/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.79/3.49  --sup_passive_queues_freq               [1;4]
% 23.79/3.49  --demod_completeness_check              fast
% 23.79/3.49  --demod_use_ground                      true
% 23.79/3.49  --sup_to_prop_solver                    passive
% 23.79/3.49  --sup_prop_simpl_new                    true
% 23.79/3.49  --sup_prop_simpl_given                  true
% 23.79/3.49  --sup_fun_splitting                     false
% 23.79/3.49  --sup_smt_interval                      50000
% 23.79/3.49  
% 23.79/3.49  ------ Superposition Simplification Setup
% 23.79/3.49  
% 23.79/3.49  --sup_indices_passive                   []
% 23.79/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.79/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.79/3.49  --sup_full_bw                           [BwDemod]
% 23.79/3.49  --sup_immed_triv                        [TrivRules]
% 23.79/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.79/3.49  --sup_immed_bw_main                     []
% 23.79/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.79/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.79/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.79/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.79/3.49  
% 23.79/3.49  ------ Combination Options
% 23.79/3.49  
% 23.79/3.49  --comb_res_mult                         3
% 23.79/3.49  --comb_sup_mult                         2
% 23.79/3.49  --comb_inst_mult                        10
% 23.79/3.49  
% 23.79/3.49  ------ Debug Options
% 23.79/3.49  
% 23.79/3.49  --dbg_backtrace                         false
% 23.79/3.49  --dbg_dump_prop_clauses                 false
% 23.79/3.49  --dbg_dump_prop_clauses_file            -
% 23.79/3.49  --dbg_out_stat                          false
% 23.79/3.49  ------ Parsing...
% 23.79/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.79/3.49  
% 23.79/3.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.79/3.49  
% 23.79/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.79/3.49  
% 23.79/3.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.79/3.49  ------ Proving...
% 23.79/3.49  ------ Problem Properties 
% 23.79/3.49  
% 23.79/3.49  
% 23.79/3.49  clauses                                 8
% 23.79/3.49  conjectures                             1
% 23.79/3.49  EPR                                     0
% 23.79/3.49  Horn                                    8
% 23.79/3.49  unary                                   8
% 23.79/3.49  binary                                  0
% 23.79/3.49  lits                                    8
% 23.79/3.49  lits eq                                 8
% 23.79/3.49  fd_pure                                 0
% 23.79/3.49  fd_pseudo                               0
% 23.79/3.49  fd_cond                                 0
% 23.79/3.49  fd_pseudo_cond                          0
% 23.79/3.49  AC symbols                              0
% 23.79/3.49  
% 23.79/3.49  ------ Input Options Time Limit: Unbounded
% 23.79/3.49  
% 23.79/3.49  
% 23.79/3.49  ------ 
% 23.79/3.49  Current options:
% 23.79/3.49  ------ 
% 23.79/3.49  
% 23.79/3.49  ------ Input Options
% 23.79/3.49  
% 23.79/3.49  --out_options                           all
% 23.79/3.49  --tptp_safe_out                         true
% 23.79/3.49  --problem_path                          ""
% 23.79/3.49  --include_path                          ""
% 23.79/3.49  --clausifier                            res/vclausify_rel
% 23.79/3.49  --clausifier_options                    --mode clausify
% 23.79/3.49  --stdin                                 false
% 23.79/3.49  --stats_out                             sel
% 23.79/3.49  
% 23.79/3.49  ------ General Options
% 23.79/3.49  
% 23.79/3.49  --fof                                   false
% 23.79/3.49  --time_out_real                         604.99
% 23.79/3.49  --time_out_virtual                      -1.
% 23.79/3.49  --symbol_type_check                     false
% 23.79/3.49  --clausify_out                          false
% 23.79/3.49  --sig_cnt_out                           false
% 23.79/3.49  --trig_cnt_out                          false
% 23.79/3.49  --trig_cnt_out_tolerance                1.
% 23.79/3.49  --trig_cnt_out_sk_spl                   false
% 23.79/3.49  --abstr_cl_out                          false
% 23.79/3.49  
% 23.79/3.49  ------ Global Options
% 23.79/3.49  
% 23.79/3.49  --schedule                              none
% 23.79/3.49  --add_important_lit                     false
% 23.79/3.49  --prop_solver_per_cl                    1000
% 23.79/3.49  --min_unsat_core                        false
% 23.79/3.49  --soft_assumptions                      false
% 23.79/3.49  --soft_lemma_size                       3
% 23.79/3.49  --prop_impl_unit_size                   0
% 23.79/3.49  --prop_impl_unit                        []
% 23.79/3.49  --share_sel_clauses                     true
% 23.79/3.49  --reset_solvers                         false
% 23.79/3.49  --bc_imp_inh                            [conj_cone]
% 23.79/3.49  --conj_cone_tolerance                   3.
% 23.79/3.49  --extra_neg_conj                        none
% 23.79/3.49  --large_theory_mode                     true
% 23.79/3.49  --prolific_symb_bound                   200
% 23.79/3.49  --lt_threshold                          2000
% 23.79/3.49  --clause_weak_htbl                      true
% 23.79/3.49  --gc_record_bc_elim                     false
% 23.79/3.49  
% 23.79/3.49  ------ Preprocessing Options
% 23.79/3.49  
% 23.79/3.49  --preprocessing_flag                    true
% 23.79/3.49  --time_out_prep_mult                    0.1
% 23.79/3.49  --splitting_mode                        input
% 23.79/3.49  --splitting_grd                         true
% 23.79/3.49  --splitting_cvd                         false
% 23.79/3.49  --splitting_cvd_svl                     false
% 23.79/3.49  --splitting_nvd                         32
% 23.79/3.49  --sub_typing                            true
% 23.79/3.49  --prep_gs_sim                           false
% 23.79/3.49  --prep_unflatten                        true
% 23.79/3.49  --prep_res_sim                          true
% 23.79/3.49  --prep_upred                            true
% 23.79/3.49  --prep_sem_filter                       exhaustive
% 23.79/3.49  --prep_sem_filter_out                   false
% 23.79/3.49  --pred_elim                             false
% 23.79/3.49  --res_sim_input                         true
% 23.79/3.49  --eq_ax_congr_red                       true
% 23.79/3.49  --pure_diseq_elim                       true
% 23.79/3.49  --brand_transform                       false
% 23.79/3.49  --non_eq_to_eq                          false
% 23.79/3.49  --prep_def_merge                        true
% 23.79/3.49  --prep_def_merge_prop_impl              false
% 23.79/3.49  --prep_def_merge_mbd                    true
% 23.79/3.49  --prep_def_merge_tr_red                 false
% 23.79/3.49  --prep_def_merge_tr_cl                  false
% 23.79/3.49  --smt_preprocessing                     true
% 23.79/3.49  --smt_ac_axioms                         fast
% 23.79/3.49  --preprocessed_out                      false
% 23.79/3.49  --preprocessed_stats                    false
% 23.79/3.49  
% 23.79/3.49  ------ Abstraction refinement Options
% 23.79/3.49  
% 23.79/3.49  --abstr_ref                             []
% 23.79/3.49  --abstr_ref_prep                        false
% 23.79/3.49  --abstr_ref_until_sat                   false
% 23.79/3.49  --abstr_ref_sig_restrict                funpre
% 23.79/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.79/3.49  --abstr_ref_under                       []
% 23.79/3.49  
% 23.79/3.49  ------ SAT Options
% 23.79/3.49  
% 23.79/3.49  --sat_mode                              false
% 23.79/3.49  --sat_fm_restart_options                ""
% 23.79/3.49  --sat_gr_def                            false
% 23.79/3.49  --sat_epr_types                         true
% 23.79/3.49  --sat_non_cyclic_types                  false
% 23.79/3.49  --sat_finite_models                     false
% 23.79/3.49  --sat_fm_lemmas                         false
% 23.79/3.49  --sat_fm_prep                           false
% 23.79/3.49  --sat_fm_uc_incr                        true
% 23.79/3.49  --sat_out_model                         small
% 23.79/3.49  --sat_out_clauses                       false
% 23.79/3.49  
% 23.79/3.49  ------ QBF Options
% 23.79/3.49  
% 23.79/3.49  --qbf_mode                              false
% 23.79/3.49  --qbf_elim_univ                         false
% 23.79/3.49  --qbf_dom_inst                          none
% 23.79/3.49  --qbf_dom_pre_inst                      false
% 23.79/3.49  --qbf_sk_in                             false
% 23.79/3.49  --qbf_pred_elim                         true
% 23.79/3.49  --qbf_split                             512
% 23.79/3.49  
% 23.79/3.49  ------ BMC1 Options
% 23.79/3.49  
% 23.79/3.49  --bmc1_incremental                      false
% 23.79/3.49  --bmc1_axioms                           reachable_all
% 23.79/3.49  --bmc1_min_bound                        0
% 23.79/3.49  --bmc1_max_bound                        -1
% 23.79/3.49  --bmc1_max_bound_default                -1
% 23.79/3.49  --bmc1_symbol_reachability              true
% 23.79/3.49  --bmc1_property_lemmas                  false
% 23.79/3.49  --bmc1_k_induction                      false
% 23.79/3.49  --bmc1_non_equiv_states                 false
% 23.79/3.49  --bmc1_deadlock                         false
% 23.79/3.49  --bmc1_ucm                              false
% 23.79/3.49  --bmc1_add_unsat_core                   none
% 23.79/3.49  --bmc1_unsat_core_children              false
% 23.79/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.79/3.49  --bmc1_out_stat                         full
% 23.79/3.49  --bmc1_ground_init                      false
% 23.79/3.49  --bmc1_pre_inst_next_state              false
% 23.79/3.49  --bmc1_pre_inst_state                   false
% 23.79/3.49  --bmc1_pre_inst_reach_state             false
% 23.79/3.49  --bmc1_out_unsat_core                   false
% 23.79/3.49  --bmc1_aig_witness_out                  false
% 23.79/3.49  --bmc1_verbose                          false
% 23.79/3.49  --bmc1_dump_clauses_tptp                false
% 23.79/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.79/3.49  --bmc1_dump_file                        -
% 23.79/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.79/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.79/3.49  --bmc1_ucm_extend_mode                  1
% 23.79/3.49  --bmc1_ucm_init_mode                    2
% 23.79/3.49  --bmc1_ucm_cone_mode                    none
% 23.79/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.79/3.49  --bmc1_ucm_relax_model                  4
% 23.79/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.79/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.79/3.49  --bmc1_ucm_layered_model                none
% 23.79/3.49  --bmc1_ucm_max_lemma_size               10
% 23.79/3.49  
% 23.79/3.49  ------ AIG Options
% 23.79/3.49  
% 23.79/3.49  --aig_mode                              false
% 23.79/3.49  
% 23.79/3.49  ------ Instantiation Options
% 23.79/3.49  
% 23.79/3.49  --instantiation_flag                    true
% 23.79/3.49  --inst_sos_flag                         false
% 23.79/3.49  --inst_sos_phase                        true
% 23.79/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.79/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.79/3.49  --inst_lit_sel_side                     num_symb
% 23.79/3.49  --inst_solver_per_active                1400
% 23.79/3.49  --inst_solver_calls_frac                1.
% 23.79/3.49  --inst_passive_queue_type               priority_queues
% 23.79/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.79/3.49  --inst_passive_queues_freq              [25;2]
% 23.79/3.49  --inst_dismatching                      true
% 23.79/3.49  --inst_eager_unprocessed_to_passive     true
% 23.79/3.49  --inst_prop_sim_given                   true
% 23.79/3.49  --inst_prop_sim_new                     false
% 23.79/3.49  --inst_subs_new                         false
% 23.79/3.49  --inst_eq_res_simp                      false
% 23.79/3.49  --inst_subs_given                       false
% 23.79/3.49  --inst_orphan_elimination               true
% 23.79/3.49  --inst_learning_loop_flag               true
% 23.79/3.49  --inst_learning_start                   3000
% 23.79/3.49  --inst_learning_factor                  2
% 23.79/3.49  --inst_start_prop_sim_after_learn       3
% 23.79/3.49  --inst_sel_renew                        solver
% 23.79/3.49  --inst_lit_activity_flag                true
% 23.79/3.49  --inst_restr_to_given                   false
% 23.79/3.49  --inst_activity_threshold               500
% 23.79/3.49  --inst_out_proof                        true
% 23.79/3.49  
% 23.79/3.49  ------ Resolution Options
% 23.79/3.49  
% 23.79/3.49  --resolution_flag                       true
% 23.79/3.49  --res_lit_sel                           adaptive
% 23.79/3.49  --res_lit_sel_side                      none
% 23.79/3.49  --res_ordering                          kbo
% 23.79/3.49  --res_to_prop_solver                    active
% 23.79/3.49  --res_prop_simpl_new                    false
% 23.79/3.49  --res_prop_simpl_given                  true
% 23.79/3.49  --res_passive_queue_type                priority_queues
% 23.79/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.79/3.49  --res_passive_queues_freq               [15;5]
% 23.79/3.49  --res_forward_subs                      full
% 23.79/3.49  --res_backward_subs                     full
% 23.79/3.49  --res_forward_subs_resolution           true
% 23.79/3.49  --res_backward_subs_resolution          true
% 23.79/3.49  --res_orphan_elimination                true
% 23.79/3.49  --res_time_limit                        2.
% 23.79/3.49  --res_out_proof                         true
% 23.79/3.49  
% 23.79/3.49  ------ Superposition Options
% 23.79/3.49  
% 23.79/3.49  --superposition_flag                    true
% 23.79/3.49  --sup_passive_queue_type                priority_queues
% 23.79/3.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.79/3.49  --sup_passive_queues_freq               [1;4]
% 23.79/3.49  --demod_completeness_check              fast
% 23.79/3.49  --demod_use_ground                      true
% 23.79/3.49  --sup_to_prop_solver                    passive
% 23.79/3.49  --sup_prop_simpl_new                    true
% 23.79/3.49  --sup_prop_simpl_given                  true
% 23.79/3.49  --sup_fun_splitting                     false
% 23.79/3.49  --sup_smt_interval                      50000
% 23.79/3.49  
% 23.79/3.49  ------ Superposition Simplification Setup
% 23.79/3.49  
% 23.79/3.49  --sup_indices_passive                   []
% 23.79/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.79/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.79/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.79/3.49  --sup_full_bw                           [BwDemod]
% 23.79/3.49  --sup_immed_triv                        [TrivRules]
% 23.79/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.79/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.79/3.49  --sup_immed_bw_main                     []
% 23.79/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.79/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.79/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.79/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.79/3.49  
% 23.79/3.49  ------ Combination Options
% 23.79/3.49  
% 23.79/3.49  --comb_res_mult                         3
% 23.79/3.49  --comb_sup_mult                         2
% 23.79/3.49  --comb_inst_mult                        10
% 23.79/3.49  
% 23.79/3.49  ------ Debug Options
% 23.79/3.49  
% 23.79/3.49  --dbg_backtrace                         false
% 23.79/3.49  --dbg_dump_prop_clauses                 false
% 23.79/3.49  --dbg_dump_prop_clauses_file            -
% 23.79/3.49  --dbg_out_stat                          false
% 23.79/3.49  
% 23.79/3.49  
% 23.79/3.49  
% 23.79/3.49  
% 23.79/3.49  ------ Proving...
% 23.79/3.49  
% 23.79/3.49  
% 23.79/3.49  % SZS status Theorem for theBenchmark.p
% 23.79/3.49  
% 23.79/3.49   Resolution empty clause
% 23.79/3.49  
% 23.79/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.79/3.49  
% 23.79/3.49  fof(f4,axiom,(
% 23.79/3.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f18,plain,(
% 23.79/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 23.79/3.49    inference(cnf_transformation,[],[f4])).
% 23.79/3.49  
% 23.79/3.49  fof(f9,axiom,(
% 23.79/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f23,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 23.79/3.49    inference(cnf_transformation,[],[f9])).
% 23.79/3.49  
% 23.79/3.49  fof(f6,axiom,(
% 23.79/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f20,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.79/3.49    inference(cnf_transformation,[],[f6])).
% 23.79/3.49  
% 23.79/3.49  fof(f25,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.79/3.49    inference(definition_unfolding,[],[f23,f20])).
% 23.79/3.49  
% 23.79/3.49  fof(f28,plain,(
% 23.79/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 23.79/3.49    inference(definition_unfolding,[],[f18,f25])).
% 23.79/3.49  
% 23.79/3.49  fof(f5,axiom,(
% 23.79/3.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f19,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 23.79/3.49    inference(cnf_transformation,[],[f5])).
% 23.79/3.49  
% 23.79/3.49  fof(f29,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0) )),
% 23.79/3.49    inference(definition_unfolding,[],[f19,f25])).
% 23.79/3.49  
% 23.79/3.49  fof(f3,axiom,(
% 23.79/3.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f17,plain,(
% 23.79/3.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.79/3.49    inference(cnf_transformation,[],[f3])).
% 23.79/3.49  
% 23.79/3.49  fof(f2,axiom,(
% 23.79/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f16,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.79/3.49    inference(cnf_transformation,[],[f2])).
% 23.79/3.49  
% 23.79/3.49  fof(f27,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 23.79/3.49    inference(definition_unfolding,[],[f16,f25,f25])).
% 23.79/3.49  
% 23.79/3.49  fof(f1,axiom,(
% 23.79/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f15,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.79/3.49    inference(cnf_transformation,[],[f1])).
% 23.79/3.49  
% 23.79/3.49  fof(f26,plain,(
% 23.79/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.79/3.49    inference(definition_unfolding,[],[f15,f20,f20])).
% 23.79/3.49  
% 23.79/3.49  fof(f7,axiom,(
% 23.79/3.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f21,plain,(
% 23.79/3.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.79/3.49    inference(cnf_transformation,[],[f7])).
% 23.79/3.49  
% 23.79/3.49  fof(f8,axiom,(
% 23.79/3.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f22,plain,(
% 23.79/3.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.79/3.49    inference(cnf_transformation,[],[f8])).
% 23.79/3.49  
% 23.79/3.49  fof(f10,conjecture,(
% 23.79/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.79/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.79/3.49  
% 23.79/3.49  fof(f11,negated_conjecture,(
% 23.79/3.49    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.79/3.49    inference(negated_conjecture,[],[f10])).
% 23.79/3.49  
% 23.79/3.49  fof(f12,plain,(
% 23.79/3.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.79/3.49    inference(ennf_transformation,[],[f11])).
% 23.79/3.49  
% 23.79/3.49  fof(f13,plain,(
% 23.79/3.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 23.79/3.49    introduced(choice_axiom,[])).
% 23.79/3.49  
% 23.79/3.49  fof(f14,plain,(
% 23.79/3.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 23.79/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 23.79/3.49  
% 23.79/3.49  fof(f24,plain,(
% 23.79/3.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 23.79/3.49    inference(cnf_transformation,[],[f14])).
% 23.79/3.49  
% 23.79/3.49  fof(f30,plain,(
% 23.79/3.49    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 23.79/3.49    inference(definition_unfolding,[],[f24,f25])).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 23.79/3.49      inference(cnf_transformation,[],[f28]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_4,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 23.79/3.49      inference(cnf_transformation,[],[f29]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_311,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_511,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_311,c_3]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_2,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.79/3.49      inference(cnf_transformation,[],[f17]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_508,plain,
% 23.79/3.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_311,c_2]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1001,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k1_xboole_0 ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_511,c_508]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 23.79/3.49      inference(cnf_transformation,[],[f27]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1021,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_1001,c_1]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_0,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.79/3.49      inference(cnf_transformation,[],[f26]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1024,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_1001,c_0]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1051,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k1_xboole_0) ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_1021,c_1024]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_5,plain,
% 23.79/3.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.79/3.49      inference(cnf_transformation,[],[f21]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1053,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k1_xboole_0) = X0 ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_1051,c_2,c_5,c_508]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_6,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.79/3.49      inference(cnf_transformation,[],[f22]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1498,plain,
% 23.79/3.49      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) = X0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_1053,c_6]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1500,plain,
% 23.79/3.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_1498,c_5]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1528,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_1500,c_3]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1541,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_1528,c_2]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1824,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_1500,c_1541]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_1858,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_1824,c_2]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_445,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_450,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_445,c_3]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3145,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X1) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k1_xboole_0) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_4,c_450]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3260,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_3145,c_3]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3261,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_3260,c_2]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_4814,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_508,c_3261]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_4864,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_3261,c_0]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_4998,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k4_xboole_0(k1_xboole_0,X2) ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_4814,c_4864]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_164,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_4855,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))))) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_3261,c_164]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_5001,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k1_xboole_0,X2)))) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_4998,c_4855]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_5004,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0))) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_5001,c_450]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_704,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_508,c_1]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_713,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0)) ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_704,c_508]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_715,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_713,c_2,c_5,c_508]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_5005,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_5004,c_2,c_450,c_715]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_5146,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X1,X2)) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_0,c_5005]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_6388,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_0,c_5146]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9482,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(k4_xboole_0(X1,X0),X2))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_3261,c_6388]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9698,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_9482,c_450]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9699,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_9698,c_2,c_5005]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9804,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_1858,c_9699]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9891,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)),k1_xboole_0) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_9699,c_1]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9942,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_9891,c_1,c_5]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_10066,plain,
% 23.79/3.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_9804,c_9942]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_10069,plain,
% 23.79/3.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_10066,c_5]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_16733,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_10069,c_1]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_16791,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_16733,c_1]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_162,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3171,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_450,c_162]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3193,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_3171,c_450]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3175,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_450,c_508]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3194,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_3193,c_3175]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_3196,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_3194,c_5]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9881,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k1_xboole_0)) = k1_xboole_0 ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_9699,c_3196]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_9959,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),X0) = k1_xboole_0 ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_9881,c_5,c_450]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_10903,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k1_xboole_0) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_9959,c_0]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_10969,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)),k1_xboole_0) = X0 ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_10903,c_2,c_9699]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_11283,plain,
% 23.79/3.49      ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)),X2)) = k4_xboole_0(X0,k1_xboole_0) ),
% 23.79/3.49      inference(superposition,[status(thm)],[c_10969,c_3261]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_11294,plain,
% 23.79/3.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
% 23.79/3.49      inference(light_normalisation,[status(thm)],[c_11283,c_2]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_16792,plain,
% 23.79/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_16791,c_5,c_508,c_11294]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_7,negated_conjecture,
% 23.79/3.49      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 23.79/3.49      inference(cnf_transformation,[],[f30]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_70774,plain,
% 23.79/3.49      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
% 23.79/3.49      inference(demodulation,[status(thm)],[c_16792,c_7]) ).
% 23.79/3.49  
% 23.79/3.49  cnf(c_70776,plain,
% 23.79/3.49      ( $false ),
% 23.79/3.49      inference(equality_resolution_simp,[status(thm)],[c_70774]) ).
% 23.79/3.49  
% 23.79/3.49  
% 23.79/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.79/3.49  
% 23.79/3.49  ------                               Statistics
% 23.79/3.49  
% 23.79/3.49  ------ Selected
% 23.79/3.49  
% 23.79/3.49  total_time:                             2.672
% 23.79/3.49  
%------------------------------------------------------------------------------
