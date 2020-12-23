%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:54 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  132 (2622 expanded)
%              Number of clauses        :  109 (1163 expanded)
%              Number of leaves         :    9 ( 697 expanded)
%              Depth                    :   27
%              Number of atoms          :  133 (2623 expanded)
%              Number of equality atoms :  132 (2622 expanded)
%              Maximal formula depth    :    6 (   1 average)
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

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f21,f20,f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f22,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f22,f20,f20,f20])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_25,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_6,c_4])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_25])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_75,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_974,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_99,c_75])).

cnf(c_1041,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_974,c_2])).

cnf(c_3,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_31,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_32,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_31,c_2])).

cnf(c_1122,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1041,c_32])).

cnf(c_1123,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1041,c_0])).

cnf(c_1172,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1122,c_1123])).

cnf(c_28,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_36,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_28,c_2])).

cnf(c_37,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_36,c_2])).

cnf(c_1289,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_1172,c_37])).

cnf(c_1299,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1289,c_1172])).

cnf(c_3787,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1299])).

cnf(c_35,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_2,c_28])).

cnf(c_38,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_35,c_28])).

cnf(c_211,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_38,c_4])).

cnf(c_4412,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_3787,c_211])).

cnf(c_78,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) ),
    inference(superposition,[status(thm)],[c_4,c_25])).

cnf(c_79,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))))) ),
    inference(demodulation,[status(thm)],[c_78,c_4])).

cnf(c_61,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_28,c_25])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_61,c_25])).

cnf(c_8557,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)),X3) ),
    inference(superposition,[status(thm)],[c_66,c_4])).

cnf(c_73,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_28,c_4])).

cnf(c_83,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_73,c_4])).

cnf(c_210,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_38,c_4])).

cnf(c_216,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_210,c_4])).

cnf(c_6530,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(superposition,[status(thm)],[c_83,c_216])).

cnf(c_6706,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_6530,c_216])).

cnf(c_4815,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X2)),X3) ),
    inference(superposition,[status(thm)],[c_83,c_4])).

cnf(c_74,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_4,c_4])).

cnf(c_82,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_74,c_4])).

cnf(c_4857,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_4815,c_4,c_82])).

cnf(c_6707,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(light_normalisation,[status(thm)],[c_6706,c_4857])).

cnf(c_1274,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1172])).

cnf(c_1394,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_1274])).

cnf(c_1449,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1394,c_1274])).

cnf(c_1419,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1274,c_0])).

cnf(c_2446,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1449,c_1419])).

cnf(c_2460,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1449,c_0])).

cnf(c_2488,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2446,c_2460])).

cnf(c_8388,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2488,c_75])).

cnf(c_1293,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1172,c_0])).

cnf(c_1454,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_1293])).

cnf(c_42,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2,c_32])).

cnf(c_1501,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1454,c_2,c_42])).

cnf(c_3052,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1501])).

cnf(c_3413,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_3052,c_75])).

cnf(c_1694,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_1419,c_75])).

cnf(c_986,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_32,c_75])).

cnf(c_987,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_37,c_75])).

cnf(c_1024,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_987,c_2])).

cnf(c_1696,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_1694,c_986,c_1024])).

cnf(c_3416,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_3413,c_1696])).

cnf(c_4816,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_83,c_2460])).

cnf(c_4819,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_83,c_2])).

cnf(c_4853,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_4819,c_2460])).

cnf(c_4856,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_4816,c_4853])).

cnf(c_8392,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_8388,c_3416,c_4856])).

cnf(c_8592,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) ),
    inference(demodulation,[status(thm)],[c_8557,c_4,c_6707,c_8392])).

cnf(c_16619,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) ),
    inference(light_normalisation,[status(thm)],[c_79,c_79,c_8592])).

cnf(c_983,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_75])).

cnf(c_16620,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_16619,c_79,c_983])).

cnf(c_7,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_26,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_7,c_4,c_25])).

cnf(c_27,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(demodulation,[status(thm)],[c_0,c_26])).

cnf(c_16621,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK0),sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(demodulation,[status(thm)],[c_16620,c_27])).

cnf(c_235,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_211,c_3])).

cnf(c_246,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_235,c_211])).

cnf(c_342,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_246,c_2])).

cnf(c_352,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_342,c_2])).

cnf(c_562,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_42,c_352])).

cnf(c_563,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_562,c_2,c_32])).

cnf(c_603,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),k2_xboole_0(X0,X0))) = k2_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_211,c_563])).

cnf(c_53,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_37,c_32])).

cnf(c_544,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_0,c_42])).

cnf(c_558,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_42,c_32])).

cnf(c_559,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_42,c_0])).

cnf(c_566,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(demodulation,[status(thm)],[c_558,c_559])).

cnf(c_624,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),X0) = k2_xboole_0(k4_xboole_0(X0,X0),X0) ),
    inference(demodulation,[status(thm)],[c_603,c_28,c_32,c_53,c_544,c_566])).

cnf(c_640,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k2_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_624,c_0])).

cnf(c_648,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),X0) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_640,c_2])).

cnf(c_650,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_648,c_624])).

cnf(c_990,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_650,c_75])).

cnf(c_1022,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_990,c_75])).

cnf(c_1023,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1022,c_2])).

cnf(c_1045,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_3,c_1023])).

cnf(c_1100,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1045,c_1023])).

cnf(c_70,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_85,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_70,c_4])).

cnf(c_6332,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) ),
    inference(superposition,[status(thm)],[c_1100,c_85])).

cnf(c_6389,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_85,c_4])).

cnf(c_6431,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_6389,c_4,c_82])).

cnf(c_6503,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),X2))) ),
    inference(demodulation,[status(thm)],[c_6332,c_6431])).

cnf(c_157,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_32,c_99])).

cnf(c_172,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_157,c_99])).

cnf(c_259,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_172,c_4])).

cnf(c_267,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_259,c_4])).

cnf(c_6504,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_6503,c_267])).

cnf(c_16622,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_16621,c_6504])).

cnf(c_17984,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4412,c_16622])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.06/1.57  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/1.57  
% 7.06/1.57  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.06/1.57  
% 7.06/1.57  ------  iProver source info
% 7.06/1.57  
% 7.06/1.57  git: date: 2020-06-30 10:37:57 +0100
% 7.06/1.57  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.06/1.57  git: non_committed_changes: false
% 7.06/1.57  git: last_make_outside_of_git: false
% 7.06/1.57  
% 7.06/1.57  ------ 
% 7.06/1.57  
% 7.06/1.57  ------ Input Options
% 7.06/1.57  
% 7.06/1.57  --out_options                           all
% 7.06/1.57  --tptp_safe_out                         true
% 7.06/1.57  --problem_path                          ""
% 7.06/1.57  --include_path                          ""
% 7.06/1.57  --clausifier                            res/vclausify_rel
% 7.06/1.57  --clausifier_options                    --mode clausify
% 7.06/1.57  --stdin                                 false
% 7.06/1.57  --stats_out                             all
% 7.06/1.57  
% 7.06/1.57  ------ General Options
% 7.06/1.57  
% 7.06/1.57  --fof                                   false
% 7.06/1.57  --time_out_real                         305.
% 7.06/1.57  --time_out_virtual                      -1.
% 7.06/1.57  --symbol_type_check                     false
% 7.06/1.57  --clausify_out                          false
% 7.06/1.57  --sig_cnt_out                           false
% 7.06/1.57  --trig_cnt_out                          false
% 7.06/1.57  --trig_cnt_out_tolerance                1.
% 7.06/1.57  --trig_cnt_out_sk_spl                   false
% 7.06/1.57  --abstr_cl_out                          false
% 7.06/1.57  
% 7.06/1.57  ------ Global Options
% 7.06/1.57  
% 7.06/1.57  --schedule                              default
% 7.06/1.57  --add_important_lit                     false
% 7.06/1.57  --prop_solver_per_cl                    1000
% 7.06/1.57  --min_unsat_core                        false
% 7.06/1.57  --soft_assumptions                      false
% 7.06/1.57  --soft_lemma_size                       3
% 7.06/1.57  --prop_impl_unit_size                   0
% 7.06/1.57  --prop_impl_unit                        []
% 7.06/1.57  --share_sel_clauses                     true
% 7.06/1.57  --reset_solvers                         false
% 7.06/1.57  --bc_imp_inh                            [conj_cone]
% 7.06/1.57  --conj_cone_tolerance                   3.
% 7.06/1.57  --extra_neg_conj                        none
% 7.06/1.57  --large_theory_mode                     true
% 7.06/1.57  --prolific_symb_bound                   200
% 7.06/1.57  --lt_threshold                          2000
% 7.06/1.57  --clause_weak_htbl                      true
% 7.06/1.57  --gc_record_bc_elim                     false
% 7.06/1.57  
% 7.06/1.57  ------ Preprocessing Options
% 7.06/1.57  
% 7.06/1.57  --preprocessing_flag                    true
% 7.06/1.57  --time_out_prep_mult                    0.1
% 7.06/1.57  --splitting_mode                        input
% 7.06/1.57  --splitting_grd                         true
% 7.06/1.57  --splitting_cvd                         false
% 7.06/1.57  --splitting_cvd_svl                     false
% 7.06/1.57  --splitting_nvd                         32
% 7.06/1.57  --sub_typing                            true
% 7.06/1.57  --prep_gs_sim                           true
% 7.06/1.57  --prep_unflatten                        true
% 7.06/1.57  --prep_res_sim                          true
% 7.06/1.57  --prep_upred                            true
% 7.06/1.57  --prep_sem_filter                       exhaustive
% 7.06/1.57  --prep_sem_filter_out                   false
% 7.06/1.57  --pred_elim                             true
% 7.06/1.57  --res_sim_input                         true
% 7.06/1.57  --eq_ax_congr_red                       true
% 7.06/1.57  --pure_diseq_elim                       true
% 7.06/1.57  --brand_transform                       false
% 7.06/1.57  --non_eq_to_eq                          false
% 7.06/1.57  --prep_def_merge                        true
% 7.06/1.57  --prep_def_merge_prop_impl              false
% 7.06/1.57  --prep_def_merge_mbd                    true
% 7.06/1.57  --prep_def_merge_tr_red                 false
% 7.06/1.57  --prep_def_merge_tr_cl                  false
% 7.06/1.57  --smt_preprocessing                     true
% 7.06/1.57  --smt_ac_axioms                         fast
% 7.06/1.57  --preprocessed_out                      false
% 7.06/1.57  --preprocessed_stats                    false
% 7.06/1.57  
% 7.06/1.57  ------ Abstraction refinement Options
% 7.06/1.57  
% 7.06/1.57  --abstr_ref                             []
% 7.06/1.57  --abstr_ref_prep                        false
% 7.06/1.57  --abstr_ref_until_sat                   false
% 7.06/1.57  --abstr_ref_sig_restrict                funpre
% 7.06/1.57  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.57  --abstr_ref_under                       []
% 7.06/1.57  
% 7.06/1.57  ------ SAT Options
% 7.06/1.57  
% 7.06/1.57  --sat_mode                              false
% 7.06/1.57  --sat_fm_restart_options                ""
% 7.06/1.57  --sat_gr_def                            false
% 7.06/1.57  --sat_epr_types                         true
% 7.06/1.57  --sat_non_cyclic_types                  false
% 7.06/1.57  --sat_finite_models                     false
% 7.06/1.57  --sat_fm_lemmas                         false
% 7.06/1.57  --sat_fm_prep                           false
% 7.06/1.57  --sat_fm_uc_incr                        true
% 7.06/1.57  --sat_out_model                         small
% 7.06/1.57  --sat_out_clauses                       false
% 7.06/1.57  
% 7.06/1.57  ------ QBF Options
% 7.06/1.57  
% 7.06/1.57  --qbf_mode                              false
% 7.06/1.57  --qbf_elim_univ                         false
% 7.06/1.57  --qbf_dom_inst                          none
% 7.06/1.57  --qbf_dom_pre_inst                      false
% 7.06/1.57  --qbf_sk_in                             false
% 7.06/1.57  --qbf_pred_elim                         true
% 7.06/1.57  --qbf_split                             512
% 7.06/1.57  
% 7.06/1.57  ------ BMC1 Options
% 7.06/1.57  
% 7.06/1.57  --bmc1_incremental                      false
% 7.06/1.57  --bmc1_axioms                           reachable_all
% 7.06/1.57  --bmc1_min_bound                        0
% 7.06/1.57  --bmc1_max_bound                        -1
% 7.06/1.57  --bmc1_max_bound_default                -1
% 7.06/1.57  --bmc1_symbol_reachability              true
% 7.06/1.57  --bmc1_property_lemmas                  false
% 7.06/1.57  --bmc1_k_induction                      false
% 7.06/1.57  --bmc1_non_equiv_states                 false
% 7.06/1.57  --bmc1_deadlock                         false
% 7.06/1.57  --bmc1_ucm                              false
% 7.06/1.57  --bmc1_add_unsat_core                   none
% 7.06/1.57  --bmc1_unsat_core_children              false
% 7.06/1.57  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.57  --bmc1_out_stat                         full
% 7.06/1.57  --bmc1_ground_init                      false
% 7.06/1.57  --bmc1_pre_inst_next_state              false
% 7.06/1.57  --bmc1_pre_inst_state                   false
% 7.06/1.57  --bmc1_pre_inst_reach_state             false
% 7.06/1.57  --bmc1_out_unsat_core                   false
% 7.06/1.57  --bmc1_aig_witness_out                  false
% 7.06/1.57  --bmc1_verbose                          false
% 7.06/1.57  --bmc1_dump_clauses_tptp                false
% 7.06/1.57  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.57  --bmc1_dump_file                        -
% 7.06/1.57  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.57  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.57  --bmc1_ucm_extend_mode                  1
% 7.06/1.57  --bmc1_ucm_init_mode                    2
% 7.06/1.57  --bmc1_ucm_cone_mode                    none
% 7.06/1.57  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.57  --bmc1_ucm_relax_model                  4
% 7.06/1.57  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.57  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.57  --bmc1_ucm_layered_model                none
% 7.06/1.57  --bmc1_ucm_max_lemma_size               10
% 7.06/1.57  
% 7.06/1.57  ------ AIG Options
% 7.06/1.57  
% 7.06/1.57  --aig_mode                              false
% 7.06/1.57  
% 7.06/1.57  ------ Instantiation Options
% 7.06/1.57  
% 7.06/1.57  --instantiation_flag                    true
% 7.06/1.57  --inst_sos_flag                         false
% 7.06/1.57  --inst_sos_phase                        true
% 7.06/1.57  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.57  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.57  --inst_lit_sel_side                     num_symb
% 7.06/1.57  --inst_solver_per_active                1400
% 7.06/1.57  --inst_solver_calls_frac                1.
% 7.06/1.57  --inst_passive_queue_type               priority_queues
% 7.06/1.57  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.57  --inst_passive_queues_freq              [25;2]
% 7.06/1.57  --inst_dismatching                      true
% 7.06/1.57  --inst_eager_unprocessed_to_passive     true
% 7.06/1.57  --inst_prop_sim_given                   true
% 7.06/1.57  --inst_prop_sim_new                     false
% 7.06/1.57  --inst_subs_new                         false
% 7.06/1.57  --inst_eq_res_simp                      false
% 7.06/1.57  --inst_subs_given                       false
% 7.06/1.57  --inst_orphan_elimination               true
% 7.06/1.57  --inst_learning_loop_flag               true
% 7.06/1.57  --inst_learning_start                   3000
% 7.06/1.57  --inst_learning_factor                  2
% 7.06/1.57  --inst_start_prop_sim_after_learn       3
% 7.06/1.57  --inst_sel_renew                        solver
% 7.06/1.57  --inst_lit_activity_flag                true
% 7.06/1.57  --inst_restr_to_given                   false
% 7.06/1.57  --inst_activity_threshold               500
% 7.06/1.57  --inst_out_proof                        true
% 7.06/1.57  
% 7.06/1.57  ------ Resolution Options
% 7.06/1.57  
% 7.06/1.57  --resolution_flag                       true
% 7.06/1.57  --res_lit_sel                           adaptive
% 7.06/1.57  --res_lit_sel_side                      none
% 7.06/1.57  --res_ordering                          kbo
% 7.06/1.57  --res_to_prop_solver                    active
% 7.06/1.57  --res_prop_simpl_new                    false
% 7.06/1.57  --res_prop_simpl_given                  true
% 7.06/1.57  --res_passive_queue_type                priority_queues
% 7.06/1.57  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.57  --res_passive_queues_freq               [15;5]
% 7.06/1.57  --res_forward_subs                      full
% 7.06/1.57  --res_backward_subs                     full
% 7.06/1.57  --res_forward_subs_resolution           true
% 7.06/1.57  --res_backward_subs_resolution          true
% 7.06/1.57  --res_orphan_elimination                true
% 7.06/1.57  --res_time_limit                        2.
% 7.06/1.57  --res_out_proof                         true
% 7.06/1.57  
% 7.06/1.57  ------ Superposition Options
% 7.06/1.57  
% 7.06/1.57  --superposition_flag                    true
% 7.06/1.57  --sup_passive_queue_type                priority_queues
% 7.06/1.57  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.57  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.57  --demod_completeness_check              fast
% 7.06/1.57  --demod_use_ground                      true
% 7.06/1.57  --sup_to_prop_solver                    passive
% 7.06/1.57  --sup_prop_simpl_new                    true
% 7.06/1.57  --sup_prop_simpl_given                  true
% 7.06/1.57  --sup_fun_splitting                     false
% 7.06/1.57  --sup_smt_interval                      50000
% 7.06/1.57  
% 7.06/1.57  ------ Superposition Simplification Setup
% 7.06/1.57  
% 7.06/1.57  --sup_indices_passive                   []
% 7.06/1.57  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.57  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.57  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.57  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.57  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.57  --sup_full_bw                           [BwDemod]
% 7.06/1.57  --sup_immed_triv                        [TrivRules]
% 7.06/1.57  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.57  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.57  --sup_immed_bw_main                     []
% 7.06/1.57  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.57  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.57  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.57  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.57  
% 7.06/1.57  ------ Combination Options
% 7.06/1.57  
% 7.06/1.57  --comb_res_mult                         3
% 7.06/1.57  --comb_sup_mult                         2
% 7.06/1.57  --comb_inst_mult                        10
% 7.06/1.57  
% 7.06/1.57  ------ Debug Options
% 7.06/1.57  
% 7.06/1.57  --dbg_backtrace                         false
% 7.06/1.57  --dbg_dump_prop_clauses                 false
% 7.06/1.57  --dbg_dump_prop_clauses_file            -
% 7.06/1.57  --dbg_out_stat                          false
% 7.06/1.57  ------ Parsing...
% 7.06/1.57  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.06/1.57  
% 7.06/1.57  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.06/1.57  
% 7.06/1.57  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.06/1.57  
% 7.06/1.57  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.06/1.57  ------ Proving...
% 7.06/1.57  ------ Problem Properties 
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  clauses                                 8
% 7.06/1.57  conjectures                             1
% 7.06/1.57  EPR                                     0
% 7.06/1.57  Horn                                    8
% 7.06/1.57  unary                                   8
% 7.06/1.57  binary                                  0
% 7.06/1.57  lits                                    8
% 7.06/1.57  lits eq                                 8
% 7.06/1.57  fd_pure                                 0
% 7.06/1.57  fd_pseudo                               0
% 7.06/1.57  fd_cond                                 0
% 7.06/1.57  fd_pseudo_cond                          0
% 7.06/1.57  AC symbols                              0
% 7.06/1.57  
% 7.06/1.57  ------ Schedule UEQ
% 7.06/1.57  
% 7.06/1.57  ------ pure equality problem: resolution off 
% 7.06/1.57  
% 7.06/1.57  ------ Option_UEQ Time Limit: Unbounded
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  ------ 
% 7.06/1.57  Current options:
% 7.06/1.57  ------ 
% 7.06/1.57  
% 7.06/1.57  ------ Input Options
% 7.06/1.57  
% 7.06/1.57  --out_options                           all
% 7.06/1.57  --tptp_safe_out                         true
% 7.06/1.57  --problem_path                          ""
% 7.06/1.57  --include_path                          ""
% 7.06/1.57  --clausifier                            res/vclausify_rel
% 7.06/1.57  --clausifier_options                    --mode clausify
% 7.06/1.57  --stdin                                 false
% 7.06/1.57  --stats_out                             all
% 7.06/1.57  
% 7.06/1.57  ------ General Options
% 7.06/1.57  
% 7.06/1.57  --fof                                   false
% 7.06/1.57  --time_out_real                         305.
% 7.06/1.57  --time_out_virtual                      -1.
% 7.06/1.57  --symbol_type_check                     false
% 7.06/1.57  --clausify_out                          false
% 7.06/1.57  --sig_cnt_out                           false
% 7.06/1.57  --trig_cnt_out                          false
% 7.06/1.57  --trig_cnt_out_tolerance                1.
% 7.06/1.57  --trig_cnt_out_sk_spl                   false
% 7.06/1.57  --abstr_cl_out                          false
% 7.06/1.57  
% 7.06/1.57  ------ Global Options
% 7.06/1.57  
% 7.06/1.57  --schedule                              default
% 7.06/1.57  --add_important_lit                     false
% 7.06/1.57  --prop_solver_per_cl                    1000
% 7.06/1.57  --min_unsat_core                        false
% 7.06/1.57  --soft_assumptions                      false
% 7.06/1.57  --soft_lemma_size                       3
% 7.06/1.57  --prop_impl_unit_size                   0
% 7.06/1.57  --prop_impl_unit                        []
% 7.06/1.57  --share_sel_clauses                     true
% 7.06/1.57  --reset_solvers                         false
% 7.06/1.57  --bc_imp_inh                            [conj_cone]
% 7.06/1.57  --conj_cone_tolerance                   3.
% 7.06/1.57  --extra_neg_conj                        none
% 7.06/1.57  --large_theory_mode                     true
% 7.06/1.57  --prolific_symb_bound                   200
% 7.06/1.57  --lt_threshold                          2000
% 7.06/1.57  --clause_weak_htbl                      true
% 7.06/1.57  --gc_record_bc_elim                     false
% 7.06/1.57  
% 7.06/1.57  ------ Preprocessing Options
% 7.06/1.57  
% 7.06/1.57  --preprocessing_flag                    true
% 7.06/1.57  --time_out_prep_mult                    0.1
% 7.06/1.57  --splitting_mode                        input
% 7.06/1.57  --splitting_grd                         true
% 7.06/1.57  --splitting_cvd                         false
% 7.06/1.57  --splitting_cvd_svl                     false
% 7.06/1.57  --splitting_nvd                         32
% 7.06/1.57  --sub_typing                            true
% 7.06/1.57  --prep_gs_sim                           true
% 7.06/1.57  --prep_unflatten                        true
% 7.06/1.57  --prep_res_sim                          true
% 7.06/1.57  --prep_upred                            true
% 7.06/1.57  --prep_sem_filter                       exhaustive
% 7.06/1.57  --prep_sem_filter_out                   false
% 7.06/1.57  --pred_elim                             true
% 7.06/1.57  --res_sim_input                         true
% 7.06/1.57  --eq_ax_congr_red                       true
% 7.06/1.57  --pure_diseq_elim                       true
% 7.06/1.57  --brand_transform                       false
% 7.06/1.57  --non_eq_to_eq                          false
% 7.06/1.57  --prep_def_merge                        true
% 7.06/1.57  --prep_def_merge_prop_impl              false
% 7.06/1.57  --prep_def_merge_mbd                    true
% 7.06/1.57  --prep_def_merge_tr_red                 false
% 7.06/1.57  --prep_def_merge_tr_cl                  false
% 7.06/1.57  --smt_preprocessing                     true
% 7.06/1.57  --smt_ac_axioms                         fast
% 7.06/1.57  --preprocessed_out                      false
% 7.06/1.57  --preprocessed_stats                    false
% 7.06/1.57  
% 7.06/1.57  ------ Abstraction refinement Options
% 7.06/1.57  
% 7.06/1.57  --abstr_ref                             []
% 7.06/1.57  --abstr_ref_prep                        false
% 7.06/1.57  --abstr_ref_until_sat                   false
% 7.06/1.57  --abstr_ref_sig_restrict                funpre
% 7.06/1.57  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.57  --abstr_ref_under                       []
% 7.06/1.57  
% 7.06/1.57  ------ SAT Options
% 7.06/1.57  
% 7.06/1.57  --sat_mode                              false
% 7.06/1.57  --sat_fm_restart_options                ""
% 7.06/1.57  --sat_gr_def                            false
% 7.06/1.57  --sat_epr_types                         true
% 7.06/1.57  --sat_non_cyclic_types                  false
% 7.06/1.57  --sat_finite_models                     false
% 7.06/1.57  --sat_fm_lemmas                         false
% 7.06/1.57  --sat_fm_prep                           false
% 7.06/1.57  --sat_fm_uc_incr                        true
% 7.06/1.57  --sat_out_model                         small
% 7.06/1.57  --sat_out_clauses                       false
% 7.06/1.57  
% 7.06/1.57  ------ QBF Options
% 7.06/1.57  
% 7.06/1.57  --qbf_mode                              false
% 7.06/1.57  --qbf_elim_univ                         false
% 7.06/1.57  --qbf_dom_inst                          none
% 7.06/1.57  --qbf_dom_pre_inst                      false
% 7.06/1.57  --qbf_sk_in                             false
% 7.06/1.57  --qbf_pred_elim                         true
% 7.06/1.57  --qbf_split                             512
% 7.06/1.57  
% 7.06/1.57  ------ BMC1 Options
% 7.06/1.57  
% 7.06/1.57  --bmc1_incremental                      false
% 7.06/1.57  --bmc1_axioms                           reachable_all
% 7.06/1.57  --bmc1_min_bound                        0
% 7.06/1.57  --bmc1_max_bound                        -1
% 7.06/1.57  --bmc1_max_bound_default                -1
% 7.06/1.57  --bmc1_symbol_reachability              true
% 7.06/1.57  --bmc1_property_lemmas                  false
% 7.06/1.57  --bmc1_k_induction                      false
% 7.06/1.57  --bmc1_non_equiv_states                 false
% 7.06/1.57  --bmc1_deadlock                         false
% 7.06/1.57  --bmc1_ucm                              false
% 7.06/1.57  --bmc1_add_unsat_core                   none
% 7.06/1.57  --bmc1_unsat_core_children              false
% 7.06/1.57  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.57  --bmc1_out_stat                         full
% 7.06/1.57  --bmc1_ground_init                      false
% 7.06/1.57  --bmc1_pre_inst_next_state              false
% 7.06/1.57  --bmc1_pre_inst_state                   false
% 7.06/1.57  --bmc1_pre_inst_reach_state             false
% 7.06/1.57  --bmc1_out_unsat_core                   false
% 7.06/1.57  --bmc1_aig_witness_out                  false
% 7.06/1.57  --bmc1_verbose                          false
% 7.06/1.57  --bmc1_dump_clauses_tptp                false
% 7.06/1.57  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.57  --bmc1_dump_file                        -
% 7.06/1.57  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.57  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.57  --bmc1_ucm_extend_mode                  1
% 7.06/1.57  --bmc1_ucm_init_mode                    2
% 7.06/1.57  --bmc1_ucm_cone_mode                    none
% 7.06/1.57  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.57  --bmc1_ucm_relax_model                  4
% 7.06/1.57  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.57  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.57  --bmc1_ucm_layered_model                none
% 7.06/1.57  --bmc1_ucm_max_lemma_size               10
% 7.06/1.57  
% 7.06/1.57  ------ AIG Options
% 7.06/1.57  
% 7.06/1.57  --aig_mode                              false
% 7.06/1.57  
% 7.06/1.57  ------ Instantiation Options
% 7.06/1.57  
% 7.06/1.57  --instantiation_flag                    false
% 7.06/1.57  --inst_sos_flag                         false
% 7.06/1.57  --inst_sos_phase                        true
% 7.06/1.57  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.57  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.57  --inst_lit_sel_side                     num_symb
% 7.06/1.57  --inst_solver_per_active                1400
% 7.06/1.57  --inst_solver_calls_frac                1.
% 7.06/1.57  --inst_passive_queue_type               priority_queues
% 7.06/1.57  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.57  --inst_passive_queues_freq              [25;2]
% 7.06/1.57  --inst_dismatching                      true
% 7.06/1.57  --inst_eager_unprocessed_to_passive     true
% 7.06/1.57  --inst_prop_sim_given                   true
% 7.06/1.57  --inst_prop_sim_new                     false
% 7.06/1.57  --inst_subs_new                         false
% 7.06/1.57  --inst_eq_res_simp                      false
% 7.06/1.57  --inst_subs_given                       false
% 7.06/1.57  --inst_orphan_elimination               true
% 7.06/1.57  --inst_learning_loop_flag               true
% 7.06/1.57  --inst_learning_start                   3000
% 7.06/1.57  --inst_learning_factor                  2
% 7.06/1.57  --inst_start_prop_sim_after_learn       3
% 7.06/1.57  --inst_sel_renew                        solver
% 7.06/1.57  --inst_lit_activity_flag                true
% 7.06/1.57  --inst_restr_to_given                   false
% 7.06/1.57  --inst_activity_threshold               500
% 7.06/1.57  --inst_out_proof                        true
% 7.06/1.57  
% 7.06/1.57  ------ Resolution Options
% 7.06/1.57  
% 7.06/1.57  --resolution_flag                       false
% 7.06/1.57  --res_lit_sel                           adaptive
% 7.06/1.57  --res_lit_sel_side                      none
% 7.06/1.57  --res_ordering                          kbo
% 7.06/1.57  --res_to_prop_solver                    active
% 7.06/1.57  --res_prop_simpl_new                    false
% 7.06/1.57  --res_prop_simpl_given                  true
% 7.06/1.57  --res_passive_queue_type                priority_queues
% 7.06/1.57  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.57  --res_passive_queues_freq               [15;5]
% 7.06/1.57  --res_forward_subs                      full
% 7.06/1.57  --res_backward_subs                     full
% 7.06/1.57  --res_forward_subs_resolution           true
% 7.06/1.57  --res_backward_subs_resolution          true
% 7.06/1.57  --res_orphan_elimination                true
% 7.06/1.57  --res_time_limit                        2.
% 7.06/1.57  --res_out_proof                         true
% 7.06/1.57  
% 7.06/1.57  ------ Superposition Options
% 7.06/1.57  
% 7.06/1.57  --superposition_flag                    true
% 7.06/1.57  --sup_passive_queue_type                priority_queues
% 7.06/1.57  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.57  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.57  --demod_completeness_check              fast
% 7.06/1.57  --demod_use_ground                      true
% 7.06/1.57  --sup_to_prop_solver                    active
% 7.06/1.57  --sup_prop_simpl_new                    false
% 7.06/1.57  --sup_prop_simpl_given                  false
% 7.06/1.57  --sup_fun_splitting                     true
% 7.06/1.57  --sup_smt_interval                      10000
% 7.06/1.57  
% 7.06/1.57  ------ Superposition Simplification Setup
% 7.06/1.57  
% 7.06/1.57  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.06/1.57  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.06/1.57  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.57  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.57  --sup_full_triv                         [TrivRules]
% 7.06/1.57  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.06/1.57  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.06/1.57  --sup_immed_triv                        [TrivRules]
% 7.06/1.57  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.57  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.57  --sup_immed_bw_main                     []
% 7.06/1.57  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.06/1.57  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.57  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.57  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.06/1.57  
% 7.06/1.57  ------ Combination Options
% 7.06/1.57  
% 7.06/1.57  --comb_res_mult                         1
% 7.06/1.57  --comb_sup_mult                         1
% 7.06/1.57  --comb_inst_mult                        1000000
% 7.06/1.57  
% 7.06/1.57  ------ Debug Options
% 7.06/1.57  
% 7.06/1.57  --dbg_backtrace                         false
% 7.06/1.57  --dbg_dump_prop_clauses                 false
% 7.06/1.57  --dbg_dump_prop_clauses_file            -
% 7.06/1.57  --dbg_out_stat                          false
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  ------ Proving...
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  % SZS status Theorem for theBenchmark.p
% 7.06/1.57  
% 7.06/1.57   Resolution empty clause
% 7.06/1.57  
% 7.06/1.57  % SZS output start CNFRefutation for theBenchmark.p
% 7.06/1.57  
% 7.06/1.57  fof(f1,axiom,(
% 7.06/1.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f14,plain,(
% 7.06/1.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.06/1.57    inference(cnf_transformation,[],[f1])).
% 7.06/1.57  
% 7.06/1.57  fof(f6,axiom,(
% 7.06/1.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f19,plain,(
% 7.06/1.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.06/1.57    inference(cnf_transformation,[],[f6])).
% 7.06/1.57  
% 7.06/1.57  fof(f7,axiom,(
% 7.06/1.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f20,plain,(
% 7.06/1.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.06/1.57    inference(cnf_transformation,[],[f7])).
% 7.06/1.57  
% 7.06/1.57  fof(f24,plain,(
% 7.06/1.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.06/1.57    inference(definition_unfolding,[],[f19,f20])).
% 7.06/1.57  
% 7.06/1.57  fof(f8,axiom,(
% 7.06/1.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f21,plain,(
% 7.06/1.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.06/1.57    inference(cnf_transformation,[],[f8])).
% 7.06/1.57  
% 7.06/1.57  fof(f25,plain,(
% 7.06/1.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.06/1.57    inference(definition_unfolding,[],[f21,f20,f20])).
% 7.06/1.57  
% 7.06/1.57  fof(f5,axiom,(
% 7.06/1.57    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f18,plain,(
% 7.06/1.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.06/1.57    inference(cnf_transformation,[],[f5])).
% 7.06/1.57  
% 7.06/1.57  fof(f3,axiom,(
% 7.06/1.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f16,plain,(
% 7.06/1.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.06/1.57    inference(cnf_transformation,[],[f3])).
% 7.06/1.57  
% 7.06/1.57  fof(f4,axiom,(
% 7.06/1.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f17,plain,(
% 7.06/1.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.06/1.57    inference(cnf_transformation,[],[f4])).
% 7.06/1.57  
% 7.06/1.57  fof(f9,conjecture,(
% 7.06/1.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.06/1.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.57  
% 7.06/1.57  fof(f10,negated_conjecture,(
% 7.06/1.57    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.06/1.57    inference(negated_conjecture,[],[f9])).
% 7.06/1.57  
% 7.06/1.57  fof(f11,plain,(
% 7.06/1.57    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.06/1.57    inference(ennf_transformation,[],[f10])).
% 7.06/1.57  
% 7.06/1.57  fof(f12,plain,(
% 7.06/1.57    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 7.06/1.57    introduced(choice_axiom,[])).
% 7.06/1.57  
% 7.06/1.57  fof(f13,plain,(
% 7.06/1.57    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 7.06/1.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 7.06/1.57  
% 7.06/1.57  fof(f22,plain,(
% 7.06/1.57    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 7.06/1.57    inference(cnf_transformation,[],[f13])).
% 7.06/1.57  
% 7.06/1.57  fof(f26,plain,(
% 7.06/1.57    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 7.06/1.57    inference(definition_unfolding,[],[f22,f20,f20,f20])).
% 7.06/1.57  
% 7.06/1.57  cnf(c_0,plain,
% 7.06/1.57      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(cnf_transformation,[],[f14]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_5,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.06/1.57      inference(cnf_transformation,[],[f24]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.06/1.57      inference(cnf_transformation,[],[f25]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.06/1.57      inference(cnf_transformation,[],[f18]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_25,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_6,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_99,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_5,c_25]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_2,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(cnf_transformation,[],[f16]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_75,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_974,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_99,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1041,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_974,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_3,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.06/1.57      inference(cnf_transformation,[],[f17]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_31,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_32,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_31,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1122,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X1) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1041,c_32]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1123,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X1) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1041,c_0]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1172,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_1122,c_1123]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_28,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_36,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_28,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_37,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_36,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1289,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1172,c_37]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1299,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_1289,c_1172]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_3787,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_0,c_1299]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_35,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_2,c_28]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_38,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_35,c_28]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_211,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_38,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4412,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_3787,c_211]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_78,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_4,c_25]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_79,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_78,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_61,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_28,c_25]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_66,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_61,c_25]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_8557,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)),X3) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_66,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_73,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_28,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_83,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_73,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_210,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_38,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_216,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_210,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6530,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_83,c_216]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6706,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X2),X3)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_6530,c_216]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4815,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X2)),X3) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_83,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_74,plain,
% 7.06/1.57      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_4,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_82,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_74,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4857,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(X2,X3))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_4815,c_4,c_82]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6707,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_6706,c_4857]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1274,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_0,c_1172]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1394,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_2,c_1274]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1449,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_1394,c_1274]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1419,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1274,c_0]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_2446,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1449,c_1419]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_2460,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1449,c_0]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_2488,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_2446,c_2460]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_8388,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_2488,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1293,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1172,c_0]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1454,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_2,c_1293]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_42,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_2,c_32]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1501,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_1454,c_2,c_42]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_3052,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_0,c_1501]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_3413,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_3052,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1694,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1419,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_986,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_32,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_987,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_37,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1024,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_987,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1696,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_1694,c_986,c_1024]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_3416,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_3413,c_1696]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4816,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_83,c_2460]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4819,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_83,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4853,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_4819,c_2460]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_4856,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_4816,c_4853]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_8392,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_8388,c_3416,c_4856]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_8592,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_8557,c_4,c_6707,c_8392]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_16619,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_79,c_79,c_8592]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_983,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_0,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_16620,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_16619,c_79,c_983]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_7,negated_conjecture,
% 7.06/1.57      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
% 7.06/1.57      inference(cnf_transformation,[],[f26]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_26,plain,
% 7.06/1.57      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_7,c_4,c_25]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_27,plain,
% 7.06/1.57      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_0,c_26]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_16621,plain,
% 7.06/1.57      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK0),sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_16620,c_27]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_235,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_211,c_3]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_246,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) = k4_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_235,c_211]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_342,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_246,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_352,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_342,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_562,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_42,c_352]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_563,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X0)) = k2_xboole_0(X0,X0) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_562,c_2,c_32]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_603,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),k2_xboole_0(X0,X0))) = k2_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_211,c_563]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_53,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_37,c_32]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_544,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_0,c_42]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_558,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_42,c_32]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_559,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_42,c_0]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_566,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_558,c_559]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_624,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X0),X0) = k2_xboole_0(k4_xboole_0(X0,X0),X0) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_603,c_28,c_32,c_53,c_544,c_566]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_640,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k2_xboole_0(X0,X0),X0) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_624,c_0]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_648,plain,
% 7.06/1.57      ( k2_xboole_0(k2_xboole_0(X0,X0),X0) = k2_xboole_0(X0,X0) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_640,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_650,plain,
% 7.06/1.57      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = k2_xboole_0(X0,X0) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_648,c_624]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_990,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_650,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1022,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_990,c_75]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1023,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_1022,c_2]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1045,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_3,c_1023]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_1100,plain,
% 7.06/1.57      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_1045,c_1023]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_70,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_85,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_70,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6332,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_1100,c_85]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6389,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_85,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6431,plain,
% 7.06/1.57      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_6389,c_4,c_82]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6503,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),X2))) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_6332,c_6431]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_157,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_32,c_99]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_172,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_157,c_99]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_259,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_172,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_267,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_259,c_4]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_6504,plain,
% 7.06/1.57      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.06/1.57      inference(light_normalisation,[status(thm)],[c_6503,c_267]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_16622,plain,
% 7.06/1.57      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
% 7.06/1.57      inference(demodulation,[status(thm)],[c_16621,c_6504]) ).
% 7.06/1.57  
% 7.06/1.57  cnf(c_17984,plain,
% 7.06/1.57      ( $false ),
% 7.06/1.57      inference(superposition,[status(thm)],[c_4412,c_16622]) ).
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  % SZS output end CNFRefutation for theBenchmark.p
% 7.06/1.57  
% 7.06/1.57  ------                               Statistics
% 7.06/1.57  
% 7.06/1.57  ------ General
% 7.06/1.57  
% 7.06/1.57  abstr_ref_over_cycles:                  0
% 7.06/1.57  abstr_ref_under_cycles:                 0
% 7.06/1.57  gc_basic_clause_elim:                   0
% 7.06/1.57  forced_gc_time:                         0
% 7.06/1.57  parsing_time:                           0.017
% 7.06/1.57  unif_index_cands_time:                  0.
% 7.06/1.57  unif_index_add_time:                    0.
% 7.06/1.57  orderings_time:                         0.
% 7.06/1.57  out_proof_time:                         0.009
% 7.06/1.57  total_time:                             0.61
% 7.06/1.57  num_of_symbols:                         36
% 7.06/1.57  num_of_terms:                           25310
% 7.06/1.57  
% 7.06/1.57  ------ Preprocessing
% 7.06/1.57  
% 7.06/1.57  num_of_splits:                          0
% 7.06/1.57  num_of_split_atoms:                     0
% 7.06/1.57  num_of_reused_defs:                     0
% 7.06/1.57  num_eq_ax_congr_red:                    0
% 7.06/1.57  num_of_sem_filtered_clauses:            0
% 7.06/1.57  num_of_subtypes:                        1
% 7.06/1.57  monotx_restored_types:                  0
% 7.06/1.57  sat_num_of_epr_types:                   0
% 7.06/1.57  sat_num_of_non_cyclic_types:            0
% 7.06/1.57  sat_guarded_non_collapsed_types:        0
% 7.06/1.57  num_pure_diseq_elim:                    0
% 7.06/1.57  simp_replaced_by:                       0
% 7.06/1.57  res_preprocessed:                       20
% 7.06/1.57  prep_upred:                             0
% 7.06/1.57  prep_unflattend:                        0
% 7.06/1.57  smt_new_axioms:                         0
% 7.06/1.57  pred_elim_cands:                        0
% 7.06/1.57  pred_elim:                              0
% 7.06/1.57  pred_elim_cl:                           0
% 7.06/1.57  pred_elim_cycles:                       0
% 7.06/1.57  merged_defs:                            0
% 7.06/1.57  merged_defs_ncl:                        0
% 7.06/1.57  bin_hyper_res:                          0
% 7.06/1.57  prep_cycles:                            2
% 7.06/1.57  pred_elim_time:                         0.016
% 7.06/1.57  splitting_time:                         0.
% 7.06/1.57  sem_filter_time:                        0.
% 7.06/1.57  monotx_time:                            0.
% 7.06/1.57  subtype_inf_time:                       0.
% 7.06/1.57  
% 7.06/1.57  ------ Problem properties
% 7.06/1.57  
% 7.06/1.57  clauses:                                8
% 7.06/1.57  conjectures:                            1
% 7.06/1.57  epr:                                    0
% 7.06/1.57  horn:                                   8
% 7.06/1.57  ground:                                 1
% 7.06/1.57  unary:                                  8
% 7.06/1.57  binary:                                 0
% 7.06/1.57  lits:                                   8
% 7.06/1.57  lits_eq:                                8
% 7.06/1.57  fd_pure:                                0
% 7.06/1.57  fd_pseudo:                              0
% 7.06/1.57  fd_cond:                                0
% 7.06/1.57  fd_pseudo_cond:                         0
% 7.06/1.57  ac_symbols:                             0
% 7.06/1.57  
% 7.06/1.57  ------ Propositional Solver
% 7.06/1.57  
% 7.06/1.57  prop_solver_calls:                      13
% 7.06/1.57  prop_fast_solver_calls:                 52
% 7.06/1.57  smt_solver_calls:                       0
% 7.06/1.57  smt_fast_solver_calls:                  0
% 7.06/1.57  prop_num_of_clauses:                    193
% 7.06/1.57  prop_preprocess_simplified:             341
% 7.06/1.57  prop_fo_subsumed:                       0
% 7.06/1.57  prop_solver_time:                       0.
% 7.06/1.57  smt_solver_time:                        0.
% 7.06/1.57  smt_fast_solver_time:                   0.
% 7.06/1.57  prop_fast_solver_time:                  0.
% 7.06/1.57  prop_unsat_core_time:                   0.
% 7.06/1.57  
% 7.06/1.57  ------ QBF
% 7.06/1.57  
% 7.06/1.57  qbf_q_res:                              0
% 7.06/1.57  qbf_num_tautologies:                    0
% 7.06/1.57  qbf_prep_cycles:                        0
% 7.06/1.57  
% 7.06/1.57  ------ BMC1
% 7.06/1.57  
% 7.06/1.57  bmc1_current_bound:                     -1
% 7.06/1.57  bmc1_last_solved_bound:                 -1
% 7.06/1.57  bmc1_unsat_core_size:                   -1
% 7.06/1.57  bmc1_unsat_core_parents_size:           -1
% 7.06/1.57  bmc1_merge_next_fun:                    0
% 7.06/1.57  bmc1_unsat_core_clauses_time:           0.
% 7.06/1.57  
% 7.06/1.57  ------ Instantiation
% 7.06/1.57  
% 7.06/1.57  inst_num_of_clauses:                    0
% 7.06/1.57  inst_num_in_passive:                    0
% 7.06/1.57  inst_num_in_active:                     0
% 7.06/1.57  inst_num_in_unprocessed:                0
% 7.06/1.57  inst_num_of_loops:                      0
% 7.06/1.57  inst_num_of_learning_restarts:          0
% 7.06/1.57  inst_num_moves_active_passive:          0
% 7.06/1.57  inst_lit_activity:                      0
% 7.06/1.57  inst_lit_activity_moves:                0
% 7.06/1.57  inst_num_tautologies:                   0
% 7.06/1.57  inst_num_prop_implied:                  0
% 7.06/1.57  inst_num_existing_simplified:           0
% 7.06/1.57  inst_num_eq_res_simplified:             0
% 7.06/1.57  inst_num_child_elim:                    0
% 7.06/1.57  inst_num_of_dismatching_blockings:      0
% 7.06/1.57  inst_num_of_non_proper_insts:           0
% 7.06/1.57  inst_num_of_duplicates:                 0
% 7.06/1.57  inst_inst_num_from_inst_to_res:         0
% 7.06/1.57  inst_dismatching_checking_time:         0.
% 7.06/1.57  
% 7.06/1.57  ------ Resolution
% 7.06/1.57  
% 7.06/1.57  res_num_of_clauses:                     0
% 7.06/1.57  res_num_in_passive:                     0
% 7.06/1.57  res_num_in_active:                      0
% 7.06/1.57  res_num_of_loops:                       22
% 7.06/1.57  res_forward_subset_subsumed:            0
% 7.06/1.57  res_backward_subset_subsumed:           0
% 7.06/1.57  res_forward_subsumed:                   0
% 7.06/1.57  res_backward_subsumed:                  0
% 7.06/1.57  res_forward_subsumption_resolution:     0
% 7.06/1.57  res_backward_subsumption_resolution:    0
% 7.06/1.57  res_clause_to_clause_subsumption:       63012
% 7.06/1.57  res_orphan_elimination:                 0
% 7.06/1.57  res_tautology_del:                      0
% 7.06/1.57  res_num_eq_res_simplified:              0
% 7.06/1.57  res_num_sel_changes:                    0
% 7.06/1.57  res_moves_from_active_to_pass:          0
% 7.06/1.57  
% 7.06/1.57  ------ Superposition
% 7.06/1.57  
% 7.06/1.57  sup_time_total:                         0.
% 7.06/1.57  sup_time_generating:                    0.
% 7.06/1.57  sup_time_sim_full:                      0.
% 7.06/1.57  sup_time_sim_immed:                     0.
% 7.06/1.57  
% 7.06/1.57  sup_num_of_clauses:                     1828
% 7.06/1.57  sup_num_in_active:                      107
% 7.06/1.57  sup_num_in_passive:                     1721
% 7.06/1.57  sup_num_of_loops:                       127
% 7.06/1.57  sup_fw_superposition:                   5541
% 7.06/1.57  sup_bw_superposition:                   4993
% 7.06/1.57  sup_immediate_simplified:               6519
% 7.06/1.57  sup_given_eliminated:                   4
% 7.06/1.57  comparisons_done:                       0
% 7.06/1.57  comparisons_avoided:                    0
% 7.06/1.57  
% 7.06/1.57  ------ Simplifications
% 7.06/1.57  
% 7.06/1.57  
% 7.06/1.57  sim_fw_subset_subsumed:                 0
% 7.06/1.57  sim_bw_subset_subsumed:                 0
% 7.06/1.57  sim_fw_subsumed:                        563
% 7.06/1.57  sim_bw_subsumed:                        12
% 7.06/1.57  sim_fw_subsumption_res:                 0
% 7.06/1.57  sim_bw_subsumption_res:                 0
% 7.06/1.57  sim_tautology_del:                      0
% 7.06/1.57  sim_eq_tautology_del:                   1369
% 7.06/1.57  sim_eq_res_simp:                        0
% 7.06/1.57  sim_fw_demodulated:                     4818
% 7.06/1.57  sim_bw_demodulated:                     57
% 7.06/1.57  sim_light_normalised:                   2500
% 7.06/1.57  sim_joinable_taut:                      0
% 7.06/1.57  sim_joinable_simp:                      0
% 7.06/1.57  sim_ac_normalised:                      0
% 7.06/1.57  sim_smt_subsumption:                    0
% 7.06/1.57  
%------------------------------------------------------------------------------
