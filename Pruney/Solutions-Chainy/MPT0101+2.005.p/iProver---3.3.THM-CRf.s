%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:58 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  149 (4601 expanded)
%              Number of clauses        :  114 (1899 expanded)
%              Number of leaves         :   14 (1230 expanded)
%              Depth                    :   28
%              Number of atoms          :  150 (4602 expanded)
%              Number of equality atoms :  149 (4601 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f22])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f28,f28])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f34,f22,f22,f28])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_38,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11,c_8])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_61,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_38,c_2])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_63,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_61,c_3])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_160,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_63,c_5])).

cnf(c_161,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_160,c_4])).

cnf(c_196,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_161,c_4])).

cnf(c_198,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_196,c_2])).

cnf(c_478,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_198])).

cnf(c_967,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_4,c_478])).

cnf(c_1016,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_967,c_478])).

cnf(c_156,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_63,c_5])).

cnf(c_163,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_156,c_8])).

cnf(c_982,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_478,c_163])).

cnf(c_113,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_7774,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_982,c_113])).

cnf(c_7961,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7774,c_2])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_30,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_10,c_9,c_0])).

cnf(c_76,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_30])).

cnf(c_171,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_76])).

cnf(c_289,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_161,c_171])).

cnf(c_295,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_289,c_61])).

cnf(c_8064,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) ),
    inference(superposition,[status(thm)],[c_7961,c_295])).

cnf(c_8115,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_8064,c_7961])).

cnf(c_101,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_9096,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_8115,c_101])).

cnf(c_9131,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_9096,c_61,c_161])).

cnf(c_9205,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1016,c_9131])).

cnf(c_186,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_161])).

cnf(c_433,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_186,c_171])).

cnf(c_454,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_433,c_5])).

cnf(c_455,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_454,c_2])).

cnf(c_3397,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_455])).

cnf(c_9215,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3397,c_9131])).

cnf(c_9255,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9131,c_1])).

cnf(c_9285,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9255,c_61,c_163])).

cnf(c_9310,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_9215,c_9285])).

cnf(c_9321,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_9205,c_9310])).

cnf(c_9418,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9321,c_5])).

cnf(c_7800,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_1016,c_113])).

cnf(c_7944,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_7800,c_113])).

cnf(c_9432,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9418,c_7944])).

cnf(c_288,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_163,c_171])).

cnf(c_296,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_288,c_61])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_12,c_9,c_0])).

cnf(c_40,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_29,c_5])).

cnf(c_792,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_296,c_40])).

cnf(c_29637,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_9432,c_792])).

cnf(c_1482,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1016,c_0])).

cnf(c_216,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_163,c_4])).

cnf(c_218,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_216,c_2])).

cnf(c_568,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_218,c_9])).

cnf(c_9206,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_568,c_9131])).

cnf(c_9319,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9206,c_9131])).

cnf(c_178,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_76,c_0])).

cnf(c_41,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_856,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_178,c_41])).

cnf(c_9212,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_856,c_9131])).

cnf(c_9320,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9319,c_9212])).

cnf(c_209,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_76,c_163])).

cnf(c_256,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_209,c_5])).

cnf(c_267,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_256,c_5,c_8])).

cnf(c_1462,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_267,c_1016])).

cnf(c_1466,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_982,c_1016])).

cnf(c_548,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_218])).

cnf(c_1106,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_548,c_218])).

cnf(c_1141,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1106,c_548])).

cnf(c_1508,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1466,c_1141])).

cnf(c_1514,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1462,c_1508])).

cnf(c_29428,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_9320,c_1514])).

cnf(c_193,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_161,c_5])).

cnf(c_199,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_193,c_8])).

cnf(c_8575,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X0) ),
    inference(superposition,[status(thm)],[c_199,c_3397])).

cnf(c_764,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_9,c_295])).

cnf(c_782,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_295,c_9])).

cnf(c_790,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_764,c_782])).

cnf(c_8790,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_8575,c_790])).

cnf(c_887,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_41,c_267])).

cnf(c_5207,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k2_xboole_0(X0,X3))) ),
    inference(superposition,[status(thm)],[c_887,c_1016])).

cnf(c_391,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_76,c_9])).

cnf(c_43,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_2752,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_391,c_43])).

cnf(c_981,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_478,c_9])).

cnf(c_561,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_218,c_9])).

cnf(c_571,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_561,c_9])).

cnf(c_1009,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_981,c_571])).

cnf(c_2778,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_2752,c_1009])).

cnf(c_5252,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5207,c_2778])).

cnf(c_711,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_267])).

cnf(c_1259,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_711,c_4])).

cnf(c_1263,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1259,c_2,c_1009])).

cnf(c_42,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_6494,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1263,c_42])).

cnf(c_6524,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_6494,c_1009,c_1514])).

cnf(c_8791,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_8790,c_478,c_5252,c_6524])).

cnf(c_29606,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3) = k2_xboole_0(X0,k2_xboole_0(X3,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_29428,c_1514,c_8791])).

cnf(c_29638,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_29637,c_1482,c_29606])).

cnf(c_1087,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_4,c_548])).

cnf(c_443,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_186,c_4])).

cnf(c_448,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_443,c_2])).

cnf(c_1147,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1087,c_448])).

cnf(c_1839,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_30,c_43])).

cnf(c_29639,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_29638,c_1147,c_1839])).

cnf(c_29640,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_29639])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:29:34 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 7.80/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/1.47  
% 7.80/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.47  
% 7.80/1.47  ------  iProver source info
% 7.80/1.47  
% 7.80/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.47  git: non_committed_changes: false
% 7.80/1.47  git: last_make_outside_of_git: false
% 7.80/1.47  
% 7.80/1.47  ------ 
% 7.80/1.47  
% 7.80/1.47  ------ Input Options
% 7.80/1.47  
% 7.80/1.47  --out_options                           all
% 7.80/1.47  --tptp_safe_out                         true
% 7.80/1.47  --problem_path                          ""
% 7.80/1.47  --include_path                          ""
% 7.80/1.47  --clausifier                            res/vclausify_rel
% 7.80/1.47  --clausifier_options                    --mode clausify
% 7.80/1.47  --stdin                                 false
% 7.80/1.47  --stats_out                             all
% 7.80/1.47  
% 7.80/1.47  ------ General Options
% 7.80/1.47  
% 7.80/1.47  --fof                                   false
% 7.80/1.47  --time_out_real                         305.
% 7.80/1.47  --time_out_virtual                      -1.
% 7.80/1.47  --symbol_type_check                     false
% 7.80/1.47  --clausify_out                          false
% 7.80/1.47  --sig_cnt_out                           false
% 7.80/1.47  --trig_cnt_out                          false
% 7.80/1.47  --trig_cnt_out_tolerance                1.
% 7.80/1.47  --trig_cnt_out_sk_spl                   false
% 7.80/1.47  --abstr_cl_out                          false
% 7.80/1.47  
% 7.80/1.47  ------ Global Options
% 7.80/1.47  
% 7.80/1.47  --schedule                              default
% 7.80/1.47  --add_important_lit                     false
% 7.80/1.47  --prop_solver_per_cl                    1000
% 7.80/1.47  --min_unsat_core                        false
% 7.80/1.47  --soft_assumptions                      false
% 7.80/1.47  --soft_lemma_size                       3
% 7.80/1.47  --prop_impl_unit_size                   0
% 7.80/1.47  --prop_impl_unit                        []
% 7.80/1.47  --share_sel_clauses                     true
% 7.80/1.47  --reset_solvers                         false
% 7.80/1.47  --bc_imp_inh                            [conj_cone]
% 7.80/1.47  --conj_cone_tolerance                   3.
% 7.80/1.47  --extra_neg_conj                        none
% 7.80/1.47  --large_theory_mode                     true
% 7.80/1.47  --prolific_symb_bound                   200
% 7.80/1.47  --lt_threshold                          2000
% 7.80/1.47  --clause_weak_htbl                      true
% 7.80/1.47  --gc_record_bc_elim                     false
% 7.80/1.47  
% 7.80/1.47  ------ Preprocessing Options
% 7.80/1.47  
% 7.80/1.47  --preprocessing_flag                    true
% 7.80/1.47  --time_out_prep_mult                    0.1
% 7.80/1.47  --splitting_mode                        input
% 7.80/1.47  --splitting_grd                         true
% 7.80/1.47  --splitting_cvd                         false
% 7.80/1.47  --splitting_cvd_svl                     false
% 7.80/1.47  --splitting_nvd                         32
% 7.80/1.47  --sub_typing                            true
% 7.80/1.47  --prep_gs_sim                           true
% 7.80/1.47  --prep_unflatten                        true
% 7.80/1.47  --prep_res_sim                          true
% 7.80/1.47  --prep_upred                            true
% 7.80/1.47  --prep_sem_filter                       exhaustive
% 7.80/1.47  --prep_sem_filter_out                   false
% 7.80/1.47  --pred_elim                             true
% 7.80/1.47  --res_sim_input                         true
% 7.80/1.47  --eq_ax_congr_red                       true
% 7.80/1.47  --pure_diseq_elim                       true
% 7.80/1.47  --brand_transform                       false
% 7.80/1.47  --non_eq_to_eq                          false
% 7.80/1.47  --prep_def_merge                        true
% 7.80/1.47  --prep_def_merge_prop_impl              false
% 7.80/1.47  --prep_def_merge_mbd                    true
% 7.80/1.47  --prep_def_merge_tr_red                 false
% 7.80/1.47  --prep_def_merge_tr_cl                  false
% 7.80/1.47  --smt_preprocessing                     true
% 7.80/1.47  --smt_ac_axioms                         fast
% 7.80/1.47  --preprocessed_out                      false
% 7.80/1.47  --preprocessed_stats                    false
% 7.80/1.47  
% 7.80/1.47  ------ Abstraction refinement Options
% 7.80/1.47  
% 7.80/1.47  --abstr_ref                             []
% 7.80/1.47  --abstr_ref_prep                        false
% 7.80/1.47  --abstr_ref_until_sat                   false
% 7.80/1.47  --abstr_ref_sig_restrict                funpre
% 7.80/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.47  --abstr_ref_under                       []
% 7.80/1.47  
% 7.80/1.47  ------ SAT Options
% 7.80/1.47  
% 7.80/1.47  --sat_mode                              false
% 7.80/1.47  --sat_fm_restart_options                ""
% 7.80/1.47  --sat_gr_def                            false
% 7.80/1.47  --sat_epr_types                         true
% 7.80/1.47  --sat_non_cyclic_types                  false
% 7.80/1.47  --sat_finite_models                     false
% 7.80/1.47  --sat_fm_lemmas                         false
% 7.80/1.47  --sat_fm_prep                           false
% 7.80/1.47  --sat_fm_uc_incr                        true
% 7.80/1.47  --sat_out_model                         small
% 7.80/1.47  --sat_out_clauses                       false
% 7.80/1.47  
% 7.80/1.47  ------ QBF Options
% 7.80/1.47  
% 7.80/1.47  --qbf_mode                              false
% 7.80/1.47  --qbf_elim_univ                         false
% 7.80/1.47  --qbf_dom_inst                          none
% 7.80/1.47  --qbf_dom_pre_inst                      false
% 7.80/1.47  --qbf_sk_in                             false
% 7.80/1.47  --qbf_pred_elim                         true
% 7.80/1.47  --qbf_split                             512
% 7.80/1.47  
% 7.80/1.47  ------ BMC1 Options
% 7.80/1.47  
% 7.80/1.47  --bmc1_incremental                      false
% 7.80/1.47  --bmc1_axioms                           reachable_all
% 7.80/1.47  --bmc1_min_bound                        0
% 7.80/1.47  --bmc1_max_bound                        -1
% 7.80/1.47  --bmc1_max_bound_default                -1
% 7.80/1.47  --bmc1_symbol_reachability              true
% 7.80/1.47  --bmc1_property_lemmas                  false
% 7.80/1.47  --bmc1_k_induction                      false
% 7.80/1.47  --bmc1_non_equiv_states                 false
% 7.80/1.47  --bmc1_deadlock                         false
% 7.80/1.47  --bmc1_ucm                              false
% 7.80/1.47  --bmc1_add_unsat_core                   none
% 7.80/1.47  --bmc1_unsat_core_children              false
% 7.80/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.47  --bmc1_out_stat                         full
% 7.80/1.47  --bmc1_ground_init                      false
% 7.80/1.47  --bmc1_pre_inst_next_state              false
% 7.80/1.47  --bmc1_pre_inst_state                   false
% 7.80/1.47  --bmc1_pre_inst_reach_state             false
% 7.80/1.47  --bmc1_out_unsat_core                   false
% 7.80/1.47  --bmc1_aig_witness_out                  false
% 7.80/1.47  --bmc1_verbose                          false
% 7.80/1.47  --bmc1_dump_clauses_tptp                false
% 7.80/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.47  --bmc1_dump_file                        -
% 7.80/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.47  --bmc1_ucm_extend_mode                  1
% 7.80/1.47  --bmc1_ucm_init_mode                    2
% 7.80/1.47  --bmc1_ucm_cone_mode                    none
% 7.80/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.47  --bmc1_ucm_relax_model                  4
% 7.80/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.47  --bmc1_ucm_layered_model                none
% 7.80/1.47  --bmc1_ucm_max_lemma_size               10
% 7.80/1.47  
% 7.80/1.47  ------ AIG Options
% 7.80/1.47  
% 7.80/1.47  --aig_mode                              false
% 7.80/1.47  
% 7.80/1.47  ------ Instantiation Options
% 7.80/1.47  
% 7.80/1.47  --instantiation_flag                    true
% 7.80/1.47  --inst_sos_flag                         false
% 7.80/1.47  --inst_sos_phase                        true
% 7.80/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.47  --inst_lit_sel_side                     num_symb
% 7.80/1.47  --inst_solver_per_active                1400
% 7.80/1.47  --inst_solver_calls_frac                1.
% 7.80/1.47  --inst_passive_queue_type               priority_queues
% 7.80/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.47  --inst_passive_queues_freq              [25;2]
% 7.80/1.47  --inst_dismatching                      true
% 7.80/1.47  --inst_eager_unprocessed_to_passive     true
% 7.80/1.47  --inst_prop_sim_given                   true
% 7.80/1.47  --inst_prop_sim_new                     false
% 7.80/1.47  --inst_subs_new                         false
% 7.80/1.47  --inst_eq_res_simp                      false
% 7.80/1.47  --inst_subs_given                       false
% 7.80/1.47  --inst_orphan_elimination               true
% 7.80/1.47  --inst_learning_loop_flag               true
% 7.80/1.47  --inst_learning_start                   3000
% 7.80/1.47  --inst_learning_factor                  2
% 7.80/1.47  --inst_start_prop_sim_after_learn       3
% 7.80/1.47  --inst_sel_renew                        solver
% 7.80/1.47  --inst_lit_activity_flag                true
% 7.80/1.47  --inst_restr_to_given                   false
% 7.80/1.47  --inst_activity_threshold               500
% 7.80/1.47  --inst_out_proof                        true
% 7.80/1.47  
% 7.80/1.47  ------ Resolution Options
% 7.80/1.47  
% 7.80/1.47  --resolution_flag                       true
% 7.80/1.47  --res_lit_sel                           adaptive
% 7.80/1.47  --res_lit_sel_side                      none
% 7.80/1.47  --res_ordering                          kbo
% 7.80/1.47  --res_to_prop_solver                    active
% 7.80/1.47  --res_prop_simpl_new                    false
% 7.80/1.47  --res_prop_simpl_given                  true
% 7.80/1.47  --res_passive_queue_type                priority_queues
% 7.80/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.47  --res_passive_queues_freq               [15;5]
% 7.80/1.47  --res_forward_subs                      full
% 7.80/1.47  --res_backward_subs                     full
% 7.80/1.47  --res_forward_subs_resolution           true
% 7.80/1.47  --res_backward_subs_resolution          true
% 7.80/1.47  --res_orphan_elimination                true
% 7.80/1.47  --res_time_limit                        2.
% 7.80/1.47  --res_out_proof                         true
% 7.80/1.47  
% 7.80/1.47  ------ Superposition Options
% 7.80/1.47  
% 7.80/1.47  --superposition_flag                    true
% 7.80/1.47  --sup_passive_queue_type                priority_queues
% 7.80/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.47  --demod_completeness_check              fast
% 7.80/1.47  --demod_use_ground                      true
% 7.80/1.47  --sup_to_prop_solver                    passive
% 7.80/1.47  --sup_prop_simpl_new                    true
% 7.80/1.47  --sup_prop_simpl_given                  true
% 7.80/1.47  --sup_fun_splitting                     false
% 7.80/1.47  --sup_smt_interval                      50000
% 7.80/1.47  
% 7.80/1.47  ------ Superposition Simplification Setup
% 7.80/1.47  
% 7.80/1.47  --sup_indices_passive                   []
% 7.80/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.47  --sup_full_bw                           [BwDemod]
% 7.80/1.47  --sup_immed_triv                        [TrivRules]
% 7.80/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.47  --sup_immed_bw_main                     []
% 7.80/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.80/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.80/1.47  
% 7.80/1.47  ------ Combination Options
% 7.80/1.47  
% 7.80/1.47  --comb_res_mult                         3
% 7.80/1.47  --comb_sup_mult                         2
% 7.80/1.47  --comb_inst_mult                        10
% 7.80/1.47  
% 7.80/1.47  ------ Debug Options
% 7.80/1.47  
% 7.80/1.47  --dbg_backtrace                         false
% 7.80/1.47  --dbg_dump_prop_clauses                 false
% 7.80/1.47  --dbg_dump_prop_clauses_file            -
% 7.80/1.47  --dbg_out_stat                          false
% 7.80/1.47  ------ Parsing...
% 7.80/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.47  
% 7.80/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.80/1.47  
% 7.80/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.47  
% 7.80/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.47  ------ Proving...
% 7.80/1.47  ------ Problem Properties 
% 7.80/1.47  
% 7.80/1.47  
% 7.80/1.47  clauses                                 13
% 7.80/1.47  conjectures                             1
% 7.80/1.47  EPR                                     0
% 7.80/1.47  Horn                                    13
% 7.80/1.47  unary                                   13
% 7.80/1.47  binary                                  0
% 7.80/1.47  lits                                    13
% 7.80/1.47  lits eq                                 13
% 7.80/1.47  fd_pure                                 0
% 7.80/1.47  fd_pseudo                               0
% 7.80/1.47  fd_cond                                 0
% 7.80/1.47  fd_pseudo_cond                          0
% 7.80/1.47  AC symbols                              1
% 7.80/1.47  
% 7.80/1.47  ------ Schedule UEQ
% 7.80/1.47  
% 7.80/1.47  ------ pure equality problem: resolution off 
% 7.80/1.47  
% 7.80/1.47  ------ Option_UEQ Time Limit: Unbounded
% 7.80/1.47  
% 7.80/1.47  
% 7.80/1.47  ------ 
% 7.80/1.47  Current options:
% 7.80/1.47  ------ 
% 7.80/1.47  
% 7.80/1.47  ------ Input Options
% 7.80/1.47  
% 7.80/1.47  --out_options                           all
% 7.80/1.47  --tptp_safe_out                         true
% 7.80/1.47  --problem_path                          ""
% 7.80/1.47  --include_path                          ""
% 7.80/1.47  --clausifier                            res/vclausify_rel
% 7.80/1.47  --clausifier_options                    --mode clausify
% 7.80/1.47  --stdin                                 false
% 7.80/1.47  --stats_out                             all
% 7.80/1.47  
% 7.80/1.47  ------ General Options
% 7.80/1.47  
% 7.80/1.47  --fof                                   false
% 7.80/1.47  --time_out_real                         305.
% 7.80/1.47  --time_out_virtual                      -1.
% 7.80/1.47  --symbol_type_check                     false
% 7.80/1.47  --clausify_out                          false
% 7.80/1.47  --sig_cnt_out                           false
% 7.80/1.47  --trig_cnt_out                          false
% 7.80/1.47  --trig_cnt_out_tolerance                1.
% 7.80/1.47  --trig_cnt_out_sk_spl                   false
% 7.80/1.47  --abstr_cl_out                          false
% 7.80/1.47  
% 7.80/1.47  ------ Global Options
% 7.80/1.47  
% 7.80/1.47  --schedule                              default
% 7.80/1.47  --add_important_lit                     false
% 7.80/1.47  --prop_solver_per_cl                    1000
% 7.80/1.47  --min_unsat_core                        false
% 7.80/1.47  --soft_assumptions                      false
% 7.80/1.47  --soft_lemma_size                       3
% 7.80/1.47  --prop_impl_unit_size                   0
% 7.80/1.47  --prop_impl_unit                        []
% 7.80/1.47  --share_sel_clauses                     true
% 7.80/1.47  --reset_solvers                         false
% 7.80/1.47  --bc_imp_inh                            [conj_cone]
% 7.80/1.47  --conj_cone_tolerance                   3.
% 7.80/1.47  --extra_neg_conj                        none
% 7.80/1.47  --large_theory_mode                     true
% 7.80/1.47  --prolific_symb_bound                   200
% 7.80/1.47  --lt_threshold                          2000
% 7.80/1.47  --clause_weak_htbl                      true
% 7.80/1.47  --gc_record_bc_elim                     false
% 7.80/1.47  
% 7.80/1.47  ------ Preprocessing Options
% 7.80/1.47  
% 7.80/1.47  --preprocessing_flag                    true
% 7.80/1.47  --time_out_prep_mult                    0.1
% 7.80/1.47  --splitting_mode                        input
% 7.80/1.47  --splitting_grd                         true
% 7.80/1.47  --splitting_cvd                         false
% 7.80/1.47  --splitting_cvd_svl                     false
% 7.80/1.47  --splitting_nvd                         32
% 7.80/1.47  --sub_typing                            true
% 7.80/1.47  --prep_gs_sim                           true
% 7.80/1.47  --prep_unflatten                        true
% 7.80/1.47  --prep_res_sim                          true
% 7.80/1.47  --prep_upred                            true
% 7.80/1.47  --prep_sem_filter                       exhaustive
% 7.80/1.47  --prep_sem_filter_out                   false
% 7.80/1.47  --pred_elim                             true
% 7.80/1.47  --res_sim_input                         true
% 7.80/1.47  --eq_ax_congr_red                       true
% 7.80/1.47  --pure_diseq_elim                       true
% 7.80/1.47  --brand_transform                       false
% 7.80/1.47  --non_eq_to_eq                          false
% 7.80/1.47  --prep_def_merge                        true
% 7.80/1.47  --prep_def_merge_prop_impl              false
% 7.80/1.47  --prep_def_merge_mbd                    true
% 7.80/1.47  --prep_def_merge_tr_red                 false
% 7.80/1.47  --prep_def_merge_tr_cl                  false
% 7.80/1.47  --smt_preprocessing                     true
% 7.80/1.47  --smt_ac_axioms                         fast
% 7.80/1.47  --preprocessed_out                      false
% 7.80/1.47  --preprocessed_stats                    false
% 7.80/1.47  
% 7.80/1.47  ------ Abstraction refinement Options
% 7.80/1.47  
% 7.80/1.47  --abstr_ref                             []
% 7.80/1.47  --abstr_ref_prep                        false
% 7.80/1.47  --abstr_ref_until_sat                   false
% 7.80/1.47  --abstr_ref_sig_restrict                funpre
% 7.80/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.47  --abstr_ref_under                       []
% 7.80/1.47  
% 7.80/1.47  ------ SAT Options
% 7.80/1.47  
% 7.80/1.47  --sat_mode                              false
% 7.80/1.47  --sat_fm_restart_options                ""
% 7.80/1.47  --sat_gr_def                            false
% 7.80/1.47  --sat_epr_types                         true
% 7.80/1.47  --sat_non_cyclic_types                  false
% 7.80/1.47  --sat_finite_models                     false
% 7.80/1.47  --sat_fm_lemmas                         false
% 7.80/1.47  --sat_fm_prep                           false
% 7.80/1.47  --sat_fm_uc_incr                        true
% 7.80/1.47  --sat_out_model                         small
% 7.80/1.47  --sat_out_clauses                       false
% 7.80/1.47  
% 7.80/1.47  ------ QBF Options
% 7.80/1.47  
% 7.80/1.47  --qbf_mode                              false
% 7.80/1.47  --qbf_elim_univ                         false
% 7.80/1.47  --qbf_dom_inst                          none
% 7.80/1.47  --qbf_dom_pre_inst                      false
% 7.80/1.47  --qbf_sk_in                             false
% 7.80/1.47  --qbf_pred_elim                         true
% 7.80/1.47  --qbf_split                             512
% 7.80/1.47  
% 7.80/1.47  ------ BMC1 Options
% 7.80/1.47  
% 7.80/1.47  --bmc1_incremental                      false
% 7.80/1.47  --bmc1_axioms                           reachable_all
% 7.80/1.47  --bmc1_min_bound                        0
% 7.80/1.47  --bmc1_max_bound                        -1
% 7.80/1.47  --bmc1_max_bound_default                -1
% 7.80/1.47  --bmc1_symbol_reachability              true
% 7.80/1.47  --bmc1_property_lemmas                  false
% 7.80/1.47  --bmc1_k_induction                      false
% 7.80/1.47  --bmc1_non_equiv_states                 false
% 7.80/1.47  --bmc1_deadlock                         false
% 7.80/1.47  --bmc1_ucm                              false
% 7.80/1.47  --bmc1_add_unsat_core                   none
% 7.80/1.47  --bmc1_unsat_core_children              false
% 7.80/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.47  --bmc1_out_stat                         full
% 7.80/1.47  --bmc1_ground_init                      false
% 7.80/1.47  --bmc1_pre_inst_next_state              false
% 7.80/1.47  --bmc1_pre_inst_state                   false
% 7.80/1.47  --bmc1_pre_inst_reach_state             false
% 7.80/1.47  --bmc1_out_unsat_core                   false
% 7.80/1.47  --bmc1_aig_witness_out                  false
% 7.80/1.47  --bmc1_verbose                          false
% 7.80/1.47  --bmc1_dump_clauses_tptp                false
% 7.80/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.47  --bmc1_dump_file                        -
% 7.80/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.47  --bmc1_ucm_extend_mode                  1
% 7.80/1.47  --bmc1_ucm_init_mode                    2
% 7.80/1.47  --bmc1_ucm_cone_mode                    none
% 7.80/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.47  --bmc1_ucm_relax_model                  4
% 7.80/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.47  --bmc1_ucm_layered_model                none
% 7.80/1.47  --bmc1_ucm_max_lemma_size               10
% 7.80/1.47  
% 7.80/1.47  ------ AIG Options
% 7.80/1.47  
% 7.80/1.47  --aig_mode                              false
% 7.80/1.47  
% 7.80/1.47  ------ Instantiation Options
% 7.80/1.47  
% 7.80/1.47  --instantiation_flag                    false
% 7.80/1.47  --inst_sos_flag                         false
% 7.80/1.47  --inst_sos_phase                        true
% 7.80/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.47  --inst_lit_sel_side                     num_symb
% 7.80/1.47  --inst_solver_per_active                1400
% 7.80/1.47  --inst_solver_calls_frac                1.
% 7.80/1.47  --inst_passive_queue_type               priority_queues
% 7.80/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.47  --inst_passive_queues_freq              [25;2]
% 7.80/1.47  --inst_dismatching                      true
% 7.80/1.47  --inst_eager_unprocessed_to_passive     true
% 7.80/1.47  --inst_prop_sim_given                   true
% 7.80/1.47  --inst_prop_sim_new                     false
% 7.80/1.47  --inst_subs_new                         false
% 7.80/1.47  --inst_eq_res_simp                      false
% 7.80/1.47  --inst_subs_given                       false
% 7.80/1.47  --inst_orphan_elimination               true
% 7.80/1.47  --inst_learning_loop_flag               true
% 7.80/1.47  --inst_learning_start                   3000
% 7.80/1.47  --inst_learning_factor                  2
% 7.80/1.47  --inst_start_prop_sim_after_learn       3
% 7.80/1.47  --inst_sel_renew                        solver
% 7.80/1.47  --inst_lit_activity_flag                true
% 7.80/1.47  --inst_restr_to_given                   false
% 7.80/1.47  --inst_activity_threshold               500
% 7.80/1.47  --inst_out_proof                        true
% 7.80/1.47  
% 7.80/1.47  ------ Resolution Options
% 7.80/1.47  
% 7.80/1.47  --resolution_flag                       false
% 7.80/1.47  --res_lit_sel                           adaptive
% 7.80/1.47  --res_lit_sel_side                      none
% 7.80/1.47  --res_ordering                          kbo
% 7.80/1.47  --res_to_prop_solver                    active
% 7.80/1.47  --res_prop_simpl_new                    false
% 7.80/1.47  --res_prop_simpl_given                  true
% 7.80/1.47  --res_passive_queue_type                priority_queues
% 7.80/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.47  --res_passive_queues_freq               [15;5]
% 7.80/1.47  --res_forward_subs                      full
% 7.80/1.47  --res_backward_subs                     full
% 7.80/1.47  --res_forward_subs_resolution           true
% 7.80/1.47  --res_backward_subs_resolution          true
% 7.80/1.47  --res_orphan_elimination                true
% 7.80/1.47  --res_time_limit                        2.
% 7.80/1.47  --res_out_proof                         true
% 7.80/1.47  
% 7.80/1.47  ------ Superposition Options
% 7.80/1.47  
% 7.80/1.47  --superposition_flag                    true
% 7.80/1.47  --sup_passive_queue_type                priority_queues
% 7.80/1.47  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.47  --demod_completeness_check              fast
% 7.80/1.47  --demod_use_ground                      true
% 7.80/1.47  --sup_to_prop_solver                    active
% 7.80/1.47  --sup_prop_simpl_new                    false
% 7.80/1.47  --sup_prop_simpl_given                  false
% 7.80/1.47  --sup_fun_splitting                     true
% 7.80/1.47  --sup_smt_interval                      10000
% 7.80/1.47  
% 7.80/1.47  ------ Superposition Simplification Setup
% 7.80/1.47  
% 7.80/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.80/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.80/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.47  --sup_full_triv                         [TrivRules]
% 7.80/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.80/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.80/1.47  --sup_immed_triv                        [TrivRules]
% 7.80/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.47  --sup_immed_bw_main                     []
% 7.80/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.80/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.47  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.80/1.47  
% 7.80/1.47  ------ Combination Options
% 7.80/1.47  
% 7.80/1.47  --comb_res_mult                         1
% 7.80/1.47  --comb_sup_mult                         1
% 7.80/1.47  --comb_inst_mult                        1000000
% 7.80/1.47  
% 7.80/1.47  ------ Debug Options
% 7.80/1.47  
% 7.80/1.47  --dbg_backtrace                         false
% 7.80/1.47  --dbg_dump_prop_clauses                 false
% 7.80/1.47  --dbg_dump_prop_clauses_file            -
% 7.80/1.47  --dbg_out_stat                          false
% 7.80/1.47  
% 7.80/1.47  
% 7.80/1.47  
% 7.80/1.47  
% 7.80/1.47  ------ Proving...
% 7.80/1.47  
% 7.80/1.47  
% 7.80/1.47  % SZS status Theorem for theBenchmark.p
% 7.80/1.47  
% 7.80/1.47   Resolution empty clause
% 7.80/1.47  
% 7.80/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.47  
% 7.80/1.47  fof(f6,axiom,(
% 7.80/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f25,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.80/1.47    inference(cnf_transformation,[],[f6])).
% 7.80/1.47  
% 7.80/1.47  fof(f1,axiom,(
% 7.80/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f20,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.80/1.47    inference(cnf_transformation,[],[f1])).
% 7.80/1.47  
% 7.80/1.47  fof(f14,axiom,(
% 7.80/1.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f33,plain,(
% 7.80/1.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.80/1.47    inference(cnf_transformation,[],[f14])).
% 7.80/1.47  
% 7.80/1.47  fof(f3,axiom,(
% 7.80/1.47    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f22,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.80/1.47    inference(cnf_transformation,[],[f3])).
% 7.80/1.47  
% 7.80/1.47  fof(f40,plain,(
% 7.80/1.47    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 7.80/1.47    inference(definition_unfolding,[],[f33,f22])).
% 7.80/1.47  
% 7.80/1.47  fof(f11,axiom,(
% 7.80/1.47    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f30,plain,(
% 7.80/1.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.80/1.47    inference(cnf_transformation,[],[f11])).
% 7.80/1.47  
% 7.80/1.47  fof(f4,axiom,(
% 7.80/1.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f23,plain,(
% 7.80/1.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.80/1.47    inference(cnf_transformation,[],[f4])).
% 7.80/1.47  
% 7.80/1.47  fof(f5,axiom,(
% 7.80/1.47    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f24,plain,(
% 7.80/1.47    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.80/1.47    inference(cnf_transformation,[],[f5])).
% 7.80/1.47  
% 7.80/1.47  fof(f9,axiom,(
% 7.80/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f28,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.80/1.47    inference(cnf_transformation,[],[f9])).
% 7.80/1.47  
% 7.80/1.47  fof(f36,plain,(
% 7.80/1.47    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.80/1.47    inference(definition_unfolding,[],[f24,f28])).
% 7.80/1.47  
% 7.80/1.47  fof(f7,axiom,(
% 7.80/1.47    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f26,plain,(
% 7.80/1.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.80/1.47    inference(cnf_transformation,[],[f7])).
% 7.80/1.47  
% 7.80/1.47  fof(f2,axiom,(
% 7.80/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f21,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.80/1.47    inference(cnf_transformation,[],[f2])).
% 7.80/1.47  
% 7.80/1.47  fof(f35,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.80/1.47    inference(definition_unfolding,[],[f21,f28,f28])).
% 7.80/1.47  
% 7.80/1.47  fof(f13,axiom,(
% 7.80/1.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f32,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.80/1.47    inference(cnf_transformation,[],[f13])).
% 7.80/1.47  
% 7.80/1.47  fof(f39,plain,(
% 7.80/1.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.80/1.47    inference(definition_unfolding,[],[f32,f28])).
% 7.80/1.47  
% 7.80/1.47  fof(f12,axiom,(
% 7.80/1.47    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f31,plain,(
% 7.80/1.47    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.80/1.47    inference(cnf_transformation,[],[f12])).
% 7.80/1.47  
% 7.80/1.47  fof(f15,conjecture,(
% 7.80/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.80/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.47  
% 7.80/1.47  fof(f16,negated_conjecture,(
% 7.80/1.47    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.80/1.47    inference(negated_conjecture,[],[f15])).
% 7.80/1.47  
% 7.80/1.47  fof(f17,plain,(
% 7.80/1.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.80/1.47    inference(ennf_transformation,[],[f16])).
% 7.80/1.47  
% 7.80/1.47  fof(f18,plain,(
% 7.80/1.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.80/1.47    introduced(choice_axiom,[])).
% 7.80/1.47  
% 7.80/1.47  fof(f19,plain,(
% 7.80/1.47    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.80/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 7.80/1.47  
% 7.80/1.47  fof(f34,plain,(
% 7.80/1.47    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.80/1.47    inference(cnf_transformation,[],[f19])).
% 7.80/1.47  
% 7.80/1.47  fof(f41,plain,(
% 7.80/1.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 7.80/1.47    inference(definition_unfolding,[],[f34,f22,f22,f28])).
% 7.80/1.47  
% 7.80/1.47  cnf(c_4,plain,
% 7.80/1.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.80/1.47      inference(cnf_transformation,[],[f25]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_0,plain,
% 7.80/1.47      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.80/1.47      inference(cnf_transformation,[],[f20]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_11,plain,
% 7.80/1.47      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.80/1.47      inference(cnf_transformation,[],[f40]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_8,plain,
% 7.80/1.47      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.80/1.47      inference(cnf_transformation,[],[f30]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_38,plain,
% 7.80/1.47      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 7.80/1.47      inference(light_normalisation,[status(thm)],[c_11,c_8]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_2,plain,
% 7.80/1.47      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.80/1.47      inference(cnf_transformation,[],[f23]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_61,plain,
% 7.80/1.47      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_38,c_2]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_3,plain,
% 7.80/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.80/1.47      inference(cnf_transformation,[],[f36]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_63,plain,
% 7.80/1.47      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.80/1.47      inference(demodulation,[status(thm)],[c_61,c_3]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_5,plain,
% 7.80/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.80/1.47      inference(cnf_transformation,[],[f26]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_160,plain,
% 7.80/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_63,c_5]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_161,plain,
% 7.80/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.80/1.47      inference(demodulation,[status(thm)],[c_160,c_4]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_196,plain,
% 7.80/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_161,c_4]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_198,plain,
% 7.80/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.80/1.47      inference(demodulation,[status(thm)],[c_196,c_2]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_478,plain,
% 7.80/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_0,c_198]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_967,plain,
% 7.80/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_4,c_478]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_1016,plain,
% 7.80/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.80/1.47      inference(demodulation,[status(thm)],[c_967,c_478]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_156,plain,
% 7.80/1.47      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_63,c_5]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_163,plain,
% 7.80/1.47      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.80/1.47      inference(demodulation,[status(thm)],[c_156,c_8]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_982,plain,
% 7.80/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_478,c_163]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_113,plain,
% 7.80/1.47      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_7774,plain,
% 7.80/1.47      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_982,c_113]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_7961,plain,
% 7.80/1.47      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
% 7.80/1.47      inference(light_normalisation,[status(thm)],[c_7774,c_2]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_1,plain,
% 7.80/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.80/1.47      inference(cnf_transformation,[],[f35]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_10,plain,
% 7.80/1.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.80/1.47      inference(cnf_transformation,[],[f39]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_9,plain,
% 7.80/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.80/1.47      inference(cnf_transformation,[],[f31]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_30,plain,
% 7.80/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.80/1.47      inference(theory_normalisation,[status(thm)],[c_10,c_9,c_0]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_76,plain,
% 7.80/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.80/1.47      inference(superposition,[status(thm)],[c_4,c_30]) ).
% 7.80/1.47  
% 7.80/1.47  cnf(c_171,plain,
% 7.80/1.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_1,c_76]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_289,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_161,c_171]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_295,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_289,c_61]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_8064,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_7961,c_295]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_8115,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_8064,c_7961]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_101,plain,
% 7.80/1.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9096,plain,
% 7.80/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_8115,c_101]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9131,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_9096,c_61,c_161]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9205,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_1016,c_9131]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_186,plain,
% 7.80/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_4,c_161]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_433,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_186,c_171]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_454,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_433,c_5]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_455,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_454,c_2]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_3397,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_0,c_455]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9215,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_3397,c_9131]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9255,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_9131,c_1]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9285,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_9255,c_61,c_163]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9310,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_9215,c_9285]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9321,plain,
% 7.80/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_9205,c_9310]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9418,plain,
% 7.80/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_9321,c_5]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_7800,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_1016,c_113]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_7944,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_7800,c_113]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9432,plain,
% 7.80/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_9418,c_7944]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_288,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_163,c_171]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_296,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_288,c_61]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_12,negated_conjecture,
% 7.80/1.48      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 7.80/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_29,negated_conjecture,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.80/1.48      inference(theory_normalisation,[status(thm)],[c_12,c_9,c_0]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_40,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_29,c_5]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_792,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_296,c_40]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_29637,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_9432,c_792]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1482,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_1016,c_0]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_216,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_163,c_4]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_218,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_216,c_2]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_568,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_218,c_9]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9206,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_568,c_9131]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9319,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_9206,c_9131]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_178,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_76,c_0]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_41,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_856,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_178,c_41]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9212,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_856,c_9131]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_9320,plain,
% 7.80/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_9319,c_9212]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_209,plain,
% 7.80/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_76,c_163]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_256,plain,
% 7.80/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_209,c_5]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_267,plain,
% 7.80/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_256,c_5,c_8]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1462,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X2)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_267,c_1016]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1466,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_982,c_1016]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_548,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_0,c_218]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1106,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_548,c_218]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1141,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_1106,c_548]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1508,plain,
% 7.80/1.48      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_1466,c_1141]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1514,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_1462,c_1508]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_29428,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_9320,c_1514]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_193,plain,
% 7.80/1.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_161,c_5]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_199,plain,
% 7.80/1.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_193,c_8]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_8575,plain,
% 7.80/1.48      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_199,c_3397]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_764,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_9,c_295]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_782,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_295,c_9]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_790,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_764,c_782]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_8790,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_8575,c_790]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_887,plain,
% 7.80/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k1_xboole_0 ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_41,c_267]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_5207,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k2_xboole_0(X0,X3))) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_887,c_1016]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_391,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_76,c_9]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_43,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_2752,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_391,c_43]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_981,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_478,c_9]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_561,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_218,c_9]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_571,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_561,c_9]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1009,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_981,c_571]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_2778,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_2752,c_1009]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_5252,plain,
% 7.80/1.48      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_5207,c_2778]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_711,plain,
% 7.80/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_0,c_267]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1259,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_711,c_4]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1263,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_1259,c_2,c_1009]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_42,plain,
% 7.80/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_6494,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_1263,c_42]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_6524,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_6494,c_1009,c_1514]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_8791,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_8790,c_478,c_5252,c_6524]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_29606,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3) = k2_xboole_0(X0,k2_xboole_0(X3,k4_xboole_0(X1,X2))) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_29428,c_1514,c_8791]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_29638,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_29637,c_1482,c_29606]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1087,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_4,c_548]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_443,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_186,c_4]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_448,plain,
% 7.80/1.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_443,c_2]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1147,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.80/1.48      inference(light_normalisation,[status(thm)],[c_1087,c_448]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_1839,plain,
% 7.80/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k2_xboole_0(X2,X0) ),
% 7.80/1.48      inference(superposition,[status(thm)],[c_30,c_43]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_29639,plain,
% 7.80/1.48      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 7.80/1.48      inference(demodulation,[status(thm)],[c_29638,c_1147,c_1839]) ).
% 7.80/1.48  
% 7.80/1.48  cnf(c_29640,plain,
% 7.80/1.48      ( $false ),
% 7.80/1.48      inference(equality_resolution_simp,[status(thm)],[c_29639]) ).
% 7.80/1.48  
% 7.80/1.48  
% 7.80/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.48  
% 7.80/1.48  ------                               Statistics
% 7.80/1.48  
% 7.80/1.48  ------ General
% 7.80/1.48  
% 7.80/1.48  abstr_ref_over_cycles:                  0
% 7.80/1.48  abstr_ref_under_cycles:                 0
% 7.80/1.48  gc_basic_clause_elim:                   0
% 7.80/1.48  forced_gc_time:                         0
% 7.80/1.48  parsing_time:                           0.009
% 7.80/1.48  unif_index_cands_time:                  0.
% 7.80/1.48  unif_index_add_time:                    0.
% 7.80/1.48  orderings_time:                         0.
% 7.80/1.48  out_proof_time:                         0.008
% 7.80/1.48  total_time:                             0.819
% 7.80/1.48  num_of_symbols:                         38
% 7.80/1.48  num_of_terms:                           51560
% 7.80/1.48  
% 7.80/1.48  ------ Preprocessing
% 7.80/1.48  
% 7.80/1.48  num_of_splits:                          0
% 7.80/1.48  num_of_split_atoms:                     2
% 7.80/1.48  num_of_reused_defs:                     0
% 7.80/1.48  num_eq_ax_congr_red:                    0
% 7.80/1.48  num_of_sem_filtered_clauses:            0
% 7.80/1.48  num_of_subtypes:                        0
% 7.80/1.48  monotx_restored_types:                  0
% 7.80/1.48  sat_num_of_epr_types:                   0
% 7.80/1.48  sat_num_of_non_cyclic_types:            0
% 7.80/1.48  sat_guarded_non_collapsed_types:        0
% 7.80/1.48  num_pure_diseq_elim:                    0
% 7.80/1.48  simp_replaced_by:                       0
% 7.80/1.48  res_preprocessed:                       30
% 7.80/1.48  prep_upred:                             0
% 7.80/1.48  prep_unflattend:                        0
% 7.80/1.48  smt_new_axioms:                         0
% 7.80/1.48  pred_elim_cands:                        0
% 7.80/1.48  pred_elim:                              0
% 7.80/1.48  pred_elim_cl:                           0
% 7.80/1.48  pred_elim_cycles:                       0
% 7.80/1.48  merged_defs:                            0
% 7.80/1.48  merged_defs_ncl:                        0
% 7.80/1.48  bin_hyper_res:                          0
% 7.80/1.48  prep_cycles:                            2
% 7.80/1.48  pred_elim_time:                         0.
% 7.80/1.48  splitting_time:                         0.
% 7.80/1.48  sem_filter_time:                        0.
% 7.80/1.48  monotx_time:                            0.
% 7.80/1.48  subtype_inf_time:                       0.
% 7.80/1.48  
% 7.80/1.48  ------ Problem properties
% 7.80/1.48  
% 7.80/1.48  clauses:                                13
% 7.80/1.48  conjectures:                            1
% 7.80/1.48  epr:                                    0
% 7.80/1.48  horn:                                   13
% 7.80/1.48  ground:                                 1
% 7.80/1.48  unary:                                  13
% 7.80/1.48  binary:                                 0
% 7.80/1.48  lits:                                   13
% 7.80/1.48  lits_eq:                                13
% 7.80/1.48  fd_pure:                                0
% 7.80/1.48  fd_pseudo:                              0
% 7.80/1.48  fd_cond:                                0
% 7.80/1.48  fd_pseudo_cond:                         0
% 7.80/1.48  ac_symbols:                             1
% 7.80/1.48  
% 7.80/1.48  ------ Propositional Solver
% 7.80/1.48  
% 7.80/1.48  prop_solver_calls:                      13
% 7.80/1.48  prop_fast_solver_calls:                 72
% 7.80/1.48  smt_solver_calls:                       0
% 7.80/1.48  smt_fast_solver_calls:                  0
% 7.80/1.48  prop_num_of_clauses:                    254
% 7.80/1.48  prop_preprocess_simplified:             469
% 7.80/1.48  prop_fo_subsumed:                       0
% 7.80/1.48  prop_solver_time:                       0.
% 7.80/1.48  smt_solver_time:                        0.
% 7.80/1.48  smt_fast_solver_time:                   0.
% 7.80/1.48  prop_fast_solver_time:                  0.
% 7.80/1.48  prop_unsat_core_time:                   0.
% 7.80/1.48  
% 7.80/1.48  ------ QBF
% 7.80/1.48  
% 7.80/1.48  qbf_q_res:                              0
% 7.80/1.48  qbf_num_tautologies:                    0
% 7.80/1.48  qbf_prep_cycles:                        0
% 7.80/1.48  
% 7.80/1.48  ------ BMC1
% 7.80/1.48  
% 7.80/1.48  bmc1_current_bound:                     -1
% 7.80/1.48  bmc1_last_solved_bound:                 -1
% 7.80/1.48  bmc1_unsat_core_size:                   -1
% 7.80/1.48  bmc1_unsat_core_parents_size:           -1
% 7.80/1.48  bmc1_merge_next_fun:                    0
% 7.80/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.80/1.48  
% 7.80/1.48  ------ Instantiation
% 7.80/1.48  
% 7.80/1.48  inst_num_of_clauses:                    0
% 7.80/1.48  inst_num_in_passive:                    0
% 7.80/1.48  inst_num_in_active:                     0
% 7.80/1.48  inst_num_in_unprocessed:                0
% 7.80/1.48  inst_num_of_loops:                      0
% 7.80/1.48  inst_num_of_learning_restarts:          0
% 7.80/1.48  inst_num_moves_active_passive:          0
% 7.80/1.48  inst_lit_activity:                      0
% 7.80/1.48  inst_lit_activity_moves:                0
% 7.80/1.48  inst_num_tautologies:                   0
% 7.80/1.48  inst_num_prop_implied:                  0
% 7.80/1.48  inst_num_existing_simplified:           0
% 7.80/1.48  inst_num_eq_res_simplified:             0
% 7.80/1.48  inst_num_child_elim:                    0
% 7.80/1.48  inst_num_of_dismatching_blockings:      0
% 7.80/1.48  inst_num_of_non_proper_insts:           0
% 7.80/1.48  inst_num_of_duplicates:                 0
% 7.80/1.48  inst_inst_num_from_inst_to_res:         0
% 7.80/1.48  inst_dismatching_checking_time:         0.
% 7.80/1.48  
% 7.80/1.48  ------ Resolution
% 7.80/1.48  
% 7.80/1.48  res_num_of_clauses:                     0
% 7.80/1.48  res_num_in_passive:                     0
% 7.80/1.48  res_num_in_active:                      0
% 7.80/1.48  res_num_of_loops:                       32
% 7.80/1.48  res_forward_subset_subsumed:            0
% 7.80/1.48  res_backward_subset_subsumed:           0
% 7.80/1.48  res_forward_subsumed:                   0
% 7.80/1.48  res_backward_subsumed:                  0
% 7.80/1.48  res_forward_subsumption_resolution:     0
% 7.80/1.48  res_backward_subsumption_resolution:    0
% 7.80/1.48  res_clause_to_clause_subsumption:       75223
% 7.80/1.48  res_orphan_elimination:                 0
% 7.80/1.48  res_tautology_del:                      0
% 7.80/1.48  res_num_eq_res_simplified:              0
% 7.80/1.48  res_num_sel_changes:                    0
% 7.80/1.48  res_moves_from_active_to_pass:          0
% 7.80/1.48  
% 7.80/1.48  ------ Superposition
% 7.80/1.48  
% 7.80/1.48  sup_time_total:                         0.
% 7.80/1.48  sup_time_generating:                    0.
% 7.80/1.48  sup_time_sim_full:                      0.
% 7.80/1.48  sup_time_sim_immed:                     0.
% 7.80/1.48  
% 7.80/1.48  sup_num_of_clauses:                     2860
% 7.80/1.48  sup_num_in_active:                      131
% 7.80/1.48  sup_num_in_passive:                     2729
% 7.80/1.48  sup_num_of_loops:                       147
% 7.80/1.48  sup_fw_superposition:                   10664
% 7.80/1.48  sup_bw_superposition:                   7865
% 7.80/1.48  sup_immediate_simplified:               9697
% 7.80/1.48  sup_given_eliminated:                   3
% 7.80/1.48  comparisons_done:                       0
% 7.80/1.48  comparisons_avoided:                    0
% 7.80/1.48  
% 7.80/1.48  ------ Simplifications
% 7.80/1.48  
% 7.80/1.48  
% 7.80/1.48  sim_fw_subset_subsumed:                 0
% 7.80/1.48  sim_bw_subset_subsumed:                 0
% 7.80/1.48  sim_fw_subsumed:                        1295
% 7.80/1.48  sim_bw_subsumed:                        18
% 7.80/1.48  sim_fw_subsumption_res:                 0
% 7.80/1.48  sim_bw_subsumption_res:                 0
% 7.80/1.48  sim_tautology_del:                      0
% 7.80/1.48  sim_eq_tautology_del:                   2708
% 7.80/1.48  sim_eq_res_simp:                        0
% 7.80/1.48  sim_fw_demodulated:                     7006
% 7.80/1.48  sim_bw_demodulated:                     55
% 7.80/1.48  sim_light_normalised:                   3705
% 7.80/1.48  sim_joinable_taut:                      162
% 7.80/1.48  sim_joinable_simp:                      0
% 7.80/1.48  sim_ac_normalised:                      0
% 7.80/1.48  sim_smt_subsumption:                    0
% 7.80/1.48  
%------------------------------------------------------------------------------
