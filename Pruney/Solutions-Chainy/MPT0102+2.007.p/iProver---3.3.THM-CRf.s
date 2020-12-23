%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:03 EST 2020

% Result     : Theorem 12.04s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :  155 (43027 expanded)
%              Number of clauses        :  123 (17229 expanded)
%              Number of leaves         :   13 (11779 expanded)
%              Depth                    :   34
%              Number of atoms          :  156 (43028 expanded)
%              Number of equality atoms :  155 (43027 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f28,f28])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f16,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f29,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f29,f28,f20,f20])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_45,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_110,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_45,c_1])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_29,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_5])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_62,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_29,c_7])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_32,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_47,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_32,c_6])).

cnf(c_52,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_47,c_29])).

cnf(c_73,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_62,c_52])).

cnf(c_116,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_110,c_5,c_73])).

cnf(c_194,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_116])).

cnf(c_291,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_194,c_7])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_31,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_9])).

cnf(c_52186,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_291,c_31])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_71,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_67,c_7])).

cnf(c_3474,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2,c_71])).

cnf(c_69,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_29])).

cnf(c_3730,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3474,c_69])).

cnf(c_4539,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3730,c_116])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_142,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_73])).

cnf(c_369,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_116,c_142])).

cnf(c_511,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_369,c_194])).

cnf(c_4551,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4539,c_511])).

cnf(c_4674,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4551,c_194])).

cnf(c_366,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_194,c_142])).

cnf(c_426,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_366])).

cnf(c_546,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_426])).

cnf(c_3774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_546])).

cnf(c_557,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_116,c_426])).

cnf(c_594,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_557,c_45])).

cnf(c_66,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_2139,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_594,c_66])).

cnf(c_2330,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_2139,c_3,c_7])).

cnf(c_2331,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2330,c_2])).

cnf(c_3957,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3774,c_2331])).

cnf(c_4410,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_3957,c_194])).

cnf(c_4789,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_4410,c_5])).

cnf(c_4812,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_45,c_4789])).

cnf(c_16054,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4674,c_4812])).

cnf(c_209,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_73,c_116])).

cnf(c_1837,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_209,c_5])).

cnf(c_1849,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1837])).

cnf(c_1969,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1849,c_116])).

cnf(c_138,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_73])).

cnf(c_1995,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1969,c_138])).

cnf(c_2963,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1837,c_1995])).

cnf(c_3026,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2963,c_1995])).

cnf(c_159,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_138,c_7])).

cnf(c_63,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_72,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_63,c_7])).

cnf(c_163,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_159,c_52,c_72])).

cnf(c_246,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_163])).

cnf(c_4804,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_4789])).

cnf(c_5507,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_246,c_4804])).

cnf(c_5577,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5507,c_5])).

cnf(c_212,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_116,c_69])).

cnf(c_85,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_10185,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
    inference(superposition,[status(thm)],[c_212,c_85])).

cnf(c_10528,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
    inference(light_normalisation,[status(thm)],[c_10185,c_5])).

cnf(c_4618,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_4551])).

cnf(c_5414,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_1849,c_4618])).

cnf(c_83,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_8432,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k2_xboole_0(X2,X4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))),X2) ),
    inference(superposition,[status(thm)],[c_5414,c_83])).

cnf(c_10529,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))),X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_10528,c_212,c_1995,c_8432])).

cnf(c_700,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_594,c_8])).

cnf(c_711,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_700,c_32])).

cnf(c_4870,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_4789,c_0])).

cnf(c_10530,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_10529,c_711,c_4870])).

cnf(c_16261,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(demodulation,[status(thm)],[c_16054,c_3026,c_5577,c_10530])).

cnf(c_4807,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_4789])).

cnf(c_2993,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1995,c_8])).

cnf(c_2998,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_2993,c_1995])).

cnf(c_2999,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2998,c_5])).

cnf(c_14320,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4807,c_2999])).

cnf(c_16262,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_16261,c_14320])).

cnf(c_16441,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_16262,c_0])).

cnf(c_4984,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_45,c_4870])).

cnf(c_18922,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_16441,c_4984])).

cnf(c_4681,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4551,c_4551])).

cnf(c_16177,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4812,c_2999])).

cnf(c_19198,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_18922,c_4681,c_16177])).

cnf(c_89,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_19350,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_19198,c_89])).

cnf(c_91,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_96,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_91,c_7])).

cnf(c_20502,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_96,c_19198])).

cnf(c_92,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_20717,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_20502,c_92])).

cnf(c_20742,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X2)),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_20717,c_19350])).

cnf(c_20724,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_20502,c_85])).

cnf(c_16701,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),X3),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_16441,c_83])).

cnf(c_20731,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_20724,c_16701])).

cnf(c_20743,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_20742,c_20731])).

cnf(c_4425,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3957,c_8])).

cnf(c_4433,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4425,c_3])).

cnf(c_16058,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4812])).

cnf(c_31416,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_4433,c_16058])).

cnf(c_14203,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_4433,c_4807])).

cnf(c_14225,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1837,c_4807])).

cnf(c_1871,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1837,c_0])).

cnf(c_2962,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1871,c_1995])).

cnf(c_3027,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2962,c_1995])).

cnf(c_14376,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_14225,c_45,c_3027])).

cnf(c_30083,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X0) ),
    inference(superposition,[status(thm)],[c_4433,c_14320])).

cnf(c_19005,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_4433,c_4984])).

cnf(c_19267,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4433,c_19198])).

cnf(c_19408,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_19267,c_19198])).

cnf(c_30239,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_30083,c_19005,c_19408])).

cnf(c_31681,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_31416,c_14203,c_14376,c_30239])).

cnf(c_49433,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
    inference(superposition,[status(thm)],[c_89,c_31681])).

cnf(c_52187,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_52186,c_19350,c_20743,c_49433])).

cnf(c_52188,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_52187,c_4433])).

cnf(c_52189,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_52188])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 15:18:15 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 12.04/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/1.99  
% 12.04/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.04/1.99  
% 12.04/1.99  ------  iProver source info
% 12.04/1.99  
% 12.04/1.99  git: date: 2020-06-30 10:37:57 +0100
% 12.04/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.04/1.99  git: non_committed_changes: false
% 12.04/1.99  git: last_make_outside_of_git: false
% 12.04/1.99  
% 12.04/1.99  ------ 
% 12.04/1.99  
% 12.04/1.99  ------ Input Options
% 12.04/1.99  
% 12.04/1.99  --out_options                           all
% 12.04/1.99  --tptp_safe_out                         true
% 12.04/1.99  --problem_path                          ""
% 12.04/1.99  --include_path                          ""
% 12.04/1.99  --clausifier                            res/vclausify_rel
% 12.04/1.99  --clausifier_options                    --mode clausify
% 12.04/1.99  --stdin                                 false
% 12.04/1.99  --stats_out                             all
% 12.04/1.99  
% 12.04/1.99  ------ General Options
% 12.04/1.99  
% 12.04/1.99  --fof                                   false
% 12.04/1.99  --time_out_real                         305.
% 12.04/1.99  --time_out_virtual                      -1.
% 12.04/1.99  --symbol_type_check                     false
% 12.04/1.99  --clausify_out                          false
% 12.04/1.99  --sig_cnt_out                           false
% 12.04/1.99  --trig_cnt_out                          false
% 12.04/1.99  --trig_cnt_out_tolerance                1.
% 12.04/1.99  --trig_cnt_out_sk_spl                   false
% 12.04/1.99  --abstr_cl_out                          false
% 12.04/1.99  
% 12.04/1.99  ------ Global Options
% 12.04/1.99  
% 12.04/1.99  --schedule                              default
% 12.04/1.99  --add_important_lit                     false
% 12.04/1.99  --prop_solver_per_cl                    1000
% 12.04/1.99  --min_unsat_core                        false
% 12.04/1.99  --soft_assumptions                      false
% 12.04/1.99  --soft_lemma_size                       3
% 12.04/1.99  --prop_impl_unit_size                   0
% 12.04/1.99  --prop_impl_unit                        []
% 12.04/1.99  --share_sel_clauses                     true
% 12.04/1.99  --reset_solvers                         false
% 12.04/1.99  --bc_imp_inh                            [conj_cone]
% 12.04/1.99  --conj_cone_tolerance                   3.
% 12.04/1.99  --extra_neg_conj                        none
% 12.04/1.99  --large_theory_mode                     true
% 12.04/1.99  --prolific_symb_bound                   200
% 12.04/1.99  --lt_threshold                          2000
% 12.04/1.99  --clause_weak_htbl                      true
% 12.04/1.99  --gc_record_bc_elim                     false
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing Options
% 12.04/1.99  
% 12.04/1.99  --preprocessing_flag                    true
% 12.04/1.99  --time_out_prep_mult                    0.1
% 12.04/1.99  --splitting_mode                        input
% 12.04/1.99  --splitting_grd                         true
% 12.04/1.99  --splitting_cvd                         false
% 12.04/1.99  --splitting_cvd_svl                     false
% 12.04/1.99  --splitting_nvd                         32
% 12.04/1.99  --sub_typing                            true
% 12.04/1.99  --prep_gs_sim                           true
% 12.04/1.99  --prep_unflatten                        true
% 12.04/1.99  --prep_res_sim                          true
% 12.04/1.99  --prep_upred                            true
% 12.04/1.99  --prep_sem_filter                       exhaustive
% 12.04/1.99  --prep_sem_filter_out                   false
% 12.04/1.99  --pred_elim                             true
% 12.04/1.99  --res_sim_input                         true
% 12.04/1.99  --eq_ax_congr_red                       true
% 12.04/1.99  --pure_diseq_elim                       true
% 12.04/1.99  --brand_transform                       false
% 12.04/1.99  --non_eq_to_eq                          false
% 12.04/1.99  --prep_def_merge                        true
% 12.04/1.99  --prep_def_merge_prop_impl              false
% 12.04/1.99  --prep_def_merge_mbd                    true
% 12.04/1.99  --prep_def_merge_tr_red                 false
% 12.04/1.99  --prep_def_merge_tr_cl                  false
% 12.04/1.99  --smt_preprocessing                     true
% 12.04/1.99  --smt_ac_axioms                         fast
% 12.04/1.99  --preprocessed_out                      false
% 12.04/1.99  --preprocessed_stats                    false
% 12.04/1.99  
% 12.04/1.99  ------ Abstraction refinement Options
% 12.04/1.99  
% 12.04/1.99  --abstr_ref                             []
% 12.04/1.99  --abstr_ref_prep                        false
% 12.04/1.99  --abstr_ref_until_sat                   false
% 12.04/1.99  --abstr_ref_sig_restrict                funpre
% 12.04/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.04/1.99  --abstr_ref_under                       []
% 12.04/1.99  
% 12.04/1.99  ------ SAT Options
% 12.04/1.99  
% 12.04/1.99  --sat_mode                              false
% 12.04/1.99  --sat_fm_restart_options                ""
% 12.04/1.99  --sat_gr_def                            false
% 12.04/1.99  --sat_epr_types                         true
% 12.04/1.99  --sat_non_cyclic_types                  false
% 12.04/1.99  --sat_finite_models                     false
% 12.04/1.99  --sat_fm_lemmas                         false
% 12.04/1.99  --sat_fm_prep                           false
% 12.04/1.99  --sat_fm_uc_incr                        true
% 12.04/1.99  --sat_out_model                         small
% 12.04/1.99  --sat_out_clauses                       false
% 12.04/1.99  
% 12.04/1.99  ------ QBF Options
% 12.04/1.99  
% 12.04/1.99  --qbf_mode                              false
% 12.04/1.99  --qbf_elim_univ                         false
% 12.04/1.99  --qbf_dom_inst                          none
% 12.04/1.99  --qbf_dom_pre_inst                      false
% 12.04/1.99  --qbf_sk_in                             false
% 12.04/1.99  --qbf_pred_elim                         true
% 12.04/1.99  --qbf_split                             512
% 12.04/1.99  
% 12.04/1.99  ------ BMC1 Options
% 12.04/1.99  
% 12.04/1.99  --bmc1_incremental                      false
% 12.04/1.99  --bmc1_axioms                           reachable_all
% 12.04/1.99  --bmc1_min_bound                        0
% 12.04/1.99  --bmc1_max_bound                        -1
% 12.04/1.99  --bmc1_max_bound_default                -1
% 12.04/1.99  --bmc1_symbol_reachability              true
% 12.04/1.99  --bmc1_property_lemmas                  false
% 12.04/1.99  --bmc1_k_induction                      false
% 12.04/1.99  --bmc1_non_equiv_states                 false
% 12.04/1.99  --bmc1_deadlock                         false
% 12.04/1.99  --bmc1_ucm                              false
% 12.04/1.99  --bmc1_add_unsat_core                   none
% 12.04/1.99  --bmc1_unsat_core_children              false
% 12.04/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.04/1.99  --bmc1_out_stat                         full
% 12.04/1.99  --bmc1_ground_init                      false
% 12.04/1.99  --bmc1_pre_inst_next_state              false
% 12.04/1.99  --bmc1_pre_inst_state                   false
% 12.04/1.99  --bmc1_pre_inst_reach_state             false
% 12.04/1.99  --bmc1_out_unsat_core                   false
% 12.04/1.99  --bmc1_aig_witness_out                  false
% 12.04/1.99  --bmc1_verbose                          false
% 12.04/1.99  --bmc1_dump_clauses_tptp                false
% 12.04/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.04/1.99  --bmc1_dump_file                        -
% 12.04/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.04/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.04/1.99  --bmc1_ucm_extend_mode                  1
% 12.04/1.99  --bmc1_ucm_init_mode                    2
% 12.04/1.99  --bmc1_ucm_cone_mode                    none
% 12.04/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.04/1.99  --bmc1_ucm_relax_model                  4
% 12.04/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.04/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.04/1.99  --bmc1_ucm_layered_model                none
% 12.04/1.99  --bmc1_ucm_max_lemma_size               10
% 12.04/1.99  
% 12.04/1.99  ------ AIG Options
% 12.04/1.99  
% 12.04/1.99  --aig_mode                              false
% 12.04/1.99  
% 12.04/1.99  ------ Instantiation Options
% 12.04/1.99  
% 12.04/1.99  --instantiation_flag                    true
% 12.04/1.99  --inst_sos_flag                         false
% 12.04/1.99  --inst_sos_phase                        true
% 12.04/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel_side                     num_symb
% 12.04/1.99  --inst_solver_per_active                1400
% 12.04/1.99  --inst_solver_calls_frac                1.
% 12.04/1.99  --inst_passive_queue_type               priority_queues
% 12.04/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.04/1.99  --inst_passive_queues_freq              [25;2]
% 12.04/1.99  --inst_dismatching                      true
% 12.04/1.99  --inst_eager_unprocessed_to_passive     true
% 12.04/1.99  --inst_prop_sim_given                   true
% 12.04/1.99  --inst_prop_sim_new                     false
% 12.04/1.99  --inst_subs_new                         false
% 12.04/1.99  --inst_eq_res_simp                      false
% 12.04/1.99  --inst_subs_given                       false
% 12.04/1.99  --inst_orphan_elimination               true
% 12.04/1.99  --inst_learning_loop_flag               true
% 12.04/1.99  --inst_learning_start                   3000
% 12.04/1.99  --inst_learning_factor                  2
% 12.04/1.99  --inst_start_prop_sim_after_learn       3
% 12.04/1.99  --inst_sel_renew                        solver
% 12.04/1.99  --inst_lit_activity_flag                true
% 12.04/1.99  --inst_restr_to_given                   false
% 12.04/1.99  --inst_activity_threshold               500
% 12.04/1.99  --inst_out_proof                        true
% 12.04/1.99  
% 12.04/1.99  ------ Resolution Options
% 12.04/1.99  
% 12.04/1.99  --resolution_flag                       true
% 12.04/1.99  --res_lit_sel                           adaptive
% 12.04/1.99  --res_lit_sel_side                      none
% 12.04/1.99  --res_ordering                          kbo
% 12.04/1.99  --res_to_prop_solver                    active
% 12.04/1.99  --res_prop_simpl_new                    false
% 12.04/1.99  --res_prop_simpl_given                  true
% 12.04/1.99  --res_passive_queue_type                priority_queues
% 12.04/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.04/1.99  --res_passive_queues_freq               [15;5]
% 12.04/1.99  --res_forward_subs                      full
% 12.04/1.99  --res_backward_subs                     full
% 12.04/1.99  --res_forward_subs_resolution           true
% 12.04/1.99  --res_backward_subs_resolution          true
% 12.04/1.99  --res_orphan_elimination                true
% 12.04/1.99  --res_time_limit                        2.
% 12.04/1.99  --res_out_proof                         true
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Options
% 12.04/1.99  
% 12.04/1.99  --superposition_flag                    true
% 12.04/1.99  --sup_passive_queue_type                priority_queues
% 12.04/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.04/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.04/1.99  --demod_completeness_check              fast
% 12.04/1.99  --demod_use_ground                      true
% 12.04/1.99  --sup_to_prop_solver                    passive
% 12.04/1.99  --sup_prop_simpl_new                    true
% 12.04/1.99  --sup_prop_simpl_given                  true
% 12.04/1.99  --sup_fun_splitting                     false
% 12.04/1.99  --sup_smt_interval                      50000
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Simplification Setup
% 12.04/1.99  
% 12.04/1.99  --sup_indices_passive                   []
% 12.04/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.04/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.04/1.99  --sup_full_bw                           [BwDemod]
% 12.04/1.99  --sup_immed_triv                        [TrivRules]
% 12.04/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.04/1.99  --sup_immed_bw_main                     []
% 12.04/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.04/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.04/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.04/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.04/1.99  
% 12.04/1.99  ------ Combination Options
% 12.04/1.99  
% 12.04/1.99  --comb_res_mult                         3
% 12.04/1.99  --comb_sup_mult                         2
% 12.04/1.99  --comb_inst_mult                        10
% 12.04/1.99  
% 12.04/1.99  ------ Debug Options
% 12.04/1.99  
% 12.04/1.99  --dbg_backtrace                         false
% 12.04/1.99  --dbg_dump_prop_clauses                 false
% 12.04/1.99  --dbg_dump_prop_clauses_file            -
% 12.04/1.99  --dbg_out_stat                          false
% 12.04/1.99  ------ Parsing...
% 12.04/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.04/1.99  ------ Proving...
% 12.04/1.99  ------ Problem Properties 
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  clauses                                 10
% 12.04/1.99  conjectures                             1
% 12.04/1.99  EPR                                     0
% 12.04/1.99  Horn                                    10
% 12.04/1.99  unary                                   10
% 12.04/1.99  binary                                  0
% 12.04/1.99  lits                                    10
% 12.04/1.99  lits eq                                 10
% 12.04/1.99  fd_pure                                 0
% 12.04/1.99  fd_pseudo                               0
% 12.04/1.99  fd_cond                                 0
% 12.04/1.99  fd_pseudo_cond                          0
% 12.04/1.99  AC symbols                              0
% 12.04/1.99  
% 12.04/1.99  ------ Schedule UEQ
% 12.04/1.99  
% 12.04/1.99  ------ pure equality problem: resolution off 
% 12.04/1.99  
% 12.04/1.99  ------ Option_UEQ Time Limit: Unbounded
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  ------ 
% 12.04/1.99  Current options:
% 12.04/1.99  ------ 
% 12.04/1.99  
% 12.04/1.99  ------ Input Options
% 12.04/1.99  
% 12.04/1.99  --out_options                           all
% 12.04/1.99  --tptp_safe_out                         true
% 12.04/1.99  --problem_path                          ""
% 12.04/1.99  --include_path                          ""
% 12.04/1.99  --clausifier                            res/vclausify_rel
% 12.04/1.99  --clausifier_options                    --mode clausify
% 12.04/1.99  --stdin                                 false
% 12.04/1.99  --stats_out                             all
% 12.04/1.99  
% 12.04/1.99  ------ General Options
% 12.04/1.99  
% 12.04/1.99  --fof                                   false
% 12.04/1.99  --time_out_real                         305.
% 12.04/1.99  --time_out_virtual                      -1.
% 12.04/1.99  --symbol_type_check                     false
% 12.04/1.99  --clausify_out                          false
% 12.04/1.99  --sig_cnt_out                           false
% 12.04/1.99  --trig_cnt_out                          false
% 12.04/1.99  --trig_cnt_out_tolerance                1.
% 12.04/1.99  --trig_cnt_out_sk_spl                   false
% 12.04/1.99  --abstr_cl_out                          false
% 12.04/1.99  
% 12.04/1.99  ------ Global Options
% 12.04/1.99  
% 12.04/1.99  --schedule                              default
% 12.04/1.99  --add_important_lit                     false
% 12.04/1.99  --prop_solver_per_cl                    1000
% 12.04/1.99  --min_unsat_core                        false
% 12.04/1.99  --soft_assumptions                      false
% 12.04/1.99  --soft_lemma_size                       3
% 12.04/1.99  --prop_impl_unit_size                   0
% 12.04/1.99  --prop_impl_unit                        []
% 12.04/1.99  --share_sel_clauses                     true
% 12.04/1.99  --reset_solvers                         false
% 12.04/1.99  --bc_imp_inh                            [conj_cone]
% 12.04/1.99  --conj_cone_tolerance                   3.
% 12.04/1.99  --extra_neg_conj                        none
% 12.04/1.99  --large_theory_mode                     true
% 12.04/1.99  --prolific_symb_bound                   200
% 12.04/1.99  --lt_threshold                          2000
% 12.04/1.99  --clause_weak_htbl                      true
% 12.04/1.99  --gc_record_bc_elim                     false
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing Options
% 12.04/1.99  
% 12.04/1.99  --preprocessing_flag                    true
% 12.04/1.99  --time_out_prep_mult                    0.1
% 12.04/1.99  --splitting_mode                        input
% 12.04/1.99  --splitting_grd                         true
% 12.04/1.99  --splitting_cvd                         false
% 12.04/1.99  --splitting_cvd_svl                     false
% 12.04/1.99  --splitting_nvd                         32
% 12.04/1.99  --sub_typing                            true
% 12.04/1.99  --prep_gs_sim                           true
% 12.04/1.99  --prep_unflatten                        true
% 12.04/1.99  --prep_res_sim                          true
% 12.04/1.99  --prep_upred                            true
% 12.04/1.99  --prep_sem_filter                       exhaustive
% 12.04/1.99  --prep_sem_filter_out                   false
% 12.04/1.99  --pred_elim                             true
% 12.04/1.99  --res_sim_input                         true
% 12.04/1.99  --eq_ax_congr_red                       true
% 12.04/1.99  --pure_diseq_elim                       true
% 12.04/1.99  --brand_transform                       false
% 12.04/1.99  --non_eq_to_eq                          false
% 12.04/1.99  --prep_def_merge                        true
% 12.04/1.99  --prep_def_merge_prop_impl              false
% 12.04/1.99  --prep_def_merge_mbd                    true
% 12.04/1.99  --prep_def_merge_tr_red                 false
% 12.04/1.99  --prep_def_merge_tr_cl                  false
% 12.04/1.99  --smt_preprocessing                     true
% 12.04/1.99  --smt_ac_axioms                         fast
% 12.04/1.99  --preprocessed_out                      false
% 12.04/1.99  --preprocessed_stats                    false
% 12.04/1.99  
% 12.04/1.99  ------ Abstraction refinement Options
% 12.04/1.99  
% 12.04/1.99  --abstr_ref                             []
% 12.04/1.99  --abstr_ref_prep                        false
% 12.04/1.99  --abstr_ref_until_sat                   false
% 12.04/1.99  --abstr_ref_sig_restrict                funpre
% 12.04/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.04/1.99  --abstr_ref_under                       []
% 12.04/1.99  
% 12.04/1.99  ------ SAT Options
% 12.04/1.99  
% 12.04/1.99  --sat_mode                              false
% 12.04/1.99  --sat_fm_restart_options                ""
% 12.04/1.99  --sat_gr_def                            false
% 12.04/1.99  --sat_epr_types                         true
% 12.04/1.99  --sat_non_cyclic_types                  false
% 12.04/1.99  --sat_finite_models                     false
% 12.04/1.99  --sat_fm_lemmas                         false
% 12.04/1.99  --sat_fm_prep                           false
% 12.04/1.99  --sat_fm_uc_incr                        true
% 12.04/1.99  --sat_out_model                         small
% 12.04/1.99  --sat_out_clauses                       false
% 12.04/1.99  
% 12.04/1.99  ------ QBF Options
% 12.04/1.99  
% 12.04/1.99  --qbf_mode                              false
% 12.04/1.99  --qbf_elim_univ                         false
% 12.04/1.99  --qbf_dom_inst                          none
% 12.04/1.99  --qbf_dom_pre_inst                      false
% 12.04/1.99  --qbf_sk_in                             false
% 12.04/1.99  --qbf_pred_elim                         true
% 12.04/1.99  --qbf_split                             512
% 12.04/1.99  
% 12.04/1.99  ------ BMC1 Options
% 12.04/1.99  
% 12.04/1.99  --bmc1_incremental                      false
% 12.04/1.99  --bmc1_axioms                           reachable_all
% 12.04/1.99  --bmc1_min_bound                        0
% 12.04/1.99  --bmc1_max_bound                        -1
% 12.04/1.99  --bmc1_max_bound_default                -1
% 12.04/1.99  --bmc1_symbol_reachability              true
% 12.04/1.99  --bmc1_property_lemmas                  false
% 12.04/1.99  --bmc1_k_induction                      false
% 12.04/1.99  --bmc1_non_equiv_states                 false
% 12.04/1.99  --bmc1_deadlock                         false
% 12.04/1.99  --bmc1_ucm                              false
% 12.04/1.99  --bmc1_add_unsat_core                   none
% 12.04/1.99  --bmc1_unsat_core_children              false
% 12.04/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.04/1.99  --bmc1_out_stat                         full
% 12.04/1.99  --bmc1_ground_init                      false
% 12.04/1.99  --bmc1_pre_inst_next_state              false
% 12.04/1.99  --bmc1_pre_inst_state                   false
% 12.04/1.99  --bmc1_pre_inst_reach_state             false
% 12.04/1.99  --bmc1_out_unsat_core                   false
% 12.04/1.99  --bmc1_aig_witness_out                  false
% 12.04/1.99  --bmc1_verbose                          false
% 12.04/1.99  --bmc1_dump_clauses_tptp                false
% 12.04/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.04/1.99  --bmc1_dump_file                        -
% 12.04/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.04/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.04/1.99  --bmc1_ucm_extend_mode                  1
% 12.04/1.99  --bmc1_ucm_init_mode                    2
% 12.04/1.99  --bmc1_ucm_cone_mode                    none
% 12.04/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.04/1.99  --bmc1_ucm_relax_model                  4
% 12.04/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.04/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.04/1.99  --bmc1_ucm_layered_model                none
% 12.04/1.99  --bmc1_ucm_max_lemma_size               10
% 12.04/1.99  
% 12.04/1.99  ------ AIG Options
% 12.04/1.99  
% 12.04/1.99  --aig_mode                              false
% 12.04/1.99  
% 12.04/1.99  ------ Instantiation Options
% 12.04/1.99  
% 12.04/1.99  --instantiation_flag                    false
% 12.04/1.99  --inst_sos_flag                         false
% 12.04/1.99  --inst_sos_phase                        true
% 12.04/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel_side                     num_symb
% 12.04/1.99  --inst_solver_per_active                1400
% 12.04/1.99  --inst_solver_calls_frac                1.
% 12.04/1.99  --inst_passive_queue_type               priority_queues
% 12.04/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.04/1.99  --inst_passive_queues_freq              [25;2]
% 12.04/1.99  --inst_dismatching                      true
% 12.04/1.99  --inst_eager_unprocessed_to_passive     true
% 12.04/1.99  --inst_prop_sim_given                   true
% 12.04/1.99  --inst_prop_sim_new                     false
% 12.04/1.99  --inst_subs_new                         false
% 12.04/1.99  --inst_eq_res_simp                      false
% 12.04/1.99  --inst_subs_given                       false
% 12.04/1.99  --inst_orphan_elimination               true
% 12.04/1.99  --inst_learning_loop_flag               true
% 12.04/1.99  --inst_learning_start                   3000
% 12.04/1.99  --inst_learning_factor                  2
% 12.04/1.99  --inst_start_prop_sim_after_learn       3
% 12.04/1.99  --inst_sel_renew                        solver
% 12.04/1.99  --inst_lit_activity_flag                true
% 12.04/1.99  --inst_restr_to_given                   false
% 12.04/1.99  --inst_activity_threshold               500
% 12.04/1.99  --inst_out_proof                        true
% 12.04/1.99  
% 12.04/1.99  ------ Resolution Options
% 12.04/1.99  
% 12.04/1.99  --resolution_flag                       false
% 12.04/1.99  --res_lit_sel                           adaptive
% 12.04/1.99  --res_lit_sel_side                      none
% 12.04/1.99  --res_ordering                          kbo
% 12.04/1.99  --res_to_prop_solver                    active
% 12.04/1.99  --res_prop_simpl_new                    false
% 12.04/1.99  --res_prop_simpl_given                  true
% 12.04/1.99  --res_passive_queue_type                priority_queues
% 12.04/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.04/1.99  --res_passive_queues_freq               [15;5]
% 12.04/1.99  --res_forward_subs                      full
% 12.04/1.99  --res_backward_subs                     full
% 12.04/1.99  --res_forward_subs_resolution           true
% 12.04/1.99  --res_backward_subs_resolution          true
% 12.04/1.99  --res_orphan_elimination                true
% 12.04/1.99  --res_time_limit                        2.
% 12.04/1.99  --res_out_proof                         true
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Options
% 12.04/1.99  
% 12.04/1.99  --superposition_flag                    true
% 12.04/1.99  --sup_passive_queue_type                priority_queues
% 12.04/1.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.04/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.04/1.99  --demod_completeness_check              fast
% 12.04/1.99  --demod_use_ground                      true
% 12.04/1.99  --sup_to_prop_solver                    active
% 12.04/1.99  --sup_prop_simpl_new                    false
% 12.04/1.99  --sup_prop_simpl_given                  false
% 12.04/1.99  --sup_fun_splitting                     true
% 12.04/1.99  --sup_smt_interval                      10000
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Simplification Setup
% 12.04/1.99  
% 12.04/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.04/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.99  --sup_full_triv                         [TrivRules]
% 12.04/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.04/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.04/1.99  --sup_immed_triv                        [TrivRules]
% 12.04/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_immed_bw_main                     []
% 12.04/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.04/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.04/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 12.04/1.99  
% 12.04/1.99  ------ Combination Options
% 12.04/1.99  
% 12.04/1.99  --comb_res_mult                         1
% 12.04/1.99  --comb_sup_mult                         1
% 12.04/1.99  --comb_inst_mult                        1000000
% 12.04/1.99  
% 12.04/1.99  ------ Debug Options
% 12.04/1.99  
% 12.04/1.99  --dbg_backtrace                         false
% 12.04/1.99  --dbg_dump_prop_clauses                 false
% 12.04/1.99  --dbg_dump_prop_clauses_file            -
% 12.04/1.99  --dbg_out_stat                          false
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  ------ Proving...
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  % SZS status Theorem for theBenchmark.p
% 12.04/1.99  
% 12.04/1.99   Resolution empty clause
% 12.04/1.99  
% 12.04/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 12.04/1.99  
% 12.04/1.99  fof(f1,axiom,(
% 12.04/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f18,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f1])).
% 12.04/1.99  
% 12.04/1.99  fof(f8,axiom,(
% 12.04/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f25,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f8])).
% 12.04/1.99  
% 12.04/1.99  fof(f2,axiom,(
% 12.04/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f19,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f2])).
% 12.04/1.99  
% 12.04/1.99  fof(f11,axiom,(
% 12.04/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f28,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.04/1.99    inference(cnf_transformation,[],[f11])).
% 12.04/1.99  
% 12.04/1.99  fof(f30,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 12.04/1.99    inference(definition_unfolding,[],[f19,f28,f28])).
% 12.04/1.99  
% 12.04/1.99  fof(f7,axiom,(
% 12.04/1.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f24,plain,(
% 12.04/1.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.04/1.99    inference(cnf_transformation,[],[f7])).
% 12.04/1.99  
% 12.04/1.99  fof(f6,axiom,(
% 12.04/1.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f23,plain,(
% 12.04/1.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 12.04/1.99    inference(cnf_transformation,[],[f6])).
% 12.04/1.99  
% 12.04/1.99  fof(f31,plain,(
% 12.04/1.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 12.04/1.99    inference(definition_unfolding,[],[f23,f28])).
% 12.04/1.99  
% 12.04/1.99  fof(f9,axiom,(
% 12.04/1.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f26,plain,(
% 12.04/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f9])).
% 12.04/1.99  
% 12.04/1.99  fof(f5,axiom,(
% 12.04/1.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f22,plain,(
% 12.04/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.04/1.99    inference(cnf_transformation,[],[f5])).
% 12.04/1.99  
% 12.04/1.99  fof(f12,conjecture,(
% 12.04/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f13,negated_conjecture,(
% 12.04/1.99    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 12.04/1.99    inference(negated_conjecture,[],[f12])).
% 12.04/1.99  
% 12.04/1.99  fof(f15,plain,(
% 12.04/1.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 12.04/1.99    inference(ennf_transformation,[],[f13])).
% 12.04/1.99  
% 12.04/1.99  fof(f16,plain,(
% 12.04/1.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 12.04/1.99    introduced(choice_axiom,[])).
% 12.04/1.99  
% 12.04/1.99  fof(f17,plain,(
% 12.04/1.99    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 12.04/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 12.04/1.99  
% 12.04/1.99  fof(f29,plain,(
% 12.04/1.99    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 12.04/1.99    inference(cnf_transformation,[],[f17])).
% 12.04/1.99  
% 12.04/1.99  fof(f3,axiom,(
% 12.04/1.99    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f20,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f3])).
% 12.04/1.99  
% 12.04/1.99  fof(f32,plain,(
% 12.04/1.99    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 12.04/1.99    inference(definition_unfolding,[],[f29,f28,f20,f20])).
% 12.04/1.99  
% 12.04/1.99  fof(f4,axiom,(
% 12.04/1.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f14,plain,(
% 12.04/1.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 12.04/1.99    inference(rectify,[],[f4])).
% 12.04/1.99  
% 12.04/1.99  fof(f21,plain,(
% 12.04/1.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 12.04/1.99    inference(cnf_transformation,[],[f14])).
% 12.04/1.99  
% 12.04/1.99  fof(f10,axiom,(
% 12.04/1.99    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 12.04/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f27,plain,(
% 12.04/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f10])).
% 12.04/1.99  
% 12.04/1.99  cnf(c_0,plain,
% 12.04/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(cnf_transformation,[],[f18]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_6,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 12.04/1.99      inference(cnf_transformation,[],[f25]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_45,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_1,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 12.04/1.99      inference(cnf_transformation,[],[f30]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_110,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_45,c_1]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_5,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.04/1.99      inference(cnf_transformation,[],[f24]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 12.04/1.99      inference(cnf_transformation,[],[f31]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_29,plain,
% 12.04/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_4,c_5]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_7,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.04/1.99      inference(cnf_transformation,[],[f26]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_62,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_29,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.04/1.99      inference(cnf_transformation,[],[f22]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_32,plain,
% 12.04/1.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_47,plain,
% 12.04/1.99      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_32,c_6]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_52,plain,
% 12.04/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_47,c_29]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_73,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_62,c_52]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_116,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_110,c_5,c_73]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_194,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_0,c_116]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_291,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_194,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_9,negated_conjecture,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.04/1.99      inference(cnf_transformation,[],[f32]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_31,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_0,c_9]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_52186,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_291,c_31]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2,plain,
% 12.04/1.99      ( k2_xboole_0(X0,X0) = X0 ),
% 12.04/1.99      inference(cnf_transformation,[],[f21]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_67,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_71,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_67,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3474,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_2,c_71]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_69,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_7,c_29]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3730,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_3474,c_69]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4539,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_3730,c_116]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_8,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 12.04/1.99      inference(cnf_transformation,[],[f27]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_142,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_8,c_73]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_369,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_116,c_142]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_511,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_369,c_194]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4551,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_4539,c_511]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4674,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4551,c_194]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_366,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_194,c_142]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_426,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1,c_366]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_546,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1,c_426]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3774,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1,c_546]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_557,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_116,c_426]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_594,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_557,c_45]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_66,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2139,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),k1_xboole_0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_594,c_66]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2330,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X1)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_2139,c_3,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2331,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_2330,c_2]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3957,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_3774,c_2331]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4410,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_3957,c_194]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4789,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4410,c_5]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4812,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_45,c_4789]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_16054,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4674,c_4812]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_209,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_73,c_116]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_1837,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_209,c_5]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_1849,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_0,c_1837]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_1969,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1849,c_116]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_138,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_0,c_73]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_1995,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_1969,c_138]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2963,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1837,c_1995]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3026,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_2963,c_1995]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_159,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_138,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_63,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_72,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_63,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_163,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_159,c_52,c_72]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_246,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_0,c_163]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4804,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1,c_4789]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_5507,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_246,c_4804]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_5577,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_5507,c_5]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_212,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_116,c_69]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_85,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_10185,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_212,c_85]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_10528,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(k4_xboole_0(X1,X2),X2))) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_10185,c_5]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4618,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_7,c_4551]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_5414,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1849,c_4618]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_83,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_8432,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k2_xboole_0(X2,X4))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))),X2) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_5414,c_83]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_10529,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k2_xboole_0(X2,X1)))),X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_10528,c_212,c_1995,c_8432]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_700,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_594,c_8]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_711,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_700,c_32]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4870,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4789,c_0]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_10530,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_10529,c_711,c_4870]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_16261,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_16054,c_3026,c_5577,c_10530]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4807,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_6,c_4789]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2993,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1995,c_8]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2998,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_2993,c_1995]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2999,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_2998,c_5]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_14320,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4807,c_2999]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_16262,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_16261,c_14320]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_16441,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_16262,c_0]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4984,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_45,c_4870]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_18922,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_16441,c_4984]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4681,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4551,c_4551]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_16177,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4812,c_2999]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_19198,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_18922,c_4681,c_16177]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_89,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_19350,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_19198,c_89]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_91,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_96,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_91,c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_20502,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_96,c_19198]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_92,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_20717,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X2,X1))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_20502,c_92]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_20742,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X2)),k4_xboole_0(X1,X2)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_20717,c_19350]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_20724,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_20502,c_85]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_16701,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),X3),k4_xboole_0(X1,X2)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_16441,c_83]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_20731,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_20724,c_16701]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_20743,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(X2,X0)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_20742,c_20731]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4425,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_3957,c_8]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4433,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_4425,c_3]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_16058,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_0,c_4812]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_31416,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4433,c_16058]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_14203,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4433,c_4807]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_14225,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1837,c_4807]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_1871,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1837,c_0]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2962,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1871,c_1995]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3027,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_2962,c_1995]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_14376,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_14225,c_45,c_3027]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_30083,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4433,c_14320]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_19005,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4433,c_4984]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_19267,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_4433,c_19198]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_19408,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_19267,c_19198]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_30239,plain,
% 12.04/1.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_30083,c_19005,c_19408]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_31681,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 12.04/1.99      inference(light_normalisation,
% 12.04/1.99                [status(thm)],
% 12.04/1.99                [c_31416,c_14203,c_14376,c_30239]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_49433,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_89,c_31681]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_52187,plain,
% 12.04/1.99      ( k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_52186,c_19350,c_20743,c_49433]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_52188,plain,
% 12.04/1.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_52187,c_4433]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_52189,plain,
% 12.04/1.99      ( $false ),
% 12.04/1.99      inference(equality_resolution_simp,[status(thm)],[c_52188]) ).
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.04/1.99  
% 12.04/1.99  ------                               Statistics
% 12.04/1.99  
% 12.04/1.99  ------ General
% 12.04/1.99  
% 12.04/1.99  abstr_ref_over_cycles:                  0
% 12.04/1.99  abstr_ref_under_cycles:                 0
% 12.04/1.99  gc_basic_clause_elim:                   0
% 12.04/1.99  forced_gc_time:                         0
% 12.04/1.99  parsing_time:                           0.007
% 12.04/1.99  unif_index_cands_time:                  0.
% 12.04/1.99  unif_index_add_time:                    0.
% 12.04/1.99  orderings_time:                         0.
% 12.04/1.99  out_proof_time:                         0.007
% 12.04/1.99  total_time:                             1.492
% 12.04/1.99  num_of_symbols:                         38
% 12.04/1.99  num_of_terms:                           81695
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing
% 12.04/1.99  
% 12.04/1.99  num_of_splits:                          0
% 12.04/1.99  num_of_split_atoms:                     2
% 12.04/1.99  num_of_reused_defs:                     8
% 12.04/1.99  num_eq_ax_congr_red:                    0
% 12.04/1.99  num_of_sem_filtered_clauses:            0
% 12.04/1.99  num_of_subtypes:                        0
% 12.04/1.99  monotx_restored_types:                  0
% 12.04/1.99  sat_num_of_epr_types:                   0
% 12.04/1.99  sat_num_of_non_cyclic_types:            0
% 12.04/1.99  sat_guarded_non_collapsed_types:        0
% 12.04/1.99  num_pure_diseq_elim:                    0
% 12.04/1.99  simp_replaced_by:                       0
% 12.04/1.99  res_preprocessed:                       24
% 12.04/1.99  prep_upred:                             0
% 12.04/1.99  prep_unflattend:                        0
% 12.04/1.99  smt_new_axioms:                         0
% 12.04/1.99  pred_elim_cands:                        0
% 12.04/1.99  pred_elim:                              0
% 12.04/1.99  pred_elim_cl:                           0
% 12.04/1.99  pred_elim_cycles:                       0
% 12.04/1.99  merged_defs:                            0
% 12.04/1.99  merged_defs_ncl:                        0
% 12.04/1.99  bin_hyper_res:                          0
% 12.04/1.99  prep_cycles:                            2
% 12.04/1.99  pred_elim_time:                         0.
% 12.04/1.99  splitting_time:                         0.
% 12.04/1.99  sem_filter_time:                        0.
% 12.04/1.99  monotx_time:                            0.
% 12.04/1.99  subtype_inf_time:                       0.
% 12.04/1.99  
% 12.04/1.99  ------ Problem properties
% 12.04/1.99  
% 12.04/1.99  clauses:                                10
% 12.04/1.99  conjectures:                            1
% 12.04/1.99  epr:                                    0
% 12.04/1.99  horn:                                   10
% 12.04/1.99  ground:                                 1
% 12.04/1.99  unary:                                  10
% 12.04/1.99  binary:                                 0
% 12.04/1.99  lits:                                   10
% 12.04/1.99  lits_eq:                                10
% 12.04/1.99  fd_pure:                                0
% 12.04/1.99  fd_pseudo:                              0
% 12.04/1.99  fd_cond:                                0
% 12.04/1.99  fd_pseudo_cond:                         0
% 12.04/1.99  ac_symbols:                             1
% 12.04/1.99  
% 12.04/1.99  ------ Propositional Solver
% 12.04/1.99  
% 12.04/1.99  prop_solver_calls:                      13
% 12.04/1.99  prop_fast_solver_calls:                 60
% 12.04/1.99  smt_solver_calls:                       0
% 12.04/1.99  smt_fast_solver_calls:                  0
% 12.04/1.99  prop_num_of_clauses:                    343
% 12.04/1.99  prop_preprocess_simplified:             424
% 12.04/1.99  prop_fo_subsumed:                       0
% 12.04/1.99  prop_solver_time:                       0.
% 12.04/1.99  smt_solver_time:                        0.
% 12.04/1.99  smt_fast_solver_time:                   0.
% 12.04/1.99  prop_fast_solver_time:                  0.
% 12.04/1.99  prop_unsat_core_time:                   0.
% 12.04/1.99  
% 12.04/1.99  ------ QBF
% 12.04/1.99  
% 12.04/1.99  qbf_q_res:                              0
% 12.04/1.99  qbf_num_tautologies:                    0
% 12.04/1.99  qbf_prep_cycles:                        0
% 12.04/1.99  
% 12.04/1.99  ------ BMC1
% 12.04/1.99  
% 12.04/1.99  bmc1_current_bound:                     -1
% 12.04/1.99  bmc1_last_solved_bound:                 -1
% 12.04/1.99  bmc1_unsat_core_size:                   -1
% 12.04/1.99  bmc1_unsat_core_parents_size:           -1
% 12.04/1.99  bmc1_merge_next_fun:                    0
% 12.04/1.99  bmc1_unsat_core_clauses_time:           0.
% 12.04/1.99  
% 12.04/1.99  ------ Instantiation
% 12.04/1.99  
% 12.04/1.99  inst_num_of_clauses:                    0
% 12.04/1.99  inst_num_in_passive:                    0
% 12.04/1.99  inst_num_in_active:                     0
% 12.04/1.99  inst_num_in_unprocessed:                0
% 12.04/1.99  inst_num_of_loops:                      0
% 12.04/1.99  inst_num_of_learning_restarts:          0
% 12.04/1.99  inst_num_moves_active_passive:          0
% 12.04/1.99  inst_lit_activity:                      0
% 12.04/1.99  inst_lit_activity_moves:                0
% 12.04/1.99  inst_num_tautologies:                   0
% 12.04/1.99  inst_num_prop_implied:                  0
% 12.04/1.99  inst_num_existing_simplified:           0
% 12.04/1.99  inst_num_eq_res_simplified:             0
% 12.04/1.99  inst_num_child_elim:                    0
% 12.04/1.99  inst_num_of_dismatching_blockings:      0
% 12.04/1.99  inst_num_of_non_proper_insts:           0
% 12.04/1.99  inst_num_of_duplicates:                 0
% 12.04/1.99  inst_inst_num_from_inst_to_res:         0
% 12.04/1.99  inst_dismatching_checking_time:         0.
% 12.04/1.99  
% 12.04/1.99  ------ Resolution
% 12.04/1.99  
% 12.04/1.99  res_num_of_clauses:                     0
% 12.04/1.99  res_num_in_passive:                     0
% 12.04/1.99  res_num_in_active:                      0
% 12.04/1.99  res_num_of_loops:                       26
% 12.04/1.99  res_forward_subset_subsumed:            0
% 12.04/1.99  res_backward_subset_subsumed:           0
% 12.04/1.99  res_forward_subsumed:                   0
% 12.04/1.99  res_backward_subsumed:                  0
% 12.04/1.99  res_forward_subsumption_resolution:     0
% 12.04/1.99  res_backward_subsumption_resolution:    0
% 12.04/1.99  res_clause_to_clause_subsumption:       135735
% 12.04/1.99  res_orphan_elimination:                 0
% 12.04/1.99  res_tautology_del:                      0
% 12.04/1.99  res_num_eq_res_simplified:              0
% 12.04/1.99  res_num_sel_changes:                    0
% 12.04/1.99  res_moves_from_active_to_pass:          0
% 12.04/1.99  
% 12.04/1.99  ------ Superposition
% 12.04/1.99  
% 12.04/1.99  sup_time_total:                         0.
% 12.04/1.99  sup_time_generating:                    0.
% 12.04/1.99  sup_time_sim_full:                      0.
% 12.04/1.99  sup_time_sim_immed:                     0.
% 12.04/1.99  
% 12.04/1.99  sup_num_of_clauses:                     5642
% 12.04/1.99  sup_num_in_active:                      154
% 12.04/1.99  sup_num_in_passive:                     5488
% 12.04/1.99  sup_num_of_loops:                       214
% 12.04/1.99  sup_fw_superposition:                   19255
% 12.04/1.99  sup_bw_superposition:                   15813
% 12.04/1.99  sup_immediate_simplified:               15655
% 12.04/1.99  sup_given_eliminated:                   9
% 12.04/1.99  comparisons_done:                       0
% 12.04/1.99  comparisons_avoided:                    0
% 12.04/1.99  
% 12.04/1.99  ------ Simplifications
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  sim_fw_subset_subsumed:                 0
% 12.04/1.99  sim_bw_subset_subsumed:                 0
% 12.04/1.99  sim_fw_subsumed:                        2354
% 12.04/1.99  sim_bw_subsumed:                        105
% 12.04/1.99  sim_fw_subsumption_res:                 0
% 12.04/1.99  sim_bw_subsumption_res:                 0
% 12.04/1.99  sim_tautology_del:                      0
% 12.04/1.99  sim_eq_tautology_del:                   4340
% 12.04/1.99  sim_eq_res_simp:                        0
% 12.04/1.99  sim_fw_demodulated:                     10573
% 12.04/1.99  sim_bw_demodulated:                     228
% 12.04/1.99  sim_light_normalised:                   5998
% 12.04/1.99  sim_joinable_taut:                      83
% 12.04/1.99  sim_joinable_simp:                      0
% 12.04/1.99  sim_ac_normalised:                      0
% 12.04/1.99  sim_smt_subsumption:                    0
% 12.04/1.99  
%------------------------------------------------------------------------------
