%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:56 EST 2020

% Result     : Theorem 11.04s
% Output     : CNFRefutation 11.04s
% Verified   : 
% Statistics : Number of formulae       :  220 (34387 expanded)
%              Number of clauses        :  189 (11233 expanded)
%              Number of leaves         :   12 (9987 expanded)
%              Depth                    :   35
%              Number of atoms          :  221 (34388 expanded)
%              Number of equality atoms :  220 (34387 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f18])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f23,f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f18,f23])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_27,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_3])).

cnf(c_84,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_27])).

cnf(c_85,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_84,c_6])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_131,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_85,c_1])).

cnf(c_140,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_131,c_3])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_175,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_140,c_4])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_176,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_175,c_2])).

cnf(c_203,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_176])).

cnf(c_66,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_6646,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_203,c_66])).

cnf(c_31,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_27,c_2])).

cnf(c_6868,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6646,c_31])).

cnf(c_6869,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_6868,c_4])).

cnf(c_106,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_52,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_74,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_114,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_106,c_52,c_74])).

cnf(c_188,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_114])).

cnf(c_306,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_176,c_188])).

cnf(c_312,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_306,c_3])).

cnf(c_275,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_203,c_4])).

cnf(c_135,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_85,c_27])).

cnf(c_136,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_135,c_114])).

cnf(c_283,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_275,c_4,c_136])).

cnf(c_721,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_188,c_283])).

cnf(c_758,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_721,c_4])).

cnf(c_4514,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_312,c_758])).

cnf(c_16586,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6869,c_4514])).

cnf(c_618,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_52,c_52,c_114])).

cnf(c_31495,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)),k4_xboole_0(k2_xboole_0(X2,X0),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_16586,c_618])).

cnf(c_213,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_176,c_2])).

cnf(c_215,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_213,c_31])).

cnf(c_386,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_215])).

cnf(c_173,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_140,c_4])).

cnf(c_178,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_173,c_136])).

cnf(c_840,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_386,c_178])).

cnf(c_6668,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_840,c_66])).

cnf(c_6839,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6668,c_31])).

cnf(c_7577,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6839,c_176])).

cnf(c_232,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_178,c_4])).

cnf(c_61,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_4,c_4])).

cnf(c_71,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_61,c_4])).

cnf(c_236,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_232,c_71,c_136])).

cnf(c_489,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_188,c_236])).

cnf(c_7872,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7577,c_489])).

cnf(c_262,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_203])).

cnf(c_2210,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_262,c_1])).

cnf(c_76,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_93,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_76,c_4])).

cnf(c_1597,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_840,c_2])).

cnf(c_233,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_178,c_2])).

cnf(c_235,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_233,c_31])).

cnf(c_443,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_235])).

cnf(c_305,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_178,c_188])).

cnf(c_313,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_305,c_3])).

cnf(c_939,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_443,c_313])).

cnf(c_961,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_939,c_443])).

cnf(c_1598,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1597,c_961])).

cnf(c_2214,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_2210,c_4,c_93,c_1598])).

cnf(c_7265,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_4,c_2214])).

cnf(c_7423,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),X3) ),
    inference(superposition,[status(thm)],[c_2214,c_4])).

cnf(c_7472,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_7423,c_71])).

cnf(c_7949,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X0,X2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7872,c_4,c_7265,c_7472])).

cnf(c_826,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_386])).

cnf(c_860,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_826,c_386])).

cnf(c_1671,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_176,c_860])).

cnf(c_797,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_313])).

cnf(c_1729,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1671,c_797])).

cnf(c_711,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_283])).

cnf(c_1071,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_711,c_4])).

cnf(c_1084,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1071,c_4,c_136])).

cnf(c_7593,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X2),k2_xboole_0(X0,X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6839,c_1084])).

cnf(c_7614,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,k2_xboole_0(X0,X3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7593,c_4,c_7265,c_7472])).

cnf(c_7950,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7949,c_71,c_1729,c_7614])).

cnf(c_21171,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X2),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7950,c_74])).

cnf(c_7575,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_6839,c_312])).

cnf(c_7620,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_7575,c_6839])).

cnf(c_58,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_8073,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_7620,c_58])).

cnf(c_8095,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_8073,c_3,c_176])).

cnf(c_8206,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_8095,c_4])).

cnf(c_8243,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_8206,c_4])).

cnf(c_8215,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8095,c_1])).

cnf(c_8234,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8215,c_3,c_178])).

cnf(c_8907,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_840,c_8234])).

cnf(c_8994,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_8907,c_961])).

cnf(c_21212,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_21171,c_8243,c_8994])).

cnf(c_31546,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_31495,c_21212])).

cnf(c_7407,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2214,c_860])).

cnf(c_847,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_386,c_283])).

cnf(c_6669,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_847,c_66])).

cnf(c_6837,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6669,c_31])).

cnf(c_6838,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_6837,c_4])).

cnf(c_14012,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6838,c_176])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_70,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_67,c_4])).

cnf(c_922,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_443])).

cnf(c_202,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_176])).

cnf(c_355,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_202,c_2])).

cnf(c_358,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_355,c_31])).

cnf(c_966,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_922,c_358])).

cnf(c_6690,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_966,c_66])).

cnf(c_6691,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_860,c_66])).

cnf(c_6821,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_6691,c_66])).

cnf(c_6822,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_6690,c_6821])).

cnf(c_8410,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_70,c_6822])).

cnf(c_195,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_114,c_0])).

cnf(c_8571,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = X0 ),
    inference(superposition,[status(thm)],[c_8410,c_195])).

cnf(c_27488,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_14012,c_8571])).

cnf(c_326,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_202])).

cnf(c_97,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_20707,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0)))),k1_xboole_0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_326,c_97])).

cnf(c_8875,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_8234])).

cnf(c_8165,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_966,c_8095])).

cnf(c_8266,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_8165,c_8234])).

cnf(c_8287,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_8266])).

cnf(c_9116,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_966,c_8287])).

cnf(c_11508,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_9116,c_8234])).

cnf(c_1696,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_860,c_0])).

cnf(c_11511,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_9116,c_1696])).

cnf(c_11532,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_11511,c_6822])).

cnf(c_11534,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_11508,c_11532])).

cnf(c_20754,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_20707,c_8875,c_11534])).

cnf(c_27555,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_27488,c_3,c_140,c_20754])).

cnf(c_8167,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_797,c_8095])).

cnf(c_8263,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8167,c_8095])).

cnf(c_9784,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8263,c_4])).

cnf(c_9824,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_9784,c_4])).

cnf(c_27556,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_27555,c_9824])).

cnf(c_31547,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_31546,c_7407,c_8994,c_27556])).

cnf(c_8,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_28,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_42999,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_31547,c_28])).

cnf(c_111,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_212,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_176,c_4])).

cnf(c_216,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_212,c_71,c_136])).

cnf(c_425,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_216,c_188])).

cnf(c_439,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_425,c_3])).

cnf(c_21679,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_961,c_439])).

cnf(c_1073,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_711,c_618])).

cnf(c_1082,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1073,c_4])).

cnf(c_1083,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1082,c_31,c_966])).

cnf(c_21683,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)),X3) = k2_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(k2_xboole_0(X2,X0),X3)) ),
    inference(superposition,[status(thm)],[c_1083,c_439])).

cnf(c_729,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_283,c_188])).

cnf(c_753,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_729,c_4])).

cnf(c_754,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_753,c_31])).

cnf(c_3971,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_754])).

cnf(c_21882,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_21683,c_3971])).

cnf(c_21886,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_21679,c_21882])).

cnf(c_21887,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_21886,c_961])).

cnf(c_837,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_386,c_236])).

cnf(c_5063,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1729,c_837])).

cnf(c_432,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_216,c_4])).

cnf(c_436,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_432,c_71,c_136])).

cnf(c_3286,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1729,c_436])).

cnf(c_5211,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5063,c_71,c_1598,c_3286])).

cnf(c_18616,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5211,c_2214])).

cnf(c_36393,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_18616,c_97])).

cnf(c_36486,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X2),X1),k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_36393,c_8994])).

cnf(c_7427,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2214,c_1696])).

cnf(c_36487,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_36486,c_7427,c_9824])).

cnf(c_8922,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8234,c_758])).

cnf(c_6695,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_313,c_66])).

cnf(c_6817,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_6695,c_1696])).

cnf(c_8983,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8922,c_71,c_6817])).

cnf(c_24832,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8983,c_97])).

cnf(c_24913,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_24832,c_8994])).

cnf(c_18595,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5211,c_74])).

cnf(c_18632,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_18595,c_8994])).

cnf(c_18633,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_18632,c_8243])).

cnf(c_21616,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1696,c_439])).

cnf(c_764,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_312])).

cnf(c_21630,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_764,c_439])).

cnf(c_21939,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_21630,c_21882])).

cnf(c_21947,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_21616,c_21939])).

cnf(c_24914,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_24913,c_7427,c_18633,c_21947])).

cnf(c_36488,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_36487,c_24914])).

cnf(c_41328,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_21887,c_36488])).

cnf(c_41403,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_111,c_41328])).

cnf(c_43001,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_42999,c_1696,c_41403])).

cnf(c_43648,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_0,c_43001])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.04/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.04/2.00  
% 11.04/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.04/2.00  
% 11.04/2.00  ------  iProver source info
% 11.04/2.00  
% 11.04/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.04/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.04/2.00  git: non_committed_changes: false
% 11.04/2.00  git: last_make_outside_of_git: false
% 11.04/2.00  
% 11.04/2.00  ------ 
% 11.04/2.00  
% 11.04/2.00  ------ Input Options
% 11.04/2.00  
% 11.04/2.00  --out_options                           all
% 11.04/2.00  --tptp_safe_out                         true
% 11.04/2.00  --problem_path                          ""
% 11.04/2.00  --include_path                          ""
% 11.04/2.00  --clausifier                            res/vclausify_rel
% 11.04/2.00  --clausifier_options                    --mode clausify
% 11.04/2.00  --stdin                                 false
% 11.04/2.00  --stats_out                             all
% 11.04/2.00  
% 11.04/2.00  ------ General Options
% 11.04/2.00  
% 11.04/2.00  --fof                                   false
% 11.04/2.00  --time_out_real                         305.
% 11.04/2.00  --time_out_virtual                      -1.
% 11.04/2.00  --symbol_type_check                     false
% 11.04/2.00  --clausify_out                          false
% 11.04/2.00  --sig_cnt_out                           false
% 11.04/2.00  --trig_cnt_out                          false
% 11.04/2.00  --trig_cnt_out_tolerance                1.
% 11.04/2.00  --trig_cnt_out_sk_spl                   false
% 11.04/2.00  --abstr_cl_out                          false
% 11.04/2.00  
% 11.04/2.00  ------ Global Options
% 11.04/2.00  
% 11.04/2.00  --schedule                              default
% 11.04/2.00  --add_important_lit                     false
% 11.04/2.00  --prop_solver_per_cl                    1000
% 11.04/2.00  --min_unsat_core                        false
% 11.04/2.00  --soft_assumptions                      false
% 11.04/2.00  --soft_lemma_size                       3
% 11.04/2.00  --prop_impl_unit_size                   0
% 11.04/2.00  --prop_impl_unit                        []
% 11.04/2.00  --share_sel_clauses                     true
% 11.04/2.00  --reset_solvers                         false
% 11.04/2.00  --bc_imp_inh                            [conj_cone]
% 11.04/2.00  --conj_cone_tolerance                   3.
% 11.04/2.00  --extra_neg_conj                        none
% 11.04/2.00  --large_theory_mode                     true
% 11.04/2.00  --prolific_symb_bound                   200
% 11.04/2.00  --lt_threshold                          2000
% 11.04/2.00  --clause_weak_htbl                      true
% 11.04/2.00  --gc_record_bc_elim                     false
% 11.04/2.00  
% 11.04/2.00  ------ Preprocessing Options
% 11.04/2.00  
% 11.04/2.00  --preprocessing_flag                    true
% 11.04/2.00  --time_out_prep_mult                    0.1
% 11.04/2.00  --splitting_mode                        input
% 11.04/2.00  --splitting_grd                         true
% 11.04/2.00  --splitting_cvd                         false
% 11.04/2.00  --splitting_cvd_svl                     false
% 11.04/2.00  --splitting_nvd                         32
% 11.04/2.00  --sub_typing                            true
% 11.04/2.00  --prep_gs_sim                           true
% 11.04/2.00  --prep_unflatten                        true
% 11.04/2.00  --prep_res_sim                          true
% 11.04/2.00  --prep_upred                            true
% 11.04/2.00  --prep_sem_filter                       exhaustive
% 11.04/2.00  --prep_sem_filter_out                   false
% 11.04/2.00  --pred_elim                             true
% 11.04/2.00  --res_sim_input                         true
% 11.04/2.00  --eq_ax_congr_red                       true
% 11.04/2.00  --pure_diseq_elim                       true
% 11.04/2.00  --brand_transform                       false
% 11.04/2.00  --non_eq_to_eq                          false
% 11.04/2.00  --prep_def_merge                        true
% 11.04/2.00  --prep_def_merge_prop_impl              false
% 11.04/2.00  --prep_def_merge_mbd                    true
% 11.04/2.00  --prep_def_merge_tr_red                 false
% 11.04/2.00  --prep_def_merge_tr_cl                  false
% 11.04/2.00  --smt_preprocessing                     true
% 11.04/2.00  --smt_ac_axioms                         fast
% 11.04/2.00  --preprocessed_out                      false
% 11.04/2.00  --preprocessed_stats                    false
% 11.04/2.00  
% 11.04/2.00  ------ Abstraction refinement Options
% 11.04/2.00  
% 11.04/2.00  --abstr_ref                             []
% 11.04/2.00  --abstr_ref_prep                        false
% 11.04/2.00  --abstr_ref_until_sat                   false
% 11.04/2.00  --abstr_ref_sig_restrict                funpre
% 11.04/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.04/2.00  --abstr_ref_under                       []
% 11.04/2.00  
% 11.04/2.00  ------ SAT Options
% 11.04/2.00  
% 11.04/2.00  --sat_mode                              false
% 11.04/2.00  --sat_fm_restart_options                ""
% 11.04/2.00  --sat_gr_def                            false
% 11.04/2.00  --sat_epr_types                         true
% 11.04/2.00  --sat_non_cyclic_types                  false
% 11.04/2.00  --sat_finite_models                     false
% 11.04/2.00  --sat_fm_lemmas                         false
% 11.04/2.00  --sat_fm_prep                           false
% 11.04/2.00  --sat_fm_uc_incr                        true
% 11.04/2.00  --sat_out_model                         small
% 11.04/2.00  --sat_out_clauses                       false
% 11.04/2.00  
% 11.04/2.00  ------ QBF Options
% 11.04/2.00  
% 11.04/2.00  --qbf_mode                              false
% 11.04/2.00  --qbf_elim_univ                         false
% 11.04/2.00  --qbf_dom_inst                          none
% 11.04/2.00  --qbf_dom_pre_inst                      false
% 11.04/2.00  --qbf_sk_in                             false
% 11.04/2.00  --qbf_pred_elim                         true
% 11.04/2.00  --qbf_split                             512
% 11.04/2.00  
% 11.04/2.00  ------ BMC1 Options
% 11.04/2.00  
% 11.04/2.00  --bmc1_incremental                      false
% 11.04/2.00  --bmc1_axioms                           reachable_all
% 11.04/2.00  --bmc1_min_bound                        0
% 11.04/2.00  --bmc1_max_bound                        -1
% 11.04/2.00  --bmc1_max_bound_default                -1
% 11.04/2.00  --bmc1_symbol_reachability              true
% 11.04/2.00  --bmc1_property_lemmas                  false
% 11.04/2.00  --bmc1_k_induction                      false
% 11.04/2.00  --bmc1_non_equiv_states                 false
% 11.04/2.00  --bmc1_deadlock                         false
% 11.04/2.00  --bmc1_ucm                              false
% 11.04/2.00  --bmc1_add_unsat_core                   none
% 11.04/2.00  --bmc1_unsat_core_children              false
% 11.04/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.04/2.00  --bmc1_out_stat                         full
% 11.04/2.00  --bmc1_ground_init                      false
% 11.04/2.00  --bmc1_pre_inst_next_state              false
% 11.04/2.00  --bmc1_pre_inst_state                   false
% 11.04/2.00  --bmc1_pre_inst_reach_state             false
% 11.04/2.00  --bmc1_out_unsat_core                   false
% 11.04/2.00  --bmc1_aig_witness_out                  false
% 11.04/2.00  --bmc1_verbose                          false
% 11.04/2.00  --bmc1_dump_clauses_tptp                false
% 11.04/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.04/2.00  --bmc1_dump_file                        -
% 11.04/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.04/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.04/2.00  --bmc1_ucm_extend_mode                  1
% 11.04/2.00  --bmc1_ucm_init_mode                    2
% 11.04/2.00  --bmc1_ucm_cone_mode                    none
% 11.04/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.04/2.00  --bmc1_ucm_relax_model                  4
% 11.04/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.04/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.04/2.00  --bmc1_ucm_layered_model                none
% 11.04/2.00  --bmc1_ucm_max_lemma_size               10
% 11.04/2.00  
% 11.04/2.00  ------ AIG Options
% 11.04/2.00  
% 11.04/2.00  --aig_mode                              false
% 11.04/2.00  
% 11.04/2.00  ------ Instantiation Options
% 11.04/2.00  
% 11.04/2.00  --instantiation_flag                    true
% 11.04/2.00  --inst_sos_flag                         false
% 11.04/2.00  --inst_sos_phase                        true
% 11.04/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.04/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.04/2.00  --inst_lit_sel_side                     num_symb
% 11.04/2.00  --inst_solver_per_active                1400
% 11.04/2.00  --inst_solver_calls_frac                1.
% 11.04/2.00  --inst_passive_queue_type               priority_queues
% 11.04/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.04/2.00  --inst_passive_queues_freq              [25;2]
% 11.04/2.00  --inst_dismatching                      true
% 11.04/2.00  --inst_eager_unprocessed_to_passive     true
% 11.04/2.00  --inst_prop_sim_given                   true
% 11.04/2.00  --inst_prop_sim_new                     false
% 11.04/2.00  --inst_subs_new                         false
% 11.04/2.00  --inst_eq_res_simp                      false
% 11.04/2.00  --inst_subs_given                       false
% 11.04/2.00  --inst_orphan_elimination               true
% 11.04/2.00  --inst_learning_loop_flag               true
% 11.04/2.00  --inst_learning_start                   3000
% 11.04/2.00  --inst_learning_factor                  2
% 11.04/2.00  --inst_start_prop_sim_after_learn       3
% 11.04/2.00  --inst_sel_renew                        solver
% 11.04/2.00  --inst_lit_activity_flag                true
% 11.04/2.00  --inst_restr_to_given                   false
% 11.04/2.00  --inst_activity_threshold               500
% 11.04/2.00  --inst_out_proof                        true
% 11.04/2.00  
% 11.04/2.00  ------ Resolution Options
% 11.04/2.00  
% 11.04/2.00  --resolution_flag                       true
% 11.04/2.00  --res_lit_sel                           adaptive
% 11.04/2.00  --res_lit_sel_side                      none
% 11.04/2.00  --res_ordering                          kbo
% 11.04/2.00  --res_to_prop_solver                    active
% 11.04/2.00  --res_prop_simpl_new                    false
% 11.04/2.00  --res_prop_simpl_given                  true
% 11.04/2.00  --res_passive_queue_type                priority_queues
% 11.04/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.04/2.00  --res_passive_queues_freq               [15;5]
% 11.04/2.00  --res_forward_subs                      full
% 11.04/2.00  --res_backward_subs                     full
% 11.04/2.00  --res_forward_subs_resolution           true
% 11.04/2.00  --res_backward_subs_resolution          true
% 11.04/2.00  --res_orphan_elimination                true
% 11.04/2.00  --res_time_limit                        2.
% 11.04/2.00  --res_out_proof                         true
% 11.04/2.00  
% 11.04/2.00  ------ Superposition Options
% 11.04/2.00  
% 11.04/2.00  --superposition_flag                    true
% 11.04/2.00  --sup_passive_queue_type                priority_queues
% 11.04/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.04/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.04/2.00  --demod_completeness_check              fast
% 11.04/2.00  --demod_use_ground                      true
% 11.04/2.00  --sup_to_prop_solver                    passive
% 11.04/2.00  --sup_prop_simpl_new                    true
% 11.04/2.00  --sup_prop_simpl_given                  true
% 11.04/2.00  --sup_fun_splitting                     false
% 11.04/2.00  --sup_smt_interval                      50000
% 11.04/2.00  
% 11.04/2.00  ------ Superposition Simplification Setup
% 11.04/2.00  
% 11.04/2.00  --sup_indices_passive                   []
% 11.04/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.04/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.04/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.04/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.04/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.04/2.00  --sup_full_bw                           [BwDemod]
% 11.04/2.00  --sup_immed_triv                        [TrivRules]
% 11.04/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.04/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.04/2.00  --sup_immed_bw_main                     []
% 11.04/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.04/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.04/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.04/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.04/2.00  
% 11.04/2.00  ------ Combination Options
% 11.04/2.00  
% 11.04/2.00  --comb_res_mult                         3
% 11.04/2.00  --comb_sup_mult                         2
% 11.04/2.00  --comb_inst_mult                        10
% 11.04/2.00  
% 11.04/2.00  ------ Debug Options
% 11.04/2.00  
% 11.04/2.00  --dbg_backtrace                         false
% 11.04/2.00  --dbg_dump_prop_clauses                 false
% 11.04/2.00  --dbg_dump_prop_clauses_file            -
% 11.04/2.00  --dbg_out_stat                          false
% 11.04/2.00  ------ Parsing...
% 11.04/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.04/2.00  
% 11.04/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.04/2.00  
% 11.04/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.04/2.00  
% 11.04/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.04/2.00  ------ Proving...
% 11.04/2.00  ------ Problem Properties 
% 11.04/2.00  
% 11.04/2.00  
% 11.04/2.00  clauses                                 9
% 11.04/2.00  conjectures                             1
% 11.04/2.00  EPR                                     0
% 11.04/2.00  Horn                                    9
% 11.04/2.00  unary                                   9
% 11.04/2.00  binary                                  0
% 11.04/2.00  lits                                    9
% 11.04/2.00  lits eq                                 9
% 11.04/2.00  fd_pure                                 0
% 11.04/2.00  fd_pseudo                               0
% 11.04/2.00  fd_cond                                 0
% 11.04/2.00  fd_pseudo_cond                          0
% 11.04/2.00  AC symbols                              0
% 11.04/2.00  
% 11.04/2.00  ------ Schedule UEQ
% 11.04/2.00  
% 11.04/2.00  ------ pure equality problem: resolution off 
% 11.04/2.00  
% 11.04/2.00  ------ Option_UEQ Time Limit: Unbounded
% 11.04/2.00  
% 11.04/2.00  
% 11.04/2.00  ------ 
% 11.04/2.00  Current options:
% 11.04/2.00  ------ 
% 11.04/2.00  
% 11.04/2.00  ------ Input Options
% 11.04/2.00  
% 11.04/2.00  --out_options                           all
% 11.04/2.00  --tptp_safe_out                         true
% 11.04/2.00  --problem_path                          ""
% 11.04/2.00  --include_path                          ""
% 11.04/2.00  --clausifier                            res/vclausify_rel
% 11.04/2.00  --clausifier_options                    --mode clausify
% 11.04/2.00  --stdin                                 false
% 11.04/2.00  --stats_out                             all
% 11.04/2.00  
% 11.04/2.00  ------ General Options
% 11.04/2.00  
% 11.04/2.00  --fof                                   false
% 11.04/2.00  --time_out_real                         305.
% 11.04/2.00  --time_out_virtual                      -1.
% 11.04/2.00  --symbol_type_check                     false
% 11.04/2.00  --clausify_out                          false
% 11.04/2.00  --sig_cnt_out                           false
% 11.04/2.00  --trig_cnt_out                          false
% 11.04/2.00  --trig_cnt_out_tolerance                1.
% 11.04/2.00  --trig_cnt_out_sk_spl                   false
% 11.04/2.00  --abstr_cl_out                          false
% 11.04/2.00  
% 11.04/2.00  ------ Global Options
% 11.04/2.00  
% 11.04/2.00  --schedule                              default
% 11.04/2.00  --add_important_lit                     false
% 11.04/2.00  --prop_solver_per_cl                    1000
% 11.04/2.00  --min_unsat_core                        false
% 11.04/2.00  --soft_assumptions                      false
% 11.04/2.00  --soft_lemma_size                       3
% 11.04/2.00  --prop_impl_unit_size                   0
% 11.04/2.00  --prop_impl_unit                        []
% 11.04/2.00  --share_sel_clauses                     true
% 11.04/2.00  --reset_solvers                         false
% 11.04/2.00  --bc_imp_inh                            [conj_cone]
% 11.04/2.00  --conj_cone_tolerance                   3.
% 11.04/2.00  --extra_neg_conj                        none
% 11.04/2.00  --large_theory_mode                     true
% 11.04/2.00  --prolific_symb_bound                   200
% 11.04/2.00  --lt_threshold                          2000
% 11.04/2.00  --clause_weak_htbl                      true
% 11.04/2.00  --gc_record_bc_elim                     false
% 11.04/2.00  
% 11.04/2.00  ------ Preprocessing Options
% 11.04/2.00  
% 11.04/2.00  --preprocessing_flag                    true
% 11.04/2.00  --time_out_prep_mult                    0.1
% 11.04/2.00  --splitting_mode                        input
% 11.04/2.00  --splitting_grd                         true
% 11.04/2.00  --splitting_cvd                         false
% 11.04/2.00  --splitting_cvd_svl                     false
% 11.04/2.00  --splitting_nvd                         32
% 11.04/2.00  --sub_typing                            true
% 11.04/2.00  --prep_gs_sim                           true
% 11.04/2.00  --prep_unflatten                        true
% 11.04/2.00  --prep_res_sim                          true
% 11.04/2.00  --prep_upred                            true
% 11.04/2.00  --prep_sem_filter                       exhaustive
% 11.04/2.00  --prep_sem_filter_out                   false
% 11.04/2.00  --pred_elim                             true
% 11.04/2.00  --res_sim_input                         true
% 11.04/2.00  --eq_ax_congr_red                       true
% 11.04/2.00  --pure_diseq_elim                       true
% 11.04/2.00  --brand_transform                       false
% 11.04/2.00  --non_eq_to_eq                          false
% 11.04/2.00  --prep_def_merge                        true
% 11.04/2.00  --prep_def_merge_prop_impl              false
% 11.04/2.00  --prep_def_merge_mbd                    true
% 11.04/2.00  --prep_def_merge_tr_red                 false
% 11.04/2.00  --prep_def_merge_tr_cl                  false
% 11.04/2.00  --smt_preprocessing                     true
% 11.04/2.00  --smt_ac_axioms                         fast
% 11.04/2.00  --preprocessed_out                      false
% 11.04/2.00  --preprocessed_stats                    false
% 11.04/2.00  
% 11.04/2.00  ------ Abstraction refinement Options
% 11.04/2.00  
% 11.04/2.00  --abstr_ref                             []
% 11.04/2.00  --abstr_ref_prep                        false
% 11.04/2.00  --abstr_ref_until_sat                   false
% 11.04/2.00  --abstr_ref_sig_restrict                funpre
% 11.04/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.04/2.00  --abstr_ref_under                       []
% 11.04/2.00  
% 11.04/2.00  ------ SAT Options
% 11.04/2.00  
% 11.04/2.00  --sat_mode                              false
% 11.04/2.00  --sat_fm_restart_options                ""
% 11.04/2.00  --sat_gr_def                            false
% 11.04/2.00  --sat_epr_types                         true
% 11.04/2.00  --sat_non_cyclic_types                  false
% 11.04/2.00  --sat_finite_models                     false
% 11.04/2.00  --sat_fm_lemmas                         false
% 11.04/2.00  --sat_fm_prep                           false
% 11.04/2.00  --sat_fm_uc_incr                        true
% 11.04/2.00  --sat_out_model                         small
% 11.04/2.00  --sat_out_clauses                       false
% 11.04/2.00  
% 11.04/2.00  ------ QBF Options
% 11.04/2.00  
% 11.04/2.00  --qbf_mode                              false
% 11.04/2.00  --qbf_elim_univ                         false
% 11.04/2.00  --qbf_dom_inst                          none
% 11.04/2.00  --qbf_dom_pre_inst                      false
% 11.04/2.00  --qbf_sk_in                             false
% 11.04/2.00  --qbf_pred_elim                         true
% 11.04/2.00  --qbf_split                             512
% 11.04/2.00  
% 11.04/2.00  ------ BMC1 Options
% 11.04/2.00  
% 11.04/2.00  --bmc1_incremental                      false
% 11.04/2.00  --bmc1_axioms                           reachable_all
% 11.04/2.00  --bmc1_min_bound                        0
% 11.04/2.00  --bmc1_max_bound                        -1
% 11.04/2.00  --bmc1_max_bound_default                -1
% 11.04/2.00  --bmc1_symbol_reachability              true
% 11.04/2.00  --bmc1_property_lemmas                  false
% 11.04/2.00  --bmc1_k_induction                      false
% 11.04/2.00  --bmc1_non_equiv_states                 false
% 11.04/2.00  --bmc1_deadlock                         false
% 11.04/2.00  --bmc1_ucm                              false
% 11.04/2.00  --bmc1_add_unsat_core                   none
% 11.04/2.00  --bmc1_unsat_core_children              false
% 11.04/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.04/2.00  --bmc1_out_stat                         full
% 11.04/2.00  --bmc1_ground_init                      false
% 11.04/2.00  --bmc1_pre_inst_next_state              false
% 11.04/2.00  --bmc1_pre_inst_state                   false
% 11.04/2.00  --bmc1_pre_inst_reach_state             false
% 11.04/2.00  --bmc1_out_unsat_core                   false
% 11.04/2.00  --bmc1_aig_witness_out                  false
% 11.04/2.00  --bmc1_verbose                          false
% 11.04/2.00  --bmc1_dump_clauses_tptp                false
% 11.04/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.04/2.00  --bmc1_dump_file                        -
% 11.04/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.04/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.04/2.00  --bmc1_ucm_extend_mode                  1
% 11.04/2.00  --bmc1_ucm_init_mode                    2
% 11.04/2.00  --bmc1_ucm_cone_mode                    none
% 11.04/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.04/2.00  --bmc1_ucm_relax_model                  4
% 11.04/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.04/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.04/2.00  --bmc1_ucm_layered_model                none
% 11.04/2.00  --bmc1_ucm_max_lemma_size               10
% 11.04/2.00  
% 11.04/2.00  ------ AIG Options
% 11.04/2.00  
% 11.04/2.00  --aig_mode                              false
% 11.04/2.00  
% 11.04/2.00  ------ Instantiation Options
% 11.04/2.00  
% 11.04/2.00  --instantiation_flag                    false
% 11.04/2.00  --inst_sos_flag                         false
% 11.04/2.00  --inst_sos_phase                        true
% 11.04/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.04/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.04/2.00  --inst_lit_sel_side                     num_symb
% 11.04/2.00  --inst_solver_per_active                1400
% 11.04/2.00  --inst_solver_calls_frac                1.
% 11.04/2.00  --inst_passive_queue_type               priority_queues
% 11.04/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.04/2.00  --inst_passive_queues_freq              [25;2]
% 11.04/2.00  --inst_dismatching                      true
% 11.04/2.00  --inst_eager_unprocessed_to_passive     true
% 11.04/2.00  --inst_prop_sim_given                   true
% 11.04/2.00  --inst_prop_sim_new                     false
% 11.04/2.00  --inst_subs_new                         false
% 11.04/2.00  --inst_eq_res_simp                      false
% 11.04/2.00  --inst_subs_given                       false
% 11.04/2.00  --inst_orphan_elimination               true
% 11.04/2.00  --inst_learning_loop_flag               true
% 11.04/2.00  --inst_learning_start                   3000
% 11.04/2.00  --inst_learning_factor                  2
% 11.04/2.00  --inst_start_prop_sim_after_learn       3
% 11.04/2.00  --inst_sel_renew                        solver
% 11.04/2.00  --inst_lit_activity_flag                true
% 11.04/2.00  --inst_restr_to_given                   false
% 11.04/2.00  --inst_activity_threshold               500
% 11.04/2.00  --inst_out_proof                        true
% 11.04/2.00  
% 11.04/2.00  ------ Resolution Options
% 11.04/2.00  
% 11.04/2.00  --resolution_flag                       false
% 11.04/2.00  --res_lit_sel                           adaptive
% 11.04/2.00  --res_lit_sel_side                      none
% 11.04/2.00  --res_ordering                          kbo
% 11.04/2.00  --res_to_prop_solver                    active
% 11.04/2.00  --res_prop_simpl_new                    false
% 11.04/2.00  --res_prop_simpl_given                  true
% 11.04/2.00  --res_passive_queue_type                priority_queues
% 11.04/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.04/2.00  --res_passive_queues_freq               [15;5]
% 11.04/2.00  --res_forward_subs                      full
% 11.04/2.00  --res_backward_subs                     full
% 11.04/2.00  --res_forward_subs_resolution           true
% 11.04/2.00  --res_backward_subs_resolution          true
% 11.04/2.00  --res_orphan_elimination                true
% 11.04/2.00  --res_time_limit                        2.
% 11.04/2.00  --res_out_proof                         true
% 11.04/2.00  
% 11.04/2.00  ------ Superposition Options
% 11.04/2.00  
% 11.04/2.00  --superposition_flag                    true
% 11.04/2.00  --sup_passive_queue_type                priority_queues
% 11.04/2.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.04/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.04/2.00  --demod_completeness_check              fast
% 11.04/2.00  --demod_use_ground                      true
% 11.04/2.00  --sup_to_prop_solver                    active
% 11.04/2.00  --sup_prop_simpl_new                    false
% 11.04/2.00  --sup_prop_simpl_given                  false
% 11.04/2.00  --sup_fun_splitting                     true
% 11.04/2.00  --sup_smt_interval                      10000
% 11.04/2.00  
% 11.04/2.00  ------ Superposition Simplification Setup
% 11.04/2.00  
% 11.04/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.04/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.04/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.04/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.04/2.00  --sup_full_triv                         [TrivRules]
% 11.04/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.04/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.04/2.00  --sup_immed_triv                        [TrivRules]
% 11.04/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.04/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.04/2.00  --sup_immed_bw_main                     []
% 11.04/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.04/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.04/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.04/2.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.04/2.00  
% 11.04/2.00  ------ Combination Options
% 11.04/2.00  
% 11.04/2.00  --comb_res_mult                         1
% 11.04/2.00  --comb_sup_mult                         1
% 11.04/2.00  --comb_inst_mult                        1000000
% 11.04/2.00  
% 11.04/2.00  ------ Debug Options
% 11.04/2.00  
% 11.04/2.00  --dbg_backtrace                         false
% 11.04/2.00  --dbg_dump_prop_clauses                 false
% 11.04/2.00  --dbg_dump_prop_clauses_file            -
% 11.04/2.00  --dbg_out_stat                          false
% 11.04/2.00  
% 11.04/2.00  
% 11.04/2.00  
% 11.04/2.00  
% 11.04/2.00  ------ Proving...
% 11.04/2.00  
% 11.04/2.00  
% 11.04/2.00  % SZS status Theorem for theBenchmark.p
% 11.04/2.00  
% 11.04/2.00   Resolution empty clause
% 11.04/2.00  
% 11.04/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.04/2.00  
% 11.04/2.00  fof(f1,axiom,(
% 11.04/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f16,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.04/2.00    inference(cnf_transformation,[],[f1])).
% 11.04/2.00  
% 11.04/2.00  fof(f9,axiom,(
% 11.04/2.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f24,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.04/2.00    inference(cnf_transformation,[],[f9])).
% 11.04/2.00  
% 11.04/2.00  fof(f8,axiom,(
% 11.04/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f23,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.04/2.00    inference(cnf_transformation,[],[f8])).
% 11.04/2.00  
% 11.04/2.00  fof(f29,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 11.04/2.00    inference(definition_unfolding,[],[f24,f23])).
% 11.04/2.00  
% 11.04/2.00  fof(f7,axiom,(
% 11.04/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f22,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.04/2.00    inference(cnf_transformation,[],[f7])).
% 11.04/2.00  
% 11.04/2.00  fof(f28,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.04/2.00    inference(definition_unfolding,[],[f22,f23])).
% 11.04/2.00  
% 11.04/2.00  fof(f10,axiom,(
% 11.04/2.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f25,plain,(
% 11.04/2.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.04/2.00    inference(cnf_transformation,[],[f10])).
% 11.04/2.00  
% 11.04/2.00  fof(f3,axiom,(
% 11.04/2.00    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f18,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.04/2.00    inference(cnf_transformation,[],[f3])).
% 11.04/2.00  
% 11.04/2.00  fof(f30,plain,(
% 11.04/2.00    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 11.04/2.00    inference(definition_unfolding,[],[f25,f18])).
% 11.04/2.00  
% 11.04/2.00  fof(f5,axiom,(
% 11.04/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f20,plain,(
% 11.04/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.04/2.00    inference(cnf_transformation,[],[f5])).
% 11.04/2.00  
% 11.04/2.00  fof(f2,axiom,(
% 11.04/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f17,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.04/2.00    inference(cnf_transformation,[],[f2])).
% 11.04/2.00  
% 11.04/2.00  fof(f27,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.04/2.00    inference(definition_unfolding,[],[f17,f23,f23])).
% 11.04/2.00  
% 11.04/2.00  fof(f6,axiom,(
% 11.04/2.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f21,plain,(
% 11.04/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.04/2.00    inference(cnf_transformation,[],[f6])).
% 11.04/2.00  
% 11.04/2.00  fof(f4,axiom,(
% 11.04/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f19,plain,(
% 11.04/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.04/2.00    inference(cnf_transformation,[],[f4])).
% 11.04/2.00  
% 11.04/2.00  fof(f11,conjecture,(
% 11.04/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.04/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.04/2.00  
% 11.04/2.00  fof(f12,negated_conjecture,(
% 11.04/2.00    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.04/2.00    inference(negated_conjecture,[],[f11])).
% 11.04/2.00  
% 11.04/2.00  fof(f13,plain,(
% 11.04/2.00    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.04/2.00    inference(ennf_transformation,[],[f12])).
% 11.04/2.00  
% 11.04/2.00  fof(f14,plain,(
% 11.04/2.00    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.04/2.00    introduced(choice_axiom,[])).
% 11.04/2.00  
% 11.04/2.00  fof(f15,plain,(
% 11.04/2.00    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.04/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 11.04/2.00  
% 11.04/2.00  fof(f26,plain,(
% 11.04/2.00    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.04/2.00    inference(cnf_transformation,[],[f15])).
% 11.04/2.00  
% 11.04/2.00  fof(f31,plain,(
% 11.04/2.00    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 11.04/2.00    inference(definition_unfolding,[],[f26,f18,f23])).
% 11.04/2.00  
% 11.04/2.00  cnf(c_0,plain,
% 11.04/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(cnf_transformation,[],[f16]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_6,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 11.04/2.00      inference(cnf_transformation,[],[f29]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_5,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.04/2.00      inference(cnf_transformation,[],[f28]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.04/2.00      inference(cnf_transformation,[],[f30]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_3,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.04/2.00      inference(cnf_transformation,[],[f20]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_27,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_7,c_3]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_84,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_5,c_27]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_85,plain,
% 11.04/2.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_84,c_6]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_1,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.04/2.00      inference(cnf_transformation,[],[f27]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_131,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_85,c_1]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_140,plain,
% 11.04/2.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_131,c_3]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_4,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.04/2.00      inference(cnf_transformation,[],[f21]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_175,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_140,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_2,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.04/2.00      inference(cnf_transformation,[],[f19]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_176,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_175,c_2]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_203,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_6,c_176]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_66,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_6646,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_203,c_66]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_31,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_27,c_2]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_6868,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_6646,c_31]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_6869,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_6868,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_106,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_52,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_74,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_114,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_106,c_52,c_74]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_188,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_1,c_114]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_306,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_176,c_188]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_312,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_306,c_3]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_275,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_203,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_135,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_85,c_27]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_136,plain,
% 11.04/2.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_135,c_114]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_283,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_275,c_4,c_136]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_721,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_188,c_283]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_758,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X1)) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_721,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_4514,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X2)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_312,c_758]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_16586,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_6869,c_4514]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_618,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_52,c_52,c_114]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_31495,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)),k4_xboole_0(k2_xboole_0(X2,X0),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_16586,c_618]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_213,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_176,c_2]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_215,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_213,c_31]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_386,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_0,c_215]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_173,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_140,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_178,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_173,c_136]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_840,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_386,c_178]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_6668,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_840,c_66]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_6839,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_6668,c_31]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7577,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_6839,c_176]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_232,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_178,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_61,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_4,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_71,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_61,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_236,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_232,c_71,c_136]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_489,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_188,c_236]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7872,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_7577,c_489]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_262,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_4,c_203]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_2210,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_262,c_1]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_76,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_93,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_76,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_1597,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_840,c_2]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_233,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_178,c_2]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_235,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_233,c_31]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_443,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_0,c_235]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_305,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_178,c_188]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_313,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_305,c_3]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_939,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_443,c_313]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_961,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_939,c_443]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_1598,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_1597,c_961]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_2214,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_2210,c_4,c_93,c_1598]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7265,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X3,X2))) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_4,c_2214]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7423,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),X3) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_2214,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7472,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_7423,c_71]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7949,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X0,X2)))) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_7872,c_4,c_7265,c_7472]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_826,plain,
% 11.04/2.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_2,c_386]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_860,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_826,c_386]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_1671,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_176,c_860]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_797,plain,
% 11.04/2.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_0,c_313]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_1729,plain,
% 11.04/2.00      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_1671,c_797]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_711,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_0,c_283]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_1071,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_711,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_1084,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_1071,c_4,c_136]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7593,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X2),k2_xboole_0(X0,X3)) = k1_xboole_0 ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_6839,c_1084]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7614,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,k2_xboole_0(X0,X3)))) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_7593,c_4,c_7265,c_7472]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7950,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_7949,c_71,c_1729,c_7614]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_21171,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X2),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_7950,c_74]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7575,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_6839,c_312]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_7620,plain,
% 11.04/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_7575,c_6839]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_58,plain,
% 11.04/2.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_8073,plain,
% 11.04/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_7620,c_58]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_8095,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.04/2.00      inference(light_normalisation,[status(thm)],[c_8073,c_3,c_176]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_8206,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 11.04/2.00      inference(superposition,[status(thm)],[c_8095,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_8243,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.04/2.00      inference(demodulation,[status(thm)],[c_8206,c_4]) ).
% 11.04/2.00  
% 11.04/2.00  cnf(c_8215,plain,
% 11.04/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_8095,c_1]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8234,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_8215,c_3,c_178]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8907,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_840,c_8234]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8994,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_8907,c_961]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21212,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_21171,c_8243,c_8994]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_31546,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),k4_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_31495,c_21212]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_7407,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_2214,c_860]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_847,plain,
% 11.04/2.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_386,c_283]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6669,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_847,c_66]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6837,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1)) = X0 ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_6669,c_31]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6838,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = X0 ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_6837,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_14012,plain,
% 11.04/2.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),X0) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_6838,c_176]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_67,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_70,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_67,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_922,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_2,c_443]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_202,plain,
% 11.04/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_2,c_176]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_355,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_202,c_2]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_358,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_355,c_31]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_966,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_922,c_358]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6690,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_966,c_66]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6691,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_860,c_66]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6821,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_6691,c_66]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6822,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_6690,c_6821]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8410,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_70,c_6822]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_195,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_114,c_0]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8571,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = X0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_8410,c_195]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_27488,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_14012,c_8571]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_326,plain,
% 11.04/2.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_4,c_202]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_97,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_20707,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0)))),k1_xboole_0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_326,c_97]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8875,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_4,c_8234]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8165,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_966,c_8095]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8266,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_8165,c_8234]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8287,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_4,c_8266]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_9116,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_966,c_8287]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_11508,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_9116,c_8234]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_1696,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_860,c_0]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_11511,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_9116,c_1696]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_11532,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_11511,c_6822]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_11534,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_11508,c_11532]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_20754,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_20707,c_8875,c_11534]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_27555,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_27488,c_3,c_140,c_20754]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8167,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_797,c_8095]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8263,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_8167,c_8095]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_9784,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_8263,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_9824,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_9784,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_27556,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_27555,c_9824]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_31547,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_31546,c_7407,c_8994,c_27556]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8,negated_conjecture,
% 11.04/2.01      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 11.04/2.01      inference(cnf_transformation,[],[f31]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_28,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_42999,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_31547,c_28]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_111,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_212,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_176,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_216,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_212,c_71,c_136]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_425,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_216,c_188]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_439,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_425,c_3]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21679,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1)),X2) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_961,c_439]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_1073,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_711,c_618]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_1082,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_1073,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_1083,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_1082,c_31,c_966]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21683,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)),X3) = k2_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(k2_xboole_0(X2,X0),X3)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_1083,c_439]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_729,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_283,c_188]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_753,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_729,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_754,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_753,c_31]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_3971,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_0,c_754]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21882,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_21683,c_3971]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21886,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_21679,c_21882]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21887,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_21886,c_961]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_837,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_386,c_236]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_5063,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2)) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_1729,c_837]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_432,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_216,c_4]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_436,plain,
% 11.04/2.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k1_xboole_0 ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_432,c_71,c_136]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_3286,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_1729,c_436]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_5211,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_5063,c_71,c_1598,c_3286]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_18616,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X2),X0)) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_5211,c_2214]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_36393,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_18616,c_97]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_36486,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X2),X1),k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_36393,c_8994]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_7427,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_2214,c_1696]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_36487,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_36486,c_7427,c_9824]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8922,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_8234,c_758]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6695,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_313,c_66]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_6817,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_6695,c_1696]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_8983,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_8922,c_71,c_6817]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_24832,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_8983,c_97]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_24913,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_24832,c_8994]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_18595,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_5211,c_74]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_18632,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_18595,c_8994]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_18633,plain,
% 11.04/2.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,X1)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_18632,c_8243]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21616,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X1))) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_1696,c_439]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_764,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_0,c_312]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21630,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X1))) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_764,c_439]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21939,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_21630,c_21882]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_21947,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_21616,c_21939]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_24914,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_24913,c_7427,c_18633,c_21947]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_36488,plain,
% 11.04/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_36487,c_24914]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_41328,plain,
% 11.04/2.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 11.04/2.01      inference(light_normalisation,[status(thm)],[c_21887,c_36488]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_41403,plain,
% 11.04/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k2_xboole_0(X0,X2) ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_111,c_41328]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_43001,plain,
% 11.04/2.01      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 11.04/2.01      inference(demodulation,[status(thm)],[c_42999,c_1696,c_41403]) ).
% 11.04/2.01  
% 11.04/2.01  cnf(c_43648,plain,
% 11.04/2.01      ( $false ),
% 11.04/2.01      inference(superposition,[status(thm)],[c_0,c_43001]) ).
% 11.04/2.01  
% 11.04/2.01  
% 11.04/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.04/2.01  
% 11.04/2.01  ------                               Statistics
% 11.04/2.01  
% 11.04/2.01  ------ General
% 11.04/2.01  
% 11.04/2.01  abstr_ref_over_cycles:                  0
% 11.04/2.01  abstr_ref_under_cycles:                 0
% 11.04/2.01  gc_basic_clause_elim:                   0
% 11.04/2.01  forced_gc_time:                         0
% 11.04/2.01  parsing_time:                           0.009
% 11.04/2.01  unif_index_cands_time:                  0.
% 11.04/2.01  unif_index_add_time:                    0.
% 11.04/2.01  orderings_time:                         0.
% 11.04/2.01  out_proof_time:                         0.009
% 11.04/2.01  total_time:                             1.097
% 11.04/2.01  num_of_symbols:                         38
% 11.04/2.01  num_of_terms:                           60978
% 11.04/2.01  
% 11.04/2.01  ------ Preprocessing
% 11.04/2.01  
% 11.04/2.01  num_of_splits:                          0
% 11.04/2.01  num_of_split_atoms:                     2
% 11.04/2.01  num_of_reused_defs:                     0
% 11.04/2.01  num_eq_ax_congr_red:                    0
% 11.04/2.01  num_of_sem_filtered_clauses:            0
% 11.04/2.01  num_of_subtypes:                        0
% 11.04/2.01  monotx_restored_types:                  0
% 11.04/2.01  sat_num_of_epr_types:                   0
% 11.04/2.01  sat_num_of_non_cyclic_types:            0
% 11.04/2.01  sat_guarded_non_collapsed_types:        0
% 11.04/2.01  num_pure_diseq_elim:                    0
% 11.04/2.01  simp_replaced_by:                       0
% 11.04/2.01  res_preprocessed:                       22
% 11.04/2.01  prep_upred:                             0
% 11.04/2.01  prep_unflattend:                        0
% 11.04/2.01  smt_new_axioms:                         0
% 11.04/2.01  pred_elim_cands:                        0
% 11.04/2.01  pred_elim:                              0
% 11.04/2.01  pred_elim_cl:                           0
% 11.04/2.01  pred_elim_cycles:                       0
% 11.04/2.01  merged_defs:                            0
% 11.04/2.01  merged_defs_ncl:                        0
% 11.04/2.01  bin_hyper_res:                          0
% 11.04/2.01  prep_cycles:                            2
% 11.04/2.01  pred_elim_time:                         0.
% 11.04/2.01  splitting_time:                         0.
% 11.04/2.01  sem_filter_time:                        0.
% 11.04/2.01  monotx_time:                            0.
% 11.04/2.01  subtype_inf_time:                       0.
% 11.04/2.01  
% 11.04/2.01  ------ Problem properties
% 11.04/2.01  
% 11.04/2.01  clauses:                                9
% 11.04/2.01  conjectures:                            1
% 11.04/2.01  epr:                                    0
% 11.04/2.01  horn:                                   9
% 11.04/2.01  ground:                                 1
% 11.04/2.01  unary:                                  9
% 11.04/2.01  binary:                                 0
% 11.04/2.01  lits:                                   9
% 11.04/2.01  lits_eq:                                9
% 11.04/2.01  fd_pure:                                0
% 11.04/2.01  fd_pseudo:                              0
% 11.04/2.01  fd_cond:                                0
% 11.04/2.01  fd_pseudo_cond:                         0
% 11.04/2.01  ac_symbols:                             0
% 11.04/2.01  
% 11.04/2.01  ------ Propositional Solver
% 11.04/2.01  
% 11.04/2.01  prop_solver_calls:                      13
% 11.04/2.01  prop_fast_solver_calls:                 56
% 11.04/2.01  smt_solver_calls:                       0
% 11.04/2.01  smt_fast_solver_calls:                  0
% 11.04/2.01  prop_num_of_clauses:                    318
% 11.04/2.01  prop_preprocess_simplified:             371
% 11.04/2.01  prop_fo_subsumed:                       0
% 11.04/2.01  prop_solver_time:                       0.
% 11.04/2.01  smt_solver_time:                        0.
% 11.04/2.01  smt_fast_solver_time:                   0.
% 11.04/2.01  prop_fast_solver_time:                  0.
% 11.04/2.01  prop_unsat_core_time:                   0.
% 11.04/2.01  
% 11.04/2.01  ------ QBF
% 11.04/2.01  
% 11.04/2.01  qbf_q_res:                              0
% 11.04/2.01  qbf_num_tautologies:                    0
% 11.04/2.01  qbf_prep_cycles:                        0
% 11.04/2.01  
% 11.04/2.01  ------ BMC1
% 11.04/2.01  
% 11.04/2.01  bmc1_current_bound:                     -1
% 11.04/2.01  bmc1_last_solved_bound:                 -1
% 11.04/2.01  bmc1_unsat_core_size:                   -1
% 11.04/2.01  bmc1_unsat_core_parents_size:           -1
% 11.04/2.01  bmc1_merge_next_fun:                    0
% 11.04/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.04/2.01  
% 11.04/2.01  ------ Instantiation
% 11.04/2.01  
% 11.04/2.01  inst_num_of_clauses:                    0
% 11.04/2.01  inst_num_in_passive:                    0
% 11.04/2.01  inst_num_in_active:                     0
% 11.04/2.01  inst_num_in_unprocessed:                0
% 11.04/2.01  inst_num_of_loops:                      0
% 11.04/2.01  inst_num_of_learning_restarts:          0
% 11.04/2.01  inst_num_moves_active_passive:          0
% 11.04/2.01  inst_lit_activity:                      0
% 11.04/2.01  inst_lit_activity_moves:                0
% 11.04/2.01  inst_num_tautologies:                   0
% 11.04/2.01  inst_num_prop_implied:                  0
% 11.04/2.01  inst_num_existing_simplified:           0
% 11.04/2.01  inst_num_eq_res_simplified:             0
% 11.04/2.01  inst_num_child_elim:                    0
% 11.04/2.01  inst_num_of_dismatching_blockings:      0
% 11.04/2.01  inst_num_of_non_proper_insts:           0
% 11.04/2.01  inst_num_of_duplicates:                 0
% 11.04/2.01  inst_inst_num_from_inst_to_res:         0
% 11.04/2.01  inst_dismatching_checking_time:         0.
% 11.04/2.01  
% 11.04/2.01  ------ Resolution
% 11.04/2.01  
% 11.04/2.01  res_num_of_clauses:                     0
% 11.04/2.01  res_num_in_passive:                     0
% 11.04/2.01  res_num_in_active:                      0
% 11.04/2.01  res_num_of_loops:                       24
% 11.04/2.01  res_forward_subset_subsumed:            0
% 11.04/2.01  res_backward_subset_subsumed:           0
% 11.04/2.01  res_forward_subsumed:                   0
% 11.04/2.01  res_backward_subsumed:                  0
% 11.04/2.01  res_forward_subsumption_resolution:     0
% 11.04/2.01  res_backward_subsumption_resolution:    0
% 11.04/2.01  res_clause_to_clause_subsumption:       111700
% 11.04/2.01  res_orphan_elimination:                 0
% 11.04/2.01  res_tautology_del:                      0
% 11.04/2.01  res_num_eq_res_simplified:              0
% 11.04/2.01  res_num_sel_changes:                    0
% 11.04/2.01  res_moves_from_active_to_pass:          0
% 11.04/2.01  
% 11.04/2.01  ------ Superposition
% 11.04/2.01  
% 11.04/2.01  sup_time_total:                         0.
% 11.04/2.01  sup_time_generating:                    0.
% 11.04/2.01  sup_time_sim_full:                      0.
% 11.04/2.01  sup_time_sim_immed:                     0.
% 11.04/2.01  
% 11.04/2.01  sup_num_of_clauses:                     3775
% 11.04/2.01  sup_num_in_active:                      139
% 11.04/2.01  sup_num_in_passive:                     3636
% 11.04/2.01  sup_num_of_loops:                       190
% 11.04/2.01  sup_fw_superposition:                   16355
% 11.04/2.01  sup_bw_superposition:                   13564
% 11.04/2.01  sup_immediate_simplified:               13526
% 11.04/2.01  sup_given_eliminated:                   7
% 11.04/2.01  comparisons_done:                       0
% 11.04/2.01  comparisons_avoided:                    0
% 11.04/2.01  
% 11.04/2.01  ------ Simplifications
% 11.04/2.01  
% 11.04/2.01  
% 11.04/2.01  sim_fw_subset_subsumed:                 0
% 11.04/2.01  sim_bw_subset_subsumed:                 0
% 11.04/2.01  sim_fw_subsumed:                        2249
% 11.04/2.01  sim_bw_subsumed:                        54
% 11.04/2.01  sim_fw_subsumption_res:                 0
% 11.04/2.01  sim_bw_subsumption_res:                 0
% 11.04/2.01  sim_tautology_del:                      0
% 11.04/2.01  sim_eq_tautology_del:                   3851
% 11.04/2.01  sim_eq_res_simp:                        0
% 11.04/2.01  sim_fw_demodulated:                     8494
% 11.04/2.01  sim_bw_demodulated:                     118
% 11.04/2.01  sim_light_normalised:                   4974
% 11.04/2.01  sim_joinable_taut:                      0
% 11.04/2.01  sim_joinable_simp:                      0
% 11.04/2.01  sim_ac_normalised:                      0
% 11.04/2.01  sim_smt_subsumption:                    0
% 11.04/2.01  
%------------------------------------------------------------------------------
