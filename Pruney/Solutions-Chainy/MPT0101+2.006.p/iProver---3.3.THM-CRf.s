%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:58 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  165 (5885 expanded)
%              Number of clauses        :  124 (2248 expanded)
%              Number of leaves         :   16 (1658 expanded)
%              Depth                    :   21
%              Number of atoms          :  166 (5886 expanded)
%              Number of equality atoms :  165 (5885 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f30,f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f30,f30])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f23,f30,f30])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

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

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f34,f22,f22,f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_36,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_9,c_6])).

cnf(c_59,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1),X2)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_5,c_36])).

cnf(c_351,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_4,c_59])).

cnf(c_503,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_351,c_5])).

cnf(c_44,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_45,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_44,c_4])).

cnf(c_345,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0),X1)) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_59])).

cnf(c_42,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_224,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_42,c_1])).

cnf(c_11,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_78,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_11,c_5])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_35,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_79,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_78,c_35])).

cnf(c_231,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_224,c_4,c_79])).

cnf(c_228,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0),X1)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_42,c_36])).

cnf(c_232,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_231,c_228])).

cnf(c_402,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_345,c_232])).

cnf(c_504,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_503,c_4,c_45,c_402])).

cnf(c_65,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_35,c_36])).

cnf(c_71,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_65,c_4,c_35])).

cnf(c_189,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_79])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_36,c_36])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_67,c_35])).

cnf(c_47,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_45])).

cnf(c_69,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_68,c_47])).

cnf(c_1180,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_189,c_69])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_550,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_35,c_10])).

cnf(c_586,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_550,c_4])).

cnf(c_1297,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1180,c_4,c_586])).

cnf(c_1319,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_71,c_1297])).

cnf(c_118,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_35])).

cnf(c_2,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_223,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_42,c_6])).

cnf(c_233,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_223,c_6])).

cnf(c_614,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_2,c_2,c_233])).

cnf(c_633,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_118,c_614])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_668,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_633,c_4,c_8])).

cnf(c_944,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_189,c_504])).

cnf(c_75,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_975,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_944,c_75])).

cnf(c_1361,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1319,c_668,c_975])).

cnf(c_2908,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_504,c_1361])).

cnf(c_1181,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_118,c_69])).

cnf(c_1293,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1181,c_4])).

cnf(c_91,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1,c_36])).

cnf(c_94,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_91,c_35])).

cnf(c_95,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_94,c_47])).

cnf(c_548,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_549,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X3)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_36,c_10])).

cnf(c_587,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_549,c_10])).

cnf(c_588,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_548,c_10,c_587])).

cnf(c_1294,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1293,c_95,c_586,c_588])).

cnf(c_1557,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_1294])).

cnf(c_2977,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2908,c_1557])).

cnf(c_1339,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1297,c_6])).

cnf(c_6173,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_2977,c_1339])).

cnf(c_1344,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1297,c_10])).

cnf(c_1352,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1344,c_35])).

cnf(c_1353,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1352,c_45])).

cnf(c_6323,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_6173,c_1353])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_37,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_12,c_6])).

cnf(c_38,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_37,c_11])).

cnf(c_40,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_38])).

cnf(c_24471,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6323,c_40])).

cnf(c_1763,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_668,c_975])).

cnf(c_1811,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1763,c_975])).

cnf(c_3181,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_1811])).

cnf(c_525,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_10])).

cnf(c_54,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_47,c_5])).

cnf(c_57,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_54,c_35])).

cnf(c_612,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_525,c_4,c_57])).

cnf(c_992,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_612])).

cnf(c_1049,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_992,c_95])).

cnf(c_3267,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_3181,c_10,c_1049])).

cnf(c_1776,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_975,c_6])).

cnf(c_1799,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_1776,c_47])).

cnf(c_13746,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_1799,c_2977])).

cnf(c_211,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_189,c_6])).

cnf(c_109,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_124,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_109,c_6])).

cnf(c_215,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_211,c_57,c_124])).

cnf(c_788,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_215])).

cnf(c_1513,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_668,c_788])).

cnf(c_1368,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_668])).

cnf(c_1438,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1368,c_1294])).

cnf(c_10773,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X2,X1),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1513,c_1438])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_724,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),X1) ),
    inference(superposition,[status(thm)],[c_231,c_7])).

cnf(c_10813,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10773,c_724])).

cnf(c_1084,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1049,c_189])).

cnf(c_1149,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1084,c_7])).

cnf(c_1158,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1149,c_45])).

cnf(c_6888,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(k4_xboole_0(X0,X1),X3) ),
    inference(superposition,[status(thm)],[c_1158,c_6])).

cnf(c_1083,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1049,c_215])).

cnf(c_1939,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X3)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1083,c_7])).

cnf(c_1943,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_1939,c_45])).

cnf(c_6938,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_6888,c_1943])).

cnf(c_10054,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_788,c_1438])).

cnf(c_434,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_452,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_466,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_434,c_452])).

cnf(c_10176,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_10054,c_466])).

cnf(c_10177,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_10176,c_4,c_1811])).

cnf(c_10814,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),k4_xboole_0(X2,k2_xboole_0(X0,k1_xboole_0)))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_10813,c_6938,c_10177])).

cnf(c_10815,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_10814,c_45])).

cnf(c_213,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_189,c_6])).

cnf(c_10036,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_213,c_1438])).

cnf(c_6906,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1158,c_7])).

cnf(c_6925,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_6906,c_452])).

cnf(c_10213,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_10036,c_4,c_1811,c_6925])).

cnf(c_10816,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_10815,c_1811,c_10213])).

cnf(c_13833,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_13746,c_2977,c_10816])).

cnf(c_24472,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_24471,c_1811,c_3267,c_13833])).

cnf(c_24806,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_0,c_24472])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:26:01 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.77/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.48  
% 7.77/1.48  ------  iProver source info
% 7.77/1.48  
% 7.77/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.48  git: non_committed_changes: false
% 7.77/1.48  git: last_make_outside_of_git: false
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    --mode clausify
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         false
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     num_symb
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       true
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     false
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   []
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_full_bw                           [BwDemod]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  ------ Parsing...
% 7.77/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.77/1.48  ------ Proving...
% 7.77/1.48  ------ Problem Properties 
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  clauses                                 13
% 7.77/1.48  conjectures                             1
% 7.77/1.48  EPR                                     0
% 7.77/1.48  Horn                                    13
% 7.77/1.48  unary                                   13
% 7.77/1.48  binary                                  0
% 7.77/1.48  lits                                    13
% 7.77/1.48  lits eq                                 13
% 7.77/1.48  fd_pure                                 0
% 7.77/1.48  fd_pseudo                               0
% 7.77/1.48  fd_cond                                 0
% 7.77/1.48  fd_pseudo_cond                          0
% 7.77/1.48  AC symbols                              0
% 7.77/1.48  
% 7.77/1.48  ------ Schedule UEQ
% 7.77/1.48  
% 7.77/1.48  ------ pure equality problem: resolution off 
% 7.77/1.48  
% 7.77/1.48  ------ Option_UEQ Time Limit: Unbounded
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  Current options:
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    --mode clausify
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    false
% 7.77/1.48  --inst_sos_flag                         false
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     num_symb
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       false
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    active
% 7.77/1.48  --sup_prop_simpl_new                    false
% 7.77/1.48  --sup_prop_simpl_given                  false
% 7.77/1.48  --sup_fun_splitting                     true
% 7.77/1.48  --sup_smt_interval                      10000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         1
% 7.77/1.48  --comb_sup_mult                         1
% 7.77/1.48  --comb_inst_mult                        1000000
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ Proving...
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS status Theorem for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48   Resolution empty clause
% 7.77/1.48  
% 7.77/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  fof(f1,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f20,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f1])).
% 7.77/1.48  
% 7.77/1.48  fof(f6,axiom,(
% 7.77/1.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f25,plain,(
% 7.77/1.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.77/1.48    inference(cnf_transformation,[],[f6])).
% 7.77/1.48  
% 7.77/1.48  fof(f7,axiom,(
% 7.77/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f26,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f7])).
% 7.77/1.48  
% 7.77/1.48  fof(f12,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f31,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f12])).
% 7.77/1.48  
% 7.77/1.48  fof(f11,axiom,(
% 7.77/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f30,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f11])).
% 7.77/1.48  
% 7.77/1.48  fof(f39,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f31,f30,f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f8,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f27,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f8])).
% 7.77/1.48  
% 7.77/1.48  fof(f2,axiom,(
% 7.77/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f21,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f2])).
% 7.77/1.48  
% 7.77/1.48  fof(f35,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f21,f30,f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f14,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f33,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f14])).
% 7.77/1.48  
% 7.77/1.48  fof(f5,axiom,(
% 7.77/1.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f24,plain,(
% 7.77/1.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.77/1.48    inference(cnf_transformation,[],[f5])).
% 7.77/1.48  
% 7.77/1.48  fof(f37,plain,(
% 7.77/1.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.77/1.48    inference(definition_unfolding,[],[f24,f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f13,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f32,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f13])).
% 7.77/1.48  
% 7.77/1.48  fof(f40,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f32,f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f4,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f23,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f4])).
% 7.77/1.48  
% 7.77/1.48  fof(f36,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f23,f30,f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f10,axiom,(
% 7.77/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f29,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f10])).
% 7.77/1.48  
% 7.77/1.48  fof(f38,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f29,f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f15,conjecture,(
% 7.77/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f16,negated_conjecture,(
% 7.77/1.48    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.77/1.48    inference(negated_conjecture,[],[f15])).
% 7.77/1.48  
% 7.77/1.48  fof(f17,plain,(
% 7.77/1.48    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.77/1.48    inference(ennf_transformation,[],[f16])).
% 7.77/1.48  
% 7.77/1.48  fof(f18,plain,(
% 7.77/1.48    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f19,plain,(
% 7.77/1.48    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 7.77/1.48  
% 7.77/1.48  fof(f34,plain,(
% 7.77/1.48    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.77/1.48    inference(cnf_transformation,[],[f19])).
% 7.77/1.48  
% 7.77/1.48  fof(f3,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f22,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f3])).
% 7.77/1.48  
% 7.77/1.48  fof(f41,plain,(
% 7.77/1.48    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 7.77/1.48    inference(definition_unfolding,[],[f34,f22,f22,f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f9,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f28,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f9])).
% 7.77/1.48  
% 7.77/1.48  cnf(c_0,plain,
% 7.77/1.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f20]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.77/1.48      inference(cnf_transformation,[],[f25]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_5,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f26]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_9,plain,
% 7.77/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6,plain,
% 7.77/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f27]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_36,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_9,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_59,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1),X2)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_5,c_36]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_351,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_4,c_59]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_503,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_351,c_5]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_44,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_45,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_44,c_4]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_345,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0),X1)) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_0,c_59]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_42,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_224,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_42,c_1]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_11,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_78,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_11,c_5]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.77/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_35,plain,
% 7.77/1.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_79,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_78,c_35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_231,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_224,c_4,c_79]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_228,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0),X1)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_42,c_36]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_232,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0),X1)) = k4_xboole_0(X0,X1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_231,c_228]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_402,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_345,c_232]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_504,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_503,c_4,c_45,c_402]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_65,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_35,c_36]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_71,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_65,c_4,c_35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_189,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_0,c_79]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_67,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_36,c_36]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_68,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_67,c_35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_47,plain,
% 7.77/1.48      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_0,c_45]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_69,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_68,c_47]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1180,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_189,c_69]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_550,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_35,c_10]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_586,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_550,c_4]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1297,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_1180,c_4,c_586]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1319,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_71,c_1297]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_118,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_6,c_35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_223,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_42,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_233,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_223,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_614,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_2,c_2,c_233]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_633,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_118,c_614]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_8,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_668,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_633,c_4,c_8]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_944,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_189,c_504]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_75,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_975,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_944,c_75]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1361,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_1319,c_668,c_975]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2908,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_504,c_1361]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1181,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_118,c_69]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1293,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_1181,c_4]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_91,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1,c_36]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_94,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_91,c_35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_95,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_94,c_47]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_548,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_549,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X3)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_36,c_10]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_587,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X3))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_549,c_10]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_588,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_548,c_10,c_587]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1294,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_1293,c_95,c_586,c_588]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1557,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_5,c_1294]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2977,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_2908,c_1557]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1339,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1297,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6173,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_2977,c_1339]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1344,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1297,c_10]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1352,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_1344,c_35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1353,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_1352,c_45]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6323,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_6173,c_1353]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_12,negated_conjecture,
% 7.77/1.48      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_37,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_12,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_38,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_37,c_11]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_40,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_0,c_38]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_24471,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_6323,c_40]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1763,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_668,c_975]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1811,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_1763,c_975]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3181,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_8,c_1811]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_525,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_4,c_10]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_54,plain,
% 7.77/1.48      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_47,c_5]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_57,plain,
% 7.77/1.48      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_54,c_35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_612,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_525,c_4,c_57]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_992,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1,c_612]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1049,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_992,c_95]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3267,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_3181,c_10,c_1049]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1776,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_975,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1799,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_1776,c_47]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_13746,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1799,c_2977]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_211,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_189,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_109,plain,
% 7.77/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_124,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_109,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_215,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_211,c_57,c_124]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_788,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_0,c_215]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1513,plain,
% 7.77/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_668,c_788]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1368,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1,c_668]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1438,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_1368,c_1294]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10773,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X2,X1),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1513,c_1438]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_7,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f28]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_724,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),X1) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_231,c_7]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10813,plain,
% 7.77/1.48      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_10773,c_724]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1084,plain,
% 7.77/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1049,c_189]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1149,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1084,c_7]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1158,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_1149,c_45]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6888,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(k4_xboole_0(X0,X1),X3) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1158,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1083,plain,
% 7.77/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1049,c_215]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1939,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X3)),k1_xboole_0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1083,c_7]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1943,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_1939,c_45]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6938,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_6888,c_1943]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10054,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_788,c_1438]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_434,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_452,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_466,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_434,c_452]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10176,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_10054,c_466]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10177,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_10176,c_4,c_1811]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10814,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),k4_xboole_0(X2,k2_xboole_0(X0,k1_xboole_0)))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_10813,c_6938,c_10177]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10815,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_10814,c_45]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_213,plain,
% 7.77/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_189,c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10036,plain,
% 7.77/1.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_213,c_1438]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6906,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1158,c_7]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6925,plain,
% 7.77/1.48      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_6906,c_452]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10213,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_10036,c_4,c_1811,c_6925]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10816,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_10815,c_1811,c_10213]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_13833,plain,
% 7.77/1.48      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_13746,c_2977,c_10816]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_24472,plain,
% 7.77/1.48      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_24471,c_1811,c_3267,c_13833]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_24806,plain,
% 7.77/1.48      ( $false ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_0,c_24472]) ).
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  ------                               Statistics
% 7.77/1.48  
% 7.77/1.48  ------ General
% 7.77/1.48  
% 7.77/1.48  abstr_ref_over_cycles:                  0
% 7.77/1.48  abstr_ref_under_cycles:                 0
% 7.77/1.48  gc_basic_clause_elim:                   0
% 7.77/1.48  forced_gc_time:                         0
% 7.77/1.48  parsing_time:                           0.013
% 7.77/1.48  unif_index_cands_time:                  0.
% 7.77/1.48  unif_index_add_time:                    0.
% 7.77/1.48  orderings_time:                         0.
% 7.77/1.48  out_proof_time:                         0.01
% 7.77/1.48  total_time:                             0.795
% 7.77/1.48  num_of_symbols:                         38
% 7.77/1.48  num_of_terms:                           48637
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing
% 7.77/1.48  
% 7.77/1.48  num_of_splits:                          0
% 7.77/1.48  num_of_split_atoms:                     2
% 7.77/1.48  num_of_reused_defs:                     0
% 7.77/1.48  num_eq_ax_congr_red:                    0
% 7.77/1.48  num_of_sem_filtered_clauses:            0
% 7.77/1.48  num_of_subtypes:                        0
% 7.77/1.48  monotx_restored_types:                  0
% 7.77/1.48  sat_num_of_epr_types:                   0
% 7.77/1.48  sat_num_of_non_cyclic_types:            0
% 7.77/1.48  sat_guarded_non_collapsed_types:        0
% 7.77/1.48  num_pure_diseq_elim:                    0
% 7.77/1.48  simp_replaced_by:                       0
% 7.77/1.48  res_preprocessed:                       30
% 7.77/1.48  prep_upred:                             0
% 7.77/1.48  prep_unflattend:                        0
% 7.77/1.48  smt_new_axioms:                         0
% 7.77/1.48  pred_elim_cands:                        0
% 7.77/1.48  pred_elim:                              0
% 7.77/1.48  pred_elim_cl:                           0
% 7.77/1.48  pred_elim_cycles:                       0
% 7.77/1.48  merged_defs:                            0
% 7.77/1.48  merged_defs_ncl:                        0
% 7.77/1.48  bin_hyper_res:                          0
% 7.77/1.48  prep_cycles:                            2
% 7.77/1.48  pred_elim_time:                         0.
% 7.77/1.48  splitting_time:                         0.
% 7.77/1.48  sem_filter_time:                        0.
% 7.77/1.48  monotx_time:                            0.
% 7.77/1.48  subtype_inf_time:                       0.
% 7.77/1.48  
% 7.77/1.48  ------ Problem properties
% 7.77/1.48  
% 7.77/1.48  clauses:                                13
% 7.77/1.48  conjectures:                            1
% 7.77/1.48  epr:                                    0
% 7.77/1.48  horn:                                   13
% 7.77/1.48  ground:                                 1
% 7.77/1.48  unary:                                  13
% 7.77/1.48  binary:                                 0
% 7.77/1.48  lits:                                   13
% 7.77/1.48  lits_eq:                                13
% 7.77/1.48  fd_pure:                                0
% 7.77/1.48  fd_pseudo:                              0
% 7.77/1.48  fd_cond:                                0
% 7.77/1.48  fd_pseudo_cond:                         0
% 7.77/1.48  ac_symbols:                             0
% 7.77/1.48  
% 7.77/1.48  ------ Propositional Solver
% 7.77/1.48  
% 7.77/1.48  prop_solver_calls:                      13
% 7.77/1.48  prop_fast_solver_calls:                 72
% 7.77/1.48  smt_solver_calls:                       0
% 7.77/1.48  smt_fast_solver_calls:                  0
% 7.77/1.48  prop_num_of_clauses:                    233
% 7.77/1.48  prop_preprocess_simplified:             459
% 7.77/1.48  prop_fo_subsumed:                       0
% 7.77/1.48  prop_solver_time:                       0.
% 7.77/1.48  smt_solver_time:                        0.
% 7.77/1.48  smt_fast_solver_time:                   0.
% 7.77/1.48  prop_fast_solver_time:                  0.
% 7.77/1.48  prop_unsat_core_time:                   0.
% 7.77/1.48  
% 7.77/1.48  ------ QBF
% 7.77/1.48  
% 7.77/1.48  qbf_q_res:                              0
% 7.77/1.48  qbf_num_tautologies:                    0
% 7.77/1.48  qbf_prep_cycles:                        0
% 7.77/1.48  
% 7.77/1.48  ------ BMC1
% 7.77/1.48  
% 7.77/1.48  bmc1_current_bound:                     -1
% 7.77/1.48  bmc1_last_solved_bound:                 -1
% 7.77/1.48  bmc1_unsat_core_size:                   -1
% 7.77/1.48  bmc1_unsat_core_parents_size:           -1
% 7.77/1.48  bmc1_merge_next_fun:                    0
% 7.77/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation
% 7.77/1.48  
% 7.77/1.48  inst_num_of_clauses:                    0
% 7.77/1.48  inst_num_in_passive:                    0
% 7.77/1.48  inst_num_in_active:                     0
% 7.77/1.48  inst_num_in_unprocessed:                0
% 7.77/1.48  inst_num_of_loops:                      0
% 7.77/1.48  inst_num_of_learning_restarts:          0
% 7.77/1.48  inst_num_moves_active_passive:          0
% 7.77/1.48  inst_lit_activity:                      0
% 7.77/1.48  inst_lit_activity_moves:                0
% 7.77/1.48  inst_num_tautologies:                   0
% 7.77/1.48  inst_num_prop_implied:                  0
% 7.77/1.48  inst_num_existing_simplified:           0
% 7.77/1.48  inst_num_eq_res_simplified:             0
% 7.77/1.48  inst_num_child_elim:                    0
% 7.77/1.48  inst_num_of_dismatching_blockings:      0
% 7.77/1.48  inst_num_of_non_proper_insts:           0
% 7.77/1.48  inst_num_of_duplicates:                 0
% 7.77/1.48  inst_inst_num_from_inst_to_res:         0
% 7.77/1.48  inst_dismatching_checking_time:         0.
% 7.77/1.48  
% 7.77/1.48  ------ Resolution
% 7.77/1.48  
% 7.77/1.48  res_num_of_clauses:                     0
% 7.77/1.48  res_num_in_passive:                     0
% 7.77/1.48  res_num_in_active:                      0
% 7.77/1.48  res_num_of_loops:                       32
% 7.77/1.48  res_forward_subset_subsumed:            0
% 7.77/1.48  res_backward_subset_subsumed:           0
% 7.77/1.48  res_forward_subsumed:                   0
% 7.77/1.48  res_backward_subsumed:                  0
% 7.77/1.48  res_forward_subsumption_resolution:     0
% 7.77/1.48  res_backward_subsumption_resolution:    0
% 7.77/1.48  res_clause_to_clause_subsumption:       55916
% 7.77/1.48  res_orphan_elimination:                 0
% 7.77/1.48  res_tautology_del:                      0
% 7.77/1.48  res_num_eq_res_simplified:              0
% 7.77/1.48  res_num_sel_changes:                    0
% 7.77/1.48  res_moves_from_active_to_pass:          0
% 7.77/1.48  
% 7.77/1.48  ------ Superposition
% 7.77/1.48  
% 7.77/1.48  sup_time_total:                         0.
% 7.77/1.48  sup_time_generating:                    0.
% 7.77/1.48  sup_time_sim_full:                      0.
% 7.77/1.48  sup_time_sim_immed:                     0.
% 7.77/1.48  
% 7.77/1.48  sup_num_of_clauses:                     2647
% 7.77/1.48  sup_num_in_active:                      117
% 7.77/1.48  sup_num_in_passive:                     2530
% 7.77/1.48  sup_num_of_loops:                       131
% 7.77/1.48  sup_fw_superposition:                   8293
% 7.77/1.48  sup_bw_superposition:                   6743
% 7.77/1.48  sup_immediate_simplified:               7952
% 7.77/1.48  sup_given_eliminated:                   5
% 7.77/1.48  comparisons_done:                       0
% 7.77/1.48  comparisons_avoided:                    0
% 7.77/1.48  
% 7.77/1.48  ------ Simplifications
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  sim_fw_subset_subsumed:                 0
% 7.77/1.48  sim_bw_subset_subsumed:                 0
% 7.77/1.48  sim_fw_subsumed:                        1023
% 7.77/1.48  sim_bw_subsumed:                        24
% 7.77/1.48  sim_fw_subsumption_res:                 0
% 7.77/1.48  sim_bw_subsumption_res:                 0
% 7.77/1.48  sim_tautology_del:                      0
% 7.77/1.48  sim_eq_tautology_del:                   2404
% 7.77/1.48  sim_eq_res_simp:                        0
% 7.77/1.48  sim_fw_demodulated:                     5868
% 7.77/1.48  sim_bw_demodulated:                     129
% 7.77/1.48  sim_light_normalised:                   3655
% 7.77/1.48  sim_joinable_taut:                      0
% 7.77/1.48  sim_joinable_simp:                      0
% 7.77/1.48  sim_ac_normalised:                      0
% 7.77/1.48  sim_smt_subsumption:                    0
% 7.77/1.48  
%------------------------------------------------------------------------------
