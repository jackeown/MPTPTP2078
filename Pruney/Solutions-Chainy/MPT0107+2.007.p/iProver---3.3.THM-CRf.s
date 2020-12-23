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
% DateTime   : Thu Dec  3 11:25:19 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  198 (80022 expanded)
%              Number of clauses        :  161 (21558 expanded)
%              Number of leaves         :   13 (25494 expanded)
%              Depth                    :   33
%              Number of atoms          :  199 (80023 expanded)
%              Number of equality atoms :  198 (80022 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f17,f27,f27])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f23,f23])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f23,f23])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f25,f27,f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f26,f27,f23])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f28,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f28,f23])).

cnf(c_0,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_159,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_4,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_158,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_162,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_158,c_0])).

cnf(c_222,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_159,c_158,c_162])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_106,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_5])).

cnf(c_471,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_106,c_4])).

cnf(c_472,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_106,c_1])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_489,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_472,c_6])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_39,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_7,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_270,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39,c_7])).

cnf(c_273,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_8,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_30,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8,c_6])).

cnf(c_275,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_273,c_6,c_30])).

cnf(c_279,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_270,c_275])).

cnf(c_72,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_31,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_73,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_72,c_3,c_31])).

cnf(c_280,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_279,c_3,c_73])).

cnf(c_490,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_489,c_280])).

cnf(c_263,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39,c_7])).

cnf(c_292,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_263,c_280])).

cnf(c_67,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_39,c_4])).

cnf(c_46,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_31])).

cnf(c_47,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_46,c_3])).

cnf(c_74,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_67,c_47])).

cnf(c_75,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_74,c_3])).

cnf(c_293,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_292,c_3,c_73,c_75])).

cnf(c_271,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = X0 ),
    inference(superposition,[status(thm)],[c_39,c_7])).

cnf(c_276,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))))) = X0 ),
    inference(demodulation,[status(thm)],[c_271,c_6,c_106])).

cnf(c_277,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_276,c_3])).

cnf(c_175,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_278,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_277,c_175])).

cnf(c_281,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_280,c_278])).

cnf(c_283,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_281,c_175])).

cnf(c_284,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_283,c_3])).

cnf(c_294,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_293,c_284])).

cnf(c_295,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_294,c_293])).

cnf(c_491,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_490,c_3,c_280,c_295])).

cnf(c_492,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_471,c_491])).

cnf(c_493,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_492,c_6,c_280])).

cnf(c_542,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_493,c_2])).

cnf(c_550,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_542,c_106])).

cnf(c_311,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_280,c_6])).

cnf(c_315,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_311,c_106])).

cnf(c_665,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_315,c_106])).

cnf(c_683,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_665,c_3])).

cnf(c_809,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_683,c_6])).

cnf(c_44,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_264,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_7])).

cnf(c_289,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_264,c_106])).

cnf(c_290,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(demodulation,[status(thm)],[c_289,c_6])).

cnf(c_291,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_290,c_106])).

cnf(c_375,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_44,c_291])).

cnf(c_60,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_404,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_375,c_60])).

cnf(c_440,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_404,c_280])).

cnf(c_603,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_440,c_30])).

cnf(c_620,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_603,c_3,c_73])).

cnf(c_833,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_809,c_280,c_293,c_620])).

cnf(c_664,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_315,c_5])).

cnf(c_677,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_664,c_3])).

cnf(c_706,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_677])).

cnf(c_2744,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_833,c_706])).

cnf(c_2746,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2744,c_3])).

cnf(c_33472,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_158,c_2746])).

cnf(c_33482,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_162,c_33472])).

cnf(c_33574,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_550,c_33482])).

cnf(c_33750,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_33574,c_440])).

cnf(c_718,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_677,c_30])).

cnf(c_736,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_718,c_677])).

cnf(c_737,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_736,c_280,c_295])).

cnf(c_889,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_737,c_30])).

cnf(c_892,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_889,c_280])).

cnf(c_893,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_892,c_295])).

cnf(c_3082,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3) ),
    inference(superposition,[status(thm)],[c_893,c_6])).

cnf(c_3084,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X0)),X2)) ),
    inference(superposition,[status(thm)],[c_893,c_30])).

cnf(c_3133,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3)) = k4_xboole_0(X0,k4_xboole_0(X1,X3)) ),
    inference(light_normalisation,[status(thm)],[c_3084,c_30])).

cnf(c_3135,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_3082,c_3133])).

cnf(c_2651,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_440,c_833])).

cnf(c_4769,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2651,c_3])).

cnf(c_4825,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_4769])).

cnf(c_1406,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_106,c_291])).

cnf(c_1440,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1406,c_493])).

cnf(c_16265,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4825,c_1440])).

cnf(c_422,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_60,c_4])).

cnf(c_428,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_422,c_280])).

cnf(c_423,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_60,c_2])).

cnf(c_429,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_428,c_423])).

cnf(c_430,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_429,c_3])).

cnf(c_977,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_430])).

cnf(c_1943,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),X2) ),
    inference(superposition,[status(thm)],[c_977,c_6])).

cnf(c_1979,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_1943,c_4])).

cnf(c_744,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_428])).

cnf(c_888,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_737,c_30])).

cnf(c_894,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_888,c_683])).

cnf(c_895,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_894,c_280,c_295])).

cnf(c_12344,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X2) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_744,c_895])).

cnf(c_12347,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(superposition,[status(thm)],[c_430,c_895])).

cnf(c_2726,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_833,c_491])).

cnf(c_601,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_440,c_6])).

cnf(c_623,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_601,c_3])).

cnf(c_2760,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2726,c_295,c_623])).

cnf(c_5084,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_60,c_2760])).

cnf(c_523,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_493])).

cnf(c_573,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_523,c_6])).

cnf(c_190,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_210,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
    inference(demodulation,[status(thm)],[c_190,c_6])).

cnf(c_466,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ),
    inference(superposition,[status(thm)],[c_106,c_30])).

cnf(c_496,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_466,c_30])).

cnf(c_497,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_496,c_6])).

cnf(c_574,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_573,c_210,c_497])).

cnf(c_12238,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(superposition,[status(thm)],[c_574,c_706])).

cnf(c_883,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X1,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) ),
    inference(superposition,[status(thm)],[c_737,c_106])).

cnf(c_897,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_883,c_3,c_280])).

cnf(c_6598,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_897,c_493])).

cnf(c_3305,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_737,c_2746])).

cnf(c_4888,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_4769,c_30])).

cnf(c_4945,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X3,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
    inference(demodulation,[status(thm)],[c_4888,c_73,c_620])).

cnf(c_4946,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
    inference(demodulation,[status(thm)],[c_4945,c_3])).

cnf(c_6683,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6598,c_3305,c_4946])).

cnf(c_8576,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6683,c_2])).

cnf(c_8639,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_8576,c_3,c_620,c_623,c_895])).

cnf(c_9023,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),X1) = k4_xboole_0(k4_xboole_0(X0,X3),X1) ),
    inference(superposition,[status(thm)],[c_8639,c_2760])).

cnf(c_12255,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_12238,c_3,c_9023])).

cnf(c_12623,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_12347,c_5084,c_12255])).

cnf(c_12625,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_12344,c_12623])).

cnf(c_9040,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_8639,c_897])).

cnf(c_12626,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_12625,c_9040])).

cnf(c_16602,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_16265,c_1979,c_12626])).

cnf(c_33751,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_33750,c_73,c_3135,c_16602])).

cnf(c_33752,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_33751,c_3])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_34579,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_33752,c_9])).

cnf(c_35271,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_222,c_34579])).

cnf(c_33414,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X0)))) ),
    inference(superposition,[status(thm)],[c_158,c_6])).

cnf(c_3017,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_4,c_893])).

cnf(c_3155,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3017,c_893])).

cnf(c_33463,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_158,c_3155])).

cnf(c_1886,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_977])).

cnf(c_2032,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1886,c_744])).

cnf(c_20068,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_2032,c_895])).

cnf(c_20118,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_20068,c_3,c_12623])).

cnf(c_33865,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_33463,c_20118,c_33472,c_33482])).

cnf(c_33977,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_33414,c_33865])).

cnf(c_33978,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_33977,c_440])).

cnf(c_33979,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_33978,c_3])).

cnf(c_33592,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_493,c_33482])).

cnf(c_33730,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_33592,c_295,c_893])).

cnf(c_33877,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_33865,c_33730])).

cnf(c_33982,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_33979,c_33877])).

cnf(c_35273,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_35271,c_33982])).

cnf(c_35274,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_35273])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.81/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.49  
% 7.81/1.49  ------  iProver source info
% 7.81/1.49  
% 7.81/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.49  git: non_committed_changes: false
% 7.81/1.49  git: last_make_outside_of_git: false
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     num_symb
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       true
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     false
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   []
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_full_bw                           [BwDemod]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  ------ Parsing...
% 7.81/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.49  ------ Proving...
% 7.81/1.49  ------ Problem Properties 
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  clauses                                 10
% 7.81/1.49  conjectures                             1
% 7.81/1.49  EPR                                     0
% 7.81/1.49  Horn                                    10
% 7.81/1.49  unary                                   10
% 7.81/1.49  binary                                  0
% 7.81/1.49  lits                                    10
% 7.81/1.49  lits eq                                 10
% 7.81/1.49  fd_pure                                 0
% 7.81/1.49  fd_pseudo                               0
% 7.81/1.49  fd_cond                                 0
% 7.81/1.49  fd_pseudo_cond                          0
% 7.81/1.49  AC symbols                              0
% 7.81/1.49  
% 7.81/1.49  ------ Schedule UEQ
% 7.81/1.49  
% 7.81/1.49  ------ pure equality problem: resolution off 
% 7.81/1.49  
% 7.81/1.49  ------ Option_UEQ Time Limit: Unbounded
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  Current options:
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    --mode clausify
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    false
% 7.81/1.49  --inst_sos_flag                         false
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     num_symb
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       false
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    active
% 7.81/1.49  --sup_prop_simpl_new                    false
% 7.81/1.49  --sup_prop_simpl_given                  false
% 7.81/1.49  --sup_fun_splitting                     true
% 7.81/1.49  --sup_smt_interval                      10000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.81/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         1
% 7.81/1.49  --comb_sup_mult                         1
% 7.81/1.49  --comb_inst_mult                        1000000
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ Proving...
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS status Theorem for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49   Resolution empty clause
% 7.81/1.49  
% 7.81/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  fof(f3,axiom,(
% 7.81/1.49    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f19,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f3])).
% 7.81/1.49  
% 7.81/1.49  fof(f11,axiom,(
% 7.81/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f27,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f11])).
% 7.81/1.49  
% 7.81/1.49  fof(f29,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f19,f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f1,axiom,(
% 7.81/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f17,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f1])).
% 7.81/1.49  
% 7.81/1.49  fof(f30,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f17,f27,f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f5,axiom,(
% 7.81/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f21,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f5])).
% 7.81/1.49  
% 7.81/1.49  fof(f32,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 7.81/1.49    inference(definition_unfolding,[],[f21,f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f2,axiom,(
% 7.81/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f18,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f2])).
% 7.81/1.49  
% 7.81/1.49  fof(f7,axiom,(
% 7.81/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f23,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f7])).
% 7.81/1.49  
% 7.81/1.49  fof(f31,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f18,f23,f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f6,axiom,(
% 7.81/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f22,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f6])).
% 7.81/1.49  
% 7.81/1.49  fof(f33,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f22,f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f8,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f24,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f8])).
% 7.81/1.49  
% 7.81/1.49  fof(f34,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.81/1.49    inference(definition_unfolding,[],[f24,f23,f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f4,axiom,(
% 7.81/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f20,plain,(
% 7.81/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.81/1.49    inference(cnf_transformation,[],[f4])).
% 7.81/1.49  
% 7.81/1.49  fof(f9,axiom,(
% 7.81/1.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f25,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.81/1.49    inference(cnf_transformation,[],[f9])).
% 7.81/1.49  
% 7.81/1.49  fof(f35,plain,(
% 7.81/1.49    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 7.81/1.49    inference(definition_unfolding,[],[f25,f27,f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f10,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f26,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f10])).
% 7.81/1.49  
% 7.81/1.49  fof(f36,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f26,f27,f23])).
% 7.81/1.49  
% 7.81/1.49  fof(f12,conjecture,(
% 7.81/1.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f13,negated_conjecture,(
% 7.81/1.49    ~! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.81/1.49    inference(negated_conjecture,[],[f12])).
% 7.81/1.49  
% 7.81/1.49  fof(f14,plain,(
% 7.81/1.49    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)),
% 7.81/1.49    inference(ennf_transformation,[],[f13])).
% 7.81/1.49  
% 7.81/1.49  fof(f15,plain,(
% 7.81/1.49    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) => k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f16,plain,(
% 7.81/1.49    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 7.81/1.49  
% 7.81/1.49  fof(f28,plain,(
% 7.81/1.49    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 7.81/1.49    inference(cnf_transformation,[],[f16])).
% 7.81/1.49  
% 7.81/1.49  fof(f37,plain,(
% 7.81/1.49    k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1)),
% 7.81/1.49    inference(definition_unfolding,[],[f28,f23])).
% 7.81/1.49  
% 7.81/1.49  cnf(c_0,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_159,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_158,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_162,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_158,c_0]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_222,plain,
% 7.81/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_159,c_158,c_162]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_106,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_2,c_5]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_471,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_106,c_4]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_472,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_106,c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_6,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_489,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_472,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.81/1.49      inference(cnf_transformation,[],[f20]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_39,plain,
% 7.81/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 7.81/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_270,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))) = k1_xboole_0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_39,c_7]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_273,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_30,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_8,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_275,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_273,c_6,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_279,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_270,c_275]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_72,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_31,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_73,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_72,c_3,c_31]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_280,plain,
% 7.81/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_279,c_3,c_73]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_490,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_489,c_280]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_263,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0))) = k1_xboole_0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_39,c_7]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_292,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_263,c_280]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_67,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_39,c_4]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_46,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_2,c_31]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_47,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_46,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_74,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_67,c_47]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_75,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_74,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_293,plain,
% 7.81/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_292,c_3,c_73,c_75]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_271,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = X0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_39,c_7]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_276,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))))) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_271,c_6,c_106]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_277,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))))) = X0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_276,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_175,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_278,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0))))) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_277,c_175]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_281,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_280,c_278]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_283,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_281,c_175]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_284,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_283,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_294,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_293,c_284]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_295,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_294,c_293]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_491,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_490,c_3,c_280,c_295]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_492,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_471,c_491]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_493,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_492,c_6,c_280]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_542,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_493,c_2]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_550,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_542,c_106]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_311,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_280,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_315,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_311,c_106]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_665,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_315,c_106]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_683,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_665,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_809,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X2) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_683,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_44,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_264,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_2,c_7]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_289,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = X0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_264,c_106]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_290,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_289,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_291,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_290,c_106]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_375,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = X0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_44,c_291]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_60,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_404,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_375,c_60]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_440,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_404,c_280]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_603,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_440,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_620,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_603,c_3,c_73]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_833,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_809,c_280,c_293,c_620]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_664,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_315,c_5]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_677,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_664,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_706,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_6,c_677]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2744,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_833,c_706]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2746,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_2744,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_33472,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_158,c_2746]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_33482,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_162,c_33472]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_33574,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_550,c_33482]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_33750,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_33574,c_440]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_718,plain,
% 7.81/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_677,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_736,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_718,c_677]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_737,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_736,c_280,c_295]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_889,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_737,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_892,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_889,c_280]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_893,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_892,c_295]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3082,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_893,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3084,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X0)),X2)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_893,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3133,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X0)),X3)) = k4_xboole_0(X0,k4_xboole_0(X1,X3)) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_3084,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3135,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_3082,c_3133]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2651,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0),k1_xboole_0) = k1_xboole_0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_440,c_833]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4769,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_2651,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_4825,plain,
% 7.81/1.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_4,c_4769]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1406,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_106,c_291]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1440,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_1406,c_493]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_16265,plain,
% 7.81/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_4825,c_1440]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_422,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_60,c_4]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_428,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_422,c_280]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_423,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_60,c_2]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_429,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_428,c_423]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_430,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_429,c_3]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_977,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1,c_430]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1943,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),X2) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_977,c_6]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1979,plain,
% 7.81/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.49      inference(light_normalisation,[status(thm)],[c_1943,c_4]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_744,plain,
% 7.81/1.49      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1,c_428]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_888,plain,
% 7.81/1.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_737,c_30]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_894,plain,
% 7.81/1.50      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_888,c_683]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_895,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_894,c_280,c_295]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_12344,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X2) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k1_xboole_0) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_744,c_895]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_12347,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_430,c_895]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_2726,plain,
% 7.81/1.50      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_833,c_491]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_601,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_440,c_6]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_623,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_601,c_3]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_2760,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_2726,c_295,c_623]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_5084,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_60,c_2760]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_523,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X2) = k1_xboole_0 ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_6,c_493]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_573,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X2))) = k1_xboole_0 ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_523,c_6]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_190,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_210,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_190,c_6]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_466,plain,
% 7.81/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_106,c_30]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_496,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_466,c_30]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_497,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_496,c_6]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_574,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X2))) = k1_xboole_0 ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_573,c_210,c_497]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_12238,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_574,c_706]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_883,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X1,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_737,c_106]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_897,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_883,c_3,c_280]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_6598,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k1_xboole_0 ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_897,c_493]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_3305,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_737,c_2746]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_4888,plain,
% 7.81/1.50      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X3,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_4769,c_30]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_4945,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X3,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_4888,c_73,c_620]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_4946,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X3)) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_4945,c_3]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_6683,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_6598,c_3305,c_4946]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_8576,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X2),X1),k1_xboole_0) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_6683,c_2]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_8639,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_8576,c_3,c_620,c_623,c_895]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_9023,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),X1) = k4_xboole_0(k4_xboole_0(X0,X3),X1) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_8639,c_2760]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_12255,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_12238,c_3,c_9023]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_12623,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_12347,c_5084,c_12255]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_12625,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_12344,c_12623]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_9040,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_8639,c_897]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_12626,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_12625,c_9040]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_16602,plain,
% 7.81/1.50      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_16265,c_1979,c_12626]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33751,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33750,c_73,c_3135,c_16602]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33752,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X1,X0),X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33751,c_3]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_9,negated_conjecture,
% 7.81/1.50      ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
% 7.81/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_34579,plain,
% 7.81/1.50      ( k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1)) != k4_xboole_0(sK0,sK1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33752,c_9]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_35271,plain,
% 7.81/1.50      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) != k4_xboole_0(sK0,sK1) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_222,c_34579]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33414,plain,
% 7.81/1.50      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X0)))) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_158,c_6]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_3017,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_4,c_893]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_3155,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(X0,X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_3017,c_893]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33463,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_158,c_3155]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_1886,plain,
% 7.81/1.50      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_4,c_977]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_2032,plain,
% 7.81/1.50      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_1886,c_744]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_20068,plain,
% 7.81/1.50      ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_2032,c_895]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_20118,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_20068,c_3,c_12623]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33865,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33463,c_20118,c_33472,c_33482]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33977,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33414,c_33865]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33978,plain,
% 7.81/1.50      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) ),
% 7.81/1.50      inference(light_normalisation,[status(thm)],[c_33977,c_440]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33979,plain,
% 7.81/1.50      ( k4_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33978,c_3]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33592,plain,
% 7.81/1.50      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 7.81/1.50      inference(superposition,[status(thm)],[c_493,c_33482]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33730,plain,
% 7.81/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33592,c_295,c_893]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33877,plain,
% 7.81/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33865,c_33730]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_33982,plain,
% 7.81/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_33979,c_33877]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_35273,plain,
% 7.81/1.50      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
% 7.81/1.50      inference(demodulation,[status(thm)],[c_35271,c_33982]) ).
% 7.81/1.50  
% 7.81/1.50  cnf(c_35274,plain,
% 7.81/1.50      ( $false ),
% 7.81/1.50      inference(equality_resolution_simp,[status(thm)],[c_35273]) ).
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.50  
% 7.81/1.50  ------                               Statistics
% 7.81/1.50  
% 7.81/1.50  ------ General
% 7.81/1.50  
% 7.81/1.50  abstr_ref_over_cycles:                  0
% 7.81/1.50  abstr_ref_under_cycles:                 0
% 7.81/1.50  gc_basic_clause_elim:                   0
% 7.81/1.50  forced_gc_time:                         0
% 7.81/1.50  parsing_time:                           0.009
% 7.81/1.50  unif_index_cands_time:                  0.
% 7.81/1.50  unif_index_add_time:                    0.
% 7.81/1.50  orderings_time:                         0.
% 7.81/1.50  out_proof_time:                         0.011
% 7.81/1.50  total_time:                             0.931
% 7.81/1.50  num_of_symbols:                         39
% 7.81/1.50  num_of_terms:                           52856
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing
% 7.81/1.50  
% 7.81/1.50  num_of_splits:                          0
% 7.81/1.50  num_of_split_atoms:                     3
% 7.81/1.50  num_of_reused_defs:                     3
% 7.81/1.50  num_eq_ax_congr_red:                    0
% 7.81/1.50  num_of_sem_filtered_clauses:            0
% 7.81/1.50  num_of_subtypes:                        0
% 7.81/1.50  monotx_restored_types:                  0
% 7.81/1.50  sat_num_of_epr_types:                   0
% 7.81/1.50  sat_num_of_non_cyclic_types:            0
% 7.81/1.50  sat_guarded_non_collapsed_types:        0
% 7.81/1.50  num_pure_diseq_elim:                    0
% 7.81/1.50  simp_replaced_by:                       0
% 7.81/1.50  res_preprocessed:                       24
% 7.81/1.50  prep_upred:                             0
% 7.81/1.50  prep_unflattend:                        0
% 7.81/1.50  smt_new_axioms:                         0
% 7.81/1.50  pred_elim_cands:                        0
% 7.81/1.50  pred_elim:                              0
% 7.81/1.50  pred_elim_cl:                           0
% 7.81/1.50  pred_elim_cycles:                       0
% 7.81/1.50  merged_defs:                            0
% 7.81/1.50  merged_defs_ncl:                        0
% 7.81/1.50  bin_hyper_res:                          0
% 7.81/1.50  prep_cycles:                            2
% 7.81/1.50  pred_elim_time:                         0.
% 7.81/1.50  splitting_time:                         0.
% 7.81/1.50  sem_filter_time:                        0.
% 7.81/1.50  monotx_time:                            0.
% 7.81/1.50  subtype_inf_time:                       0.
% 7.81/1.50  
% 7.81/1.50  ------ Problem properties
% 7.81/1.50  
% 7.81/1.50  clauses:                                10
% 7.81/1.50  conjectures:                            1
% 7.81/1.50  epr:                                    0
% 7.81/1.50  horn:                                   10
% 7.81/1.50  ground:                                 1
% 7.81/1.50  unary:                                  10
% 7.81/1.50  binary:                                 0
% 7.81/1.50  lits:                                   10
% 7.81/1.50  lits_eq:                                10
% 7.81/1.50  fd_pure:                                0
% 7.81/1.50  fd_pseudo:                              0
% 7.81/1.50  fd_cond:                                0
% 7.81/1.50  fd_pseudo_cond:                         0
% 7.81/1.50  ac_symbols:                             0
% 7.81/1.50  
% 7.81/1.50  ------ Propositional Solver
% 7.81/1.50  
% 7.81/1.50  prop_solver_calls:                      13
% 7.81/1.50  prop_fast_solver_calls:                 60
% 7.81/1.50  smt_solver_calls:                       0
% 7.81/1.50  smt_fast_solver_calls:                  0
% 7.81/1.50  prop_num_of_clauses:                    234
% 7.81/1.50  prop_preprocess_simplified:             363
% 7.81/1.50  prop_fo_subsumed:                       0
% 7.81/1.50  prop_solver_time:                       0.
% 7.81/1.50  smt_solver_time:                        0.
% 7.81/1.50  smt_fast_solver_time:                   0.
% 7.81/1.50  prop_fast_solver_time:                  0.
% 7.81/1.50  prop_unsat_core_time:                   0.
% 7.81/1.50  
% 7.81/1.50  ------ QBF
% 7.81/1.50  
% 7.81/1.50  qbf_q_res:                              0
% 7.81/1.50  qbf_num_tautologies:                    0
% 7.81/1.50  qbf_prep_cycles:                        0
% 7.81/1.50  
% 7.81/1.50  ------ BMC1
% 7.81/1.50  
% 7.81/1.50  bmc1_current_bound:                     -1
% 7.81/1.50  bmc1_last_solved_bound:                 -1
% 7.81/1.50  bmc1_unsat_core_size:                   -1
% 7.81/1.50  bmc1_unsat_core_parents_size:           -1
% 7.81/1.50  bmc1_merge_next_fun:                    0
% 7.81/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.50  
% 7.81/1.50  ------ Instantiation
% 7.81/1.50  
% 7.81/1.50  inst_num_of_clauses:                    0
% 7.81/1.50  inst_num_in_passive:                    0
% 7.81/1.50  inst_num_in_active:                     0
% 7.81/1.50  inst_num_in_unprocessed:                0
% 7.81/1.50  inst_num_of_loops:                      0
% 7.81/1.50  inst_num_of_learning_restarts:          0
% 7.81/1.50  inst_num_moves_active_passive:          0
% 7.81/1.50  inst_lit_activity:                      0
% 7.81/1.50  inst_lit_activity_moves:                0
% 7.81/1.50  inst_num_tautologies:                   0
% 7.81/1.50  inst_num_prop_implied:                  0
% 7.81/1.50  inst_num_existing_simplified:           0
% 7.81/1.50  inst_num_eq_res_simplified:             0
% 7.81/1.50  inst_num_child_elim:                    0
% 7.81/1.50  inst_num_of_dismatching_blockings:      0
% 7.81/1.50  inst_num_of_non_proper_insts:           0
% 7.81/1.50  inst_num_of_duplicates:                 0
% 7.81/1.50  inst_inst_num_from_inst_to_res:         0
% 7.81/1.50  inst_dismatching_checking_time:         0.
% 7.81/1.50  
% 7.81/1.50  ------ Resolution
% 7.81/1.50  
% 7.81/1.50  res_num_of_clauses:                     0
% 7.81/1.50  res_num_in_passive:                     0
% 7.81/1.50  res_num_in_active:                      0
% 7.81/1.50  res_num_of_loops:                       26
% 7.81/1.50  res_forward_subset_subsumed:            0
% 7.81/1.50  res_backward_subset_subsumed:           0
% 7.81/1.50  res_forward_subsumed:                   0
% 7.81/1.50  res_backward_subsumed:                  0
% 7.81/1.50  res_forward_subsumption_resolution:     0
% 7.81/1.50  res_backward_subsumption_resolution:    0
% 7.81/1.50  res_clause_to_clause_subsumption:       78733
% 7.81/1.50  res_orphan_elimination:                 0
% 7.81/1.50  res_tautology_del:                      0
% 7.81/1.50  res_num_eq_res_simplified:              0
% 7.81/1.50  res_num_sel_changes:                    0
% 7.81/1.50  res_moves_from_active_to_pass:          0
% 7.81/1.50  
% 7.81/1.50  ------ Superposition
% 7.81/1.50  
% 7.81/1.50  sup_time_total:                         0.
% 7.81/1.50  sup_time_generating:                    0.
% 7.81/1.50  sup_time_sim_full:                      0.
% 7.81/1.50  sup_time_sim_immed:                     0.
% 7.81/1.50  
% 7.81/1.50  sup_num_of_clauses:                     2525
% 7.81/1.50  sup_num_in_active:                      111
% 7.81/1.50  sup_num_in_passive:                     2414
% 7.81/1.50  sup_num_of_loops:                       128
% 7.81/1.50  sup_fw_superposition:                   11548
% 7.81/1.50  sup_bw_superposition:                   8856
% 7.81/1.50  sup_immediate_simplified:               11829
% 7.81/1.50  sup_given_eliminated:                   5
% 7.81/1.50  comparisons_done:                       0
% 7.81/1.50  comparisons_avoided:                    0
% 7.81/1.50  
% 7.81/1.50  ------ Simplifications
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  sim_fw_subset_subsumed:                 0
% 7.81/1.50  sim_bw_subset_subsumed:                 0
% 7.81/1.50  sim_fw_subsumed:                        1068
% 7.81/1.50  sim_bw_subsumed:                        22
% 7.81/1.50  sim_fw_subsumption_res:                 0
% 7.81/1.50  sim_bw_subsumption_res:                 0
% 7.81/1.50  sim_tautology_del:                      0
% 7.81/1.50  sim_eq_tautology_del:                   4822
% 7.81/1.50  sim_eq_res_simp:                        0
% 7.81/1.50  sim_fw_demodulated:                     9185
% 7.81/1.50  sim_bw_demodulated:                     211
% 7.81/1.50  sim_light_normalised:                   5347
% 7.81/1.50  sim_joinable_taut:                      0
% 7.81/1.50  sim_joinable_simp:                      0
% 7.81/1.50  sim_ac_normalised:                      0
% 7.81/1.50  sim_smt_subsumption:                    0
% 7.81/1.50  
%------------------------------------------------------------------------------
