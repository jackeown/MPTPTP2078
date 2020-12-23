%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:15 EST 2020

% Result     : Theorem 47.69s
% Output     : CNFRefutation 47.69s
% Verified   : 
% Statistics : Number of formulae       :  415 (32463871 expanded)
%              Number of clauses        :  378 (9671780 expanded)
%              Number of leaves         :   13 (9314966 expanded)
%              Depth                    :   70
%              Number of atoms          :  416 (32463872 expanded)
%              Number of equality atoms :  415 (32463871 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f21,f31,f31])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f20,f31,f25])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f23,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f19,f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f17,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f30,f31])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_162,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_34,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_35,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_34,c_3])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_85,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_35,c_4])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_36,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_35,c_1])).

cnf(c_105,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_85,c_36])).

cnf(c_252,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_105])).

cnf(c_274,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_252,c_0])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_107,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_37044,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_274,c_107])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_59,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_120,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_35,c_0])).

cnf(c_140,plain,
    ( k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_120,c_36])).

cnf(c_467,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_59,c_59,c_140])).

cnf(c_492,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_467,c_5])).

cnf(c_1993,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_274,c_492])).

cnf(c_125,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_138,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_125,c_7])).

cnf(c_141,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_140,c_138])).

cnf(c_50,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_36])).

cnf(c_142,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_141,c_50])).

cnf(c_2073,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1993,c_140,c_142])).

cnf(c_164,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_166,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_164,c_4])).

cnf(c_56,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_1035,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) ),
    inference(superposition,[status(thm)],[c_166,c_56])).

cnf(c_1040,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1035,c_5])).

cnf(c_2371,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2073,c_1040])).

cnf(c_2435,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2371,c_2073])).

cnf(c_3875,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_0,c_2435])).

cnf(c_3993,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3875,c_0])).

cnf(c_3994,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3993,c_4])).

cnf(c_1028,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_166,c_140])).

cnf(c_5892,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3994,c_1028])).

cnf(c_5967,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5892,c_3994])).

cnf(c_46,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_237,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_46,c_8])).

cnf(c_247,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_237,c_8])).

cnf(c_1126,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_247,c_8])).

cnf(c_1172,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_1126,c_247])).

cnf(c_48,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_36])).

cnf(c_1134,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_247,c_48])).

cnf(c_1164,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_1134,c_247])).

cnf(c_1176,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_1172,c_1164])).

cnf(c_370,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_48,c_46])).

cnf(c_371,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_370,c_46])).

cnf(c_717,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_371])).

cnf(c_1182,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1176,c_717])).

cnf(c_1317,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_1126,c_46,c_1182])).

cnf(c_5968,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_5967,c_140,c_1317])).

cnf(c_37434,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_37044,c_5968])).

cnf(c_47,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_36,c_8])).

cnf(c_187,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_50,c_4])).

cnf(c_189,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_187,c_50,c_140,c_142])).

cnf(c_1460,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_274,c_189])).

cnf(c_1480,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1460,c_274])).

cnf(c_1481,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1480,c_1028])).

cnf(c_1482,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1481,c_6])).

cnf(c_12911,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0))))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_47,c_1482])).

cnf(c_13229,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_12911,c_47])).

cnf(c_1998,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),X1)) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_47,c_492])).

cnf(c_13230,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13229,c_1998])).

cnf(c_2378,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2073,c_166])).

cnf(c_2433,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2378,c_2073])).

cnf(c_253,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_140,c_105])).

cnf(c_273,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_253,c_140])).

cnf(c_1002,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),X1) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_273,c_166])).

cnf(c_1058,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1002,c_273])).

cnf(c_6849,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1058,c_492])).

cnf(c_6857,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_6849,c_492])).

cnf(c_13231,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13230,c_2433,c_6857])).

cnf(c_13434,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_13231])).

cnf(c_13531,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_13434,c_8])).

cnf(c_13465,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_13231,c_0])).

cnf(c_13494,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_13465,c_5968])).

cnf(c_1112,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_247,c_8])).

cnf(c_1374,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_1112,c_46,c_1182])).

cnf(c_13495,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_13494,c_1317,c_1374])).

cnf(c_13496,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_13495,c_1317])).

cnf(c_218,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_142])).

cnf(c_184,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_50])).

cnf(c_2282,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_184,c_8])).

cnf(c_13497,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13496,c_47,c_218,c_2282])).

cnf(c_13711,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_13497])).

cnf(c_13907,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_13711,c_8])).

cnf(c_37435,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_37434,c_13531,c_13907])).

cnf(c_501,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X1))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_467,c_467])).

cnf(c_504,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_501,c_7,c_467])).

cnf(c_2030,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_492,c_166])).

cnf(c_260,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_105,c_5])).

cnf(c_266,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_260,c_105])).

cnf(c_267,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_266,c_166])).

cnf(c_2036,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2030,c_267,c_1028])).

cnf(c_2652,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2073,c_2036])).

cnf(c_2711,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2652,c_2073])).

cnf(c_2766,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),X1) ),
    inference(superposition,[status(thm)],[c_2711,c_166])).

cnf(c_2830,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2766,c_2711])).

cnf(c_11683,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k4_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_504,c_2830])).

cnf(c_2381,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2073,c_0])).

cnf(c_496,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k5_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_467,c_2])).

cnf(c_507,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_496,c_3,c_7,c_50,c_140,c_273])).

cnf(c_2429,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2381,c_140,c_142,c_507])).

cnf(c_186,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_50,c_8])).

cnf(c_2469,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2429,c_186])).

cnf(c_2471,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2469,c_50])).

cnf(c_2462,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2429,c_8])).

cnf(c_3119,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2471,c_2462])).

cnf(c_472,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X0) ),
    inference(superposition,[status(thm)],[c_140,c_467])).

cnf(c_477,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))),X0) = k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_273,c_467])).

cnf(c_318,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_47,c_142])).

cnf(c_523,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_477,c_47,c_318])).

cnf(c_527,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_472,c_523])).

cnf(c_528,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_527,c_142])).

cnf(c_3185,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3119,c_528,c_2429])).

cnf(c_81,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_4])).

cnf(c_7826,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) = k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_3185,c_81])).

cnf(c_8098,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7826,c_3])).

cnf(c_263,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_105,c_6])).

cnf(c_4839,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_263,c_5])).

cnf(c_4912,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_4839,c_5])).

cnf(c_8139,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_8098,c_4912])).

cnf(c_8276,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8139,c_8098])).

cnf(c_22015,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_140,c_8276])).

cnf(c_1685,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1182,c_142])).

cnf(c_1756,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_1685,c_46,c_218])).

cnf(c_8216,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_8098,c_1756])).

cnf(c_22408,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_22015,c_140,c_8216])).

cnf(c_22536,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_22408,c_6])).

cnf(c_22696,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_22536,c_142])).

cnf(c_42160,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_22696,c_5])).

cnf(c_1019,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_166,c_105])).

cnf(c_1048,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1019,c_166])).

cnf(c_82994,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2435,c_1048])).

cnf(c_83846,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_82994,c_2435])).

cnf(c_84143,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) = k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1) ),
    inference(superposition,[status(thm)],[c_42160,c_83846])).

cnf(c_11706,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_467,c_2830])).

cnf(c_768,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_528,c_142])).

cnf(c_1539,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_768,c_166])).

cnf(c_1563,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_1539,c_768])).

cnf(c_11893,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_11706,c_6,c_492,c_1563])).

cnf(c_84485,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_84143,c_11893])).

cnf(c_27929,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ),
    inference(superposition,[status(thm)],[c_11893,c_166])).

cnf(c_751,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_4,c_528])).

cnf(c_785,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_751,c_4])).

cnf(c_39517,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ),
    inference(superposition,[status(thm)],[c_785,c_504])).

cnf(c_39584,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_39517,c_785])).

cnf(c_84486,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_84485,c_7,c_27929,c_39584])).

cnf(c_88022,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0)),X1) ),
    inference(superposition,[status(thm)],[c_11683,c_84486])).

cnf(c_27892,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_11893,c_140])).

cnf(c_27917,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_11893,c_5])).

cnf(c_28059,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_27917,c_11893])).

cnf(c_28060,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))))))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_28059,c_11893])).

cnf(c_2771,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_2711,c_6])).

cnf(c_2823,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2771,c_140])).

cnf(c_491,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_467,c_6])).

cnf(c_2824,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_2823,c_6,c_467,c_491])).

cnf(c_16449,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_2824,c_492])).

cnf(c_16466,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_16449,c_492])).

cnf(c_28061,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_28060,c_16466])).

cnf(c_64,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_75,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
    inference(demodulation,[status(thm)],[c_64,c_6])).

cnf(c_6106,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
    inference(superposition,[status(thm)],[c_3,c_75])).

cnf(c_6116,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
    inference(superposition,[status(thm)],[c_142,c_75])).

cnf(c_6128,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
    inference(superposition,[status(thm)],[c_2711,c_75])).

cnf(c_500,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,X2))))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_467,c_6])).

cnf(c_505,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))))))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
    inference(demodulation,[status(thm)],[c_500,c_6])).

cnf(c_6640,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
    inference(demodulation,[status(thm)],[c_6128,c_6,c_505])).

cnf(c_6641,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_6640,c_1028])).

cnf(c_6642,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) ),
    inference(demodulation,[status(thm)],[c_6641,c_6])).

cnf(c_6675,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) ),
    inference(demodulation,[status(thm)],[c_6116,c_6642])).

cnf(c_6676,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) ),
    inference(demodulation,[status(thm)],[c_6675,c_492,c_505])).

cnf(c_6677,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),X2) ),
    inference(demodulation,[status(thm)],[c_6676,c_1028])).

cnf(c_6678,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ),
    inference(demodulation,[status(thm)],[c_6677,c_6])).

cnf(c_6682,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ),
    inference(demodulation,[status(thm)],[c_6678,c_6642])).

cnf(c_6689,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ),
    inference(demodulation,[status(thm)],[c_6106,c_6682])).

cnf(c_28062,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_28061,c_6689,c_16466])).

cnf(c_28103,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_27892,c_28062])).

cnf(c_28104,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_28103,c_140])).

cnf(c_28105,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_28104,c_528])).

cnf(c_48635,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_28105,c_2824])).

cnf(c_48641,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_48635,c_7,c_504])).

cnf(c_88604,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_88022,c_48641])).

cnf(c_42015,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) ),
    inference(superposition,[status(thm)],[c_4912,c_22696])).

cnf(c_43052,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_42015,c_5,c_42160])).

cnf(c_554,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_507,c_8])).

cnf(c_44596,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)),k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0))))) = k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_43052,c_554])).

cnf(c_44677,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)),X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_44596,c_3,c_7,c_1028,c_11683,c_13497])).

cnf(c_92,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3) ),
    inference(demodulation,[status(thm)],[c_92,c_6])).

cnf(c_30978,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1))),X2) ),
    inference(superposition,[status(thm)],[c_140,c_102])).

cnf(c_30988,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))),X2) ),
    inference(superposition,[status(thm)],[c_166,c_102])).

cnf(c_206,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_140,c_6])).

cnf(c_31728,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))),X2) ),
    inference(demodulation,[status(thm)],[c_30988,c_206,c_1317])).

cnf(c_31729,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))),X2) ),
    inference(demodulation,[status(thm)],[c_31728,c_13497])).

cnf(c_31745,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))))) = k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)),X2)) ),
    inference(demodulation,[status(thm)],[c_30978,c_31729])).

cnf(c_1941,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_267,c_6])).

cnf(c_31746,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),X2)) ),
    inference(demodulation,[status(thm)],[c_31745,c_267,c_1941])).

cnf(c_1003,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_142,c_166])).

cnf(c_1057,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1003,c_142])).

cnf(c_31747,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),X2)) ),
    inference(demodulation,[status(thm)],[c_31746,c_1057])).

cnf(c_261,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(superposition,[status(thm)],[c_105,c_4])).

cnf(c_265,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(demodulation,[status(thm)],[c_261,c_166])).

cnf(c_31748,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(demodulation,[status(thm)],[c_31747,c_166,c_265])).

cnf(c_44678,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_44677,c_8098,c_31748])).

cnf(c_44679,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_44678,c_3])).

cnf(c_44680,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_44679,c_7,c_2462])).

cnf(c_1433,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_274])).

cnf(c_45118,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) ),
    inference(superposition,[status(thm)],[c_44680,c_1433])).

cnf(c_45236,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_45118,c_44680])).

cnf(c_45787,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_45236,c_6])).

cnf(c_67481,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) ),
    inference(superposition,[status(thm)],[c_4912,c_45787])).

cnf(c_42002,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) ),
    inference(superposition,[status(thm)],[c_5,c_22696])).

cnf(c_43068,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_42002,c_5,c_42160])).

cnf(c_67794,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k1_xboole_0,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_45787,c_43068])).

cnf(c_67823,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k1_xboole_0,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_67794,c_42160])).

cnf(c_67824,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)),X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_67823,c_46])).

cnf(c_67825,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_67824,c_8098])).

cnf(c_69025,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_67481,c_5,c_67825])).

cnf(c_74487,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X1),X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1)))),X2) ),
    inference(superposition,[status(thm)],[c_69025,c_102])).

cnf(c_74852,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X1),X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_74487,c_69025])).

cnf(c_2638,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_273,c_2036])).

cnf(c_2723,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_2638,c_273])).

cnf(c_4029,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))),k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2723,c_0])).

cnf(c_4044,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4029,c_318])).

cnf(c_4045,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_4044,c_1317])).

cnf(c_4046,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0)))),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_4045,c_1317])).

cnf(c_4047,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4046,c_318,c_554])).

cnf(c_5248,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_4047,c_8])).

cnf(c_24062,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_5248,c_8])).

cnf(c_24116,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_24062,c_2462])).

cnf(c_25491,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_24116,c_8])).

cnf(c_25768,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_25491,c_24116])).

cnf(c_67642,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_45787,c_6])).

cnf(c_74853,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_74852,c_140,c_24116,c_25768,c_67642])).

cnf(c_74854,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),X2)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_74853,c_140,c_67642])).

cnf(c_8152,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_8098,c_105])).

cnf(c_8264,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8152,c_8098])).

cnf(c_8923,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2723,c_8264])).

cnf(c_9037,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_8923,c_2723])).

cnf(c_126,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_13696,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_13497])).

cnf(c_28235,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(superposition,[status(thm)],[c_8,c_13696])).

cnf(c_406,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_186,c_8])).

cnf(c_420,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_406,c_8])).

cnf(c_6354,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_420,c_1182])).

cnf(c_6356,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)),X3)) ),
    inference(superposition,[status(thm)],[c_420,c_420])).

cnf(c_6385,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_6356,c_420])).

cnf(c_6386,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_6385,c_186,c_1374])).

cnf(c_6396,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_6354,c_6386])).

cnf(c_6397,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X2) ),
    inference(light_normalisation,[status(thm)],[c_6396,c_8])).

cnf(c_28272,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_6397,c_13696])).

cnf(c_28615,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_28272,c_46])).

cnf(c_28669,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_28235,c_28615])).

cnf(c_49133,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(demodulation,[status(thm)],[c_126,c_1374,c_28669])).

cnf(c_49134,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(demodulation,[status(thm)],[c_49133,c_28669])).

cnf(c_49135,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)))))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(demodulation,[status(thm)],[c_49134,c_28669])).

cnf(c_49273,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
    inference(superposition,[status(thm)],[c_9037,c_49135])).

cnf(c_8915,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_2036,c_8264])).

cnf(c_9045,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8915,c_2036])).

cnf(c_48966,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_48641,c_9045])).

cnf(c_50203,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
    inference(light_normalisation,[status(thm)],[c_49273,c_48966])).

cnf(c_13774,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_13497,c_2462])).

cnf(c_13790,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_13774,c_528,c_2462])).

cnf(c_13973,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_13790,c_8])).

cnf(c_14080,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_13973,c_8])).

cnf(c_50204,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))))) ),
    inference(demodulation,[status(thm)],[c_50203,c_14080,c_28669])).

cnf(c_50205,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
    inference(demodulation,[status(thm)],[c_50204,c_46,c_14080])).

cnf(c_50206,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
    inference(demodulation,[status(thm)],[c_50205,c_46,c_1998])).

cnf(c_2641,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_189,c_2036])).

cnf(c_2721,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2641,c_189])).

cnf(c_11479,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2723,c_2721])).

cnf(c_11595,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_11479,c_528,c_2723])).

cnf(c_48630,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_28105,c_504])).

cnf(c_48664,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X1)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_48630,c_504])).

cnf(c_50207,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),X1),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_50206,c_50,c_8098,c_11595,c_48664])).

cnf(c_322,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_47,c_8])).

cnf(c_34570,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) ),
    inference(superposition,[status(thm)],[c_11683,c_0])).

cnf(c_34592,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) ),
    inference(superposition,[status(thm)],[c_11683,c_2])).

cnf(c_34778,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))) ),
    inference(demodulation,[status(thm)],[c_34592,c_1374,c_24116])).

cnf(c_34803,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_34570,c_34778])).

cnf(c_50208,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_50207,c_273,c_322,c_24116,c_34803])).

cnf(c_70804,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,X1))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_50208,c_2462])).

cnf(c_70819,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_70804,c_2462])).

cnf(c_74855,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_74854,c_140,c_1998,c_13497,c_70819])).

cnf(c_88605,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_88604,c_3,c_166,c_11683,c_74855])).

cnf(c_48934,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_48641,c_1040])).

cnf(c_49084,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_48934,c_48641])).

cnf(c_88606,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_88605,c_49084])).

cnf(c_725,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_371,c_8])).

cnf(c_10177,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_725,c_725,c_1182])).

cnf(c_91845,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10177,c_88606])).

cnf(c_345,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_46,c_48])).

cnf(c_5641,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_345,c_8])).

cnf(c_5653,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5641,c_1182])).

cnf(c_48912,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_48641,c_8276])).

cnf(c_49112,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_48912,c_48641])).

cnf(c_1466,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_274,c_467])).

cnf(c_1467,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_1466,c_140,c_1182])).

cnf(c_1468,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_1467,c_46])).

cnf(c_49113,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_49112,c_1468])).

cnf(c_92420,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_91845,c_5653,c_49113])).

cnf(c_92421,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_92420,c_8098])).

cnf(c_93883,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0),X1) ),
    inference(superposition,[status(thm)],[c_92421,c_4])).

cnf(c_13447,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_13231,c_8264])).

cnf(c_13516,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13447,c_13231])).

cnf(c_2593,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2471,c_8])).

cnf(c_3569,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_2471,c_2593])).

cnf(c_3641,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3569,c_2471])).

cnf(c_3642,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_3641,c_528])).

cnf(c_4945,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) ),
    inference(superposition,[status(thm)],[c_3642,c_4])).

cnf(c_4973,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) ),
    inference(demodulation,[status(thm)],[c_4945,c_467])).

cnf(c_1006,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_318,c_166])).

cnf(c_1054,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1006,c_318])).

cnf(c_4974,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_4973,c_1054])).

cnf(c_4975,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4974,c_3,c_50])).

cnf(c_34991,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)))))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_13516,c_4975])).

cnf(c_35139,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)))))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_34991,c_13516])).

cnf(c_1679,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1182,c_318])).

cnf(c_1763,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_1679,c_1182])).

cnf(c_691,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_318])).

cnf(c_1764,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_1763,c_46,c_140,c_691])).

cnf(c_35140,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_35139,c_1764])).

cnf(c_35141,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_35140,c_8098,c_28105])).

cnf(c_53571,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_35141,c_0])).

cnf(c_53667,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_53571,c_5968])).

cnf(c_53668,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_53667,c_1317])).

cnf(c_53669,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) ),
    inference(demodulation,[status(thm)],[c_53668,c_13531,c_13907])).

cnf(c_3155,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_2462,c_2462])).

cnf(c_3156,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3155,c_2462])).

cnf(c_13781,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_13497,c_3156])).

cnf(c_13785,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_13781,c_3156])).

cnf(c_13786,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13785,c_528])).

cnf(c_53670,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_53669,c_13786])).

cnf(c_91888,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_53670,c_88606])).

cnf(c_8326,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_528,c_504])).

cnf(c_8462,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_8326,c_528])).

cnf(c_92363,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_91888,c_8462,c_48641])).

cnf(c_93956,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_93883,c_37435,c_92363])).

cnf(c_93957,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_93956,c_81])).

cnf(c_94834,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_88606,c_93957])).

cnf(c_94969,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_93957,c_1040])).

cnf(c_95107,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_94969,c_93957])).

cnf(c_95266,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_94834,c_95107])).

cnf(c_95267,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_95266,c_92421])).

cnf(c_34522,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_528,c_11683])).

cnf(c_34858,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(demodulation,[status(thm)],[c_34522,c_528])).

cnf(c_95387,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(demodulation,[status(thm)],[c_95267,c_34858])).

cnf(c_104641,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_95387,c_467])).

cnf(c_104918,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_104641,c_467])).

cnf(c_118935,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_104918,c_50208])).

cnf(c_118953,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_118935,c_50,c_1317])).

cnf(c_125240,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),X0),k5_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) ),
    inference(superposition,[status(thm)],[c_118953,c_1482])).

cnf(c_125310,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),X0),k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_125240,c_118953])).

cnf(c_256,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_6,c_105])).

cnf(c_270,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_256,c_6])).

cnf(c_104626,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))),k5_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_95387,c_270])).

cnf(c_104940,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))),k5_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(demodulation,[status(thm)],[c_104626,c_95387])).

cnf(c_104941,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X1),k5_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_104940,c_467])).

cnf(c_118936,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_104918,c_11683])).

cnf(c_125311,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X1)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_125310,c_5,c_104941,c_118936])).

cnf(c_125696,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_2,c_125311])).

cnf(c_5931,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1028,c_36])).

cnf(c_32868,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_270,c_5931])).

cnf(c_126255,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_125696,c_2,c_32868,c_37435])).

cnf(c_133957,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_162,c_162,c_37435,c_126255])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_43,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_8,c_9])).

cnf(c_133958,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_133957,c_43])).

cnf(c_133965,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_133958])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:32:36 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 47.69/6.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.69/6.48  
% 47.69/6.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.69/6.48  
% 47.69/6.48  ------  iProver source info
% 47.69/6.48  
% 47.69/6.48  git: date: 2020-06-30 10:37:57 +0100
% 47.69/6.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.69/6.48  git: non_committed_changes: false
% 47.69/6.48  git: last_make_outside_of_git: false
% 47.69/6.48  
% 47.69/6.48  ------ 
% 47.69/6.48  
% 47.69/6.48  ------ Input Options
% 47.69/6.48  
% 47.69/6.48  --out_options                           all
% 47.69/6.48  --tptp_safe_out                         true
% 47.69/6.48  --problem_path                          ""
% 47.69/6.48  --include_path                          ""
% 47.69/6.48  --clausifier                            res/vclausify_rel
% 47.69/6.48  --clausifier_options                    --mode clausify
% 47.69/6.48  --stdin                                 false
% 47.69/6.48  --stats_out                             all
% 47.69/6.48  
% 47.69/6.48  ------ General Options
% 47.69/6.48  
% 47.69/6.48  --fof                                   false
% 47.69/6.48  --time_out_real                         305.
% 47.69/6.48  --time_out_virtual                      -1.
% 47.69/6.48  --symbol_type_check                     false
% 47.69/6.48  --clausify_out                          false
% 47.69/6.48  --sig_cnt_out                           false
% 47.69/6.48  --trig_cnt_out                          false
% 47.69/6.48  --trig_cnt_out_tolerance                1.
% 47.69/6.48  --trig_cnt_out_sk_spl                   false
% 47.69/6.48  --abstr_cl_out                          false
% 47.69/6.48  
% 47.69/6.48  ------ Global Options
% 47.69/6.48  
% 47.69/6.48  --schedule                              default
% 47.69/6.48  --add_important_lit                     false
% 47.69/6.48  --prop_solver_per_cl                    1000
% 47.69/6.48  --min_unsat_core                        false
% 47.69/6.48  --soft_assumptions                      false
% 47.69/6.48  --soft_lemma_size                       3
% 47.69/6.48  --prop_impl_unit_size                   0
% 47.69/6.48  --prop_impl_unit                        []
% 47.69/6.48  --share_sel_clauses                     true
% 47.69/6.48  --reset_solvers                         false
% 47.69/6.48  --bc_imp_inh                            [conj_cone]
% 47.69/6.48  --conj_cone_tolerance                   3.
% 47.69/6.48  --extra_neg_conj                        none
% 47.69/6.48  --large_theory_mode                     true
% 47.69/6.48  --prolific_symb_bound                   200
% 47.69/6.48  --lt_threshold                          2000
% 47.69/6.48  --clause_weak_htbl                      true
% 47.69/6.48  --gc_record_bc_elim                     false
% 47.69/6.48  
% 47.69/6.48  ------ Preprocessing Options
% 47.69/6.48  
% 47.69/6.48  --preprocessing_flag                    true
% 47.69/6.48  --time_out_prep_mult                    0.1
% 47.69/6.48  --splitting_mode                        input
% 47.69/6.48  --splitting_grd                         true
% 47.69/6.48  --splitting_cvd                         false
% 47.69/6.48  --splitting_cvd_svl                     false
% 47.69/6.48  --splitting_nvd                         32
% 47.69/6.48  --sub_typing                            true
% 47.69/6.48  --prep_gs_sim                           true
% 47.69/6.48  --prep_unflatten                        true
% 47.69/6.48  --prep_res_sim                          true
% 47.69/6.48  --prep_upred                            true
% 47.69/6.48  --prep_sem_filter                       exhaustive
% 47.69/6.48  --prep_sem_filter_out                   false
% 47.69/6.48  --pred_elim                             true
% 47.69/6.48  --res_sim_input                         true
% 47.69/6.48  --eq_ax_congr_red                       true
% 47.69/6.48  --pure_diseq_elim                       true
% 47.69/6.48  --brand_transform                       false
% 47.69/6.48  --non_eq_to_eq                          false
% 47.69/6.48  --prep_def_merge                        true
% 47.69/6.48  --prep_def_merge_prop_impl              false
% 47.69/6.48  --prep_def_merge_mbd                    true
% 47.69/6.48  --prep_def_merge_tr_red                 false
% 47.69/6.48  --prep_def_merge_tr_cl                  false
% 47.69/6.48  --smt_preprocessing                     true
% 47.69/6.48  --smt_ac_axioms                         fast
% 47.69/6.48  --preprocessed_out                      false
% 47.69/6.48  --preprocessed_stats                    false
% 47.69/6.48  
% 47.69/6.48  ------ Abstraction refinement Options
% 47.69/6.48  
% 47.69/6.48  --abstr_ref                             []
% 47.69/6.48  --abstr_ref_prep                        false
% 47.69/6.48  --abstr_ref_until_sat                   false
% 47.69/6.48  --abstr_ref_sig_restrict                funpre
% 47.69/6.48  --abstr_ref_af_restrict_to_split_sk     false
% 47.69/6.48  --abstr_ref_under                       []
% 47.69/6.48  
% 47.69/6.48  ------ SAT Options
% 47.69/6.48  
% 47.69/6.48  --sat_mode                              false
% 47.69/6.48  --sat_fm_restart_options                ""
% 47.69/6.48  --sat_gr_def                            false
% 47.69/6.48  --sat_epr_types                         true
% 47.69/6.48  --sat_non_cyclic_types                  false
% 47.69/6.48  --sat_finite_models                     false
% 47.69/6.48  --sat_fm_lemmas                         false
% 47.69/6.48  --sat_fm_prep                           false
% 47.69/6.48  --sat_fm_uc_incr                        true
% 47.69/6.48  --sat_out_model                         small
% 47.69/6.48  --sat_out_clauses                       false
% 47.69/6.48  
% 47.69/6.48  ------ QBF Options
% 47.69/6.48  
% 47.69/6.48  --qbf_mode                              false
% 47.69/6.48  --qbf_elim_univ                         false
% 47.69/6.48  --qbf_dom_inst                          none
% 47.69/6.48  --qbf_dom_pre_inst                      false
% 47.69/6.48  --qbf_sk_in                             false
% 47.69/6.48  --qbf_pred_elim                         true
% 47.69/6.48  --qbf_split                             512
% 47.69/6.48  
% 47.69/6.48  ------ BMC1 Options
% 47.69/6.48  
% 47.69/6.48  --bmc1_incremental                      false
% 47.69/6.48  --bmc1_axioms                           reachable_all
% 47.69/6.48  --bmc1_min_bound                        0
% 47.69/6.48  --bmc1_max_bound                        -1
% 47.69/6.48  --bmc1_max_bound_default                -1
% 47.69/6.48  --bmc1_symbol_reachability              true
% 47.69/6.48  --bmc1_property_lemmas                  false
% 47.69/6.48  --bmc1_k_induction                      false
% 47.69/6.48  --bmc1_non_equiv_states                 false
% 47.69/6.48  --bmc1_deadlock                         false
% 47.69/6.48  --bmc1_ucm                              false
% 47.69/6.48  --bmc1_add_unsat_core                   none
% 47.69/6.48  --bmc1_unsat_core_children              false
% 47.69/6.48  --bmc1_unsat_core_extrapolate_axioms    false
% 47.69/6.48  --bmc1_out_stat                         full
% 47.69/6.48  --bmc1_ground_init                      false
% 47.69/6.48  --bmc1_pre_inst_next_state              false
% 47.69/6.48  --bmc1_pre_inst_state                   false
% 47.69/6.48  --bmc1_pre_inst_reach_state             false
% 47.69/6.48  --bmc1_out_unsat_core                   false
% 47.69/6.48  --bmc1_aig_witness_out                  false
% 47.69/6.48  --bmc1_verbose                          false
% 47.69/6.48  --bmc1_dump_clauses_tptp                false
% 47.69/6.48  --bmc1_dump_unsat_core_tptp             false
% 47.69/6.48  --bmc1_dump_file                        -
% 47.69/6.48  --bmc1_ucm_expand_uc_limit              128
% 47.69/6.48  --bmc1_ucm_n_expand_iterations          6
% 47.69/6.48  --bmc1_ucm_extend_mode                  1
% 47.69/6.48  --bmc1_ucm_init_mode                    2
% 47.69/6.48  --bmc1_ucm_cone_mode                    none
% 47.69/6.48  --bmc1_ucm_reduced_relation_type        0
% 47.69/6.48  --bmc1_ucm_relax_model                  4
% 47.69/6.48  --bmc1_ucm_full_tr_after_sat            true
% 47.69/6.48  --bmc1_ucm_expand_neg_assumptions       false
% 47.69/6.48  --bmc1_ucm_layered_model                none
% 47.69/6.48  --bmc1_ucm_max_lemma_size               10
% 47.69/6.48  
% 47.69/6.48  ------ AIG Options
% 47.69/6.48  
% 47.69/6.48  --aig_mode                              false
% 47.69/6.48  
% 47.69/6.48  ------ Instantiation Options
% 47.69/6.48  
% 47.69/6.48  --instantiation_flag                    true
% 47.69/6.48  --inst_sos_flag                         false
% 47.69/6.48  --inst_sos_phase                        true
% 47.69/6.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.69/6.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.69/6.48  --inst_lit_sel_side                     num_symb
% 47.69/6.48  --inst_solver_per_active                1400
% 47.69/6.48  --inst_solver_calls_frac                1.
% 47.69/6.48  --inst_passive_queue_type               priority_queues
% 47.69/6.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.69/6.48  --inst_passive_queues_freq              [25;2]
% 47.69/6.48  --inst_dismatching                      true
% 47.69/6.48  --inst_eager_unprocessed_to_passive     true
% 47.69/6.48  --inst_prop_sim_given                   true
% 47.69/6.48  --inst_prop_sim_new                     false
% 47.69/6.48  --inst_subs_new                         false
% 47.69/6.48  --inst_eq_res_simp                      false
% 47.69/6.48  --inst_subs_given                       false
% 47.69/6.48  --inst_orphan_elimination               true
% 47.69/6.48  --inst_learning_loop_flag               true
% 47.69/6.48  --inst_learning_start                   3000
% 47.69/6.48  --inst_learning_factor                  2
% 47.69/6.48  --inst_start_prop_sim_after_learn       3
% 47.69/6.48  --inst_sel_renew                        solver
% 47.69/6.48  --inst_lit_activity_flag                true
% 47.69/6.48  --inst_restr_to_given                   false
% 47.69/6.48  --inst_activity_threshold               500
% 47.69/6.48  --inst_out_proof                        true
% 47.69/6.48  
% 47.69/6.48  ------ Resolution Options
% 47.69/6.48  
% 47.69/6.48  --resolution_flag                       true
% 47.69/6.48  --res_lit_sel                           adaptive
% 47.69/6.48  --res_lit_sel_side                      none
% 47.69/6.48  --res_ordering                          kbo
% 47.69/6.48  --res_to_prop_solver                    active
% 47.69/6.48  --res_prop_simpl_new                    false
% 47.69/6.48  --res_prop_simpl_given                  true
% 47.69/6.48  --res_passive_queue_type                priority_queues
% 47.69/6.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.69/6.48  --res_passive_queues_freq               [15;5]
% 47.69/6.48  --res_forward_subs                      full
% 47.69/6.48  --res_backward_subs                     full
% 47.69/6.48  --res_forward_subs_resolution           true
% 47.69/6.48  --res_backward_subs_resolution          true
% 47.69/6.48  --res_orphan_elimination                true
% 47.69/6.48  --res_time_limit                        2.
% 47.69/6.48  --res_out_proof                         true
% 47.69/6.48  
% 47.69/6.48  ------ Superposition Options
% 47.69/6.48  
% 47.69/6.48  --superposition_flag                    true
% 47.69/6.48  --sup_passive_queue_type                priority_queues
% 47.69/6.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.69/6.48  --sup_passive_queues_freq               [8;1;4]
% 47.69/6.48  --demod_completeness_check              fast
% 47.69/6.48  --demod_use_ground                      true
% 47.69/6.48  --sup_to_prop_solver                    passive
% 47.69/6.48  --sup_prop_simpl_new                    true
% 47.69/6.48  --sup_prop_simpl_given                  true
% 47.69/6.48  --sup_fun_splitting                     false
% 47.69/6.48  --sup_smt_interval                      50000
% 47.69/6.48  
% 47.69/6.48  ------ Superposition Simplification Setup
% 47.69/6.48  
% 47.69/6.48  --sup_indices_passive                   []
% 47.69/6.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.69/6.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.69/6.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.69/6.48  --sup_full_triv                         [TrivRules;PropSubs]
% 47.69/6.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.69/6.48  --sup_full_bw                           [BwDemod]
% 47.69/6.48  --sup_immed_triv                        [TrivRules]
% 47.69/6.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.69/6.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.69/6.48  --sup_immed_bw_main                     []
% 47.69/6.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.69/6.48  --sup_input_triv                        [Unflattening;TrivRules]
% 47.69/6.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.69/6.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.69/6.48  
% 47.69/6.48  ------ Combination Options
% 47.69/6.48  
% 47.69/6.48  --comb_res_mult                         3
% 47.69/6.48  --comb_sup_mult                         2
% 47.69/6.48  --comb_inst_mult                        10
% 47.69/6.48  
% 47.69/6.48  ------ Debug Options
% 47.69/6.48  
% 47.69/6.48  --dbg_backtrace                         false
% 47.69/6.48  --dbg_dump_prop_clauses                 false
% 47.69/6.48  --dbg_dump_prop_clauses_file            -
% 47.69/6.48  --dbg_out_stat                          false
% 47.69/6.48  ------ Parsing...
% 47.69/6.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.69/6.48  
% 47.69/6.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 47.69/6.48  
% 47.69/6.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.69/6.48  
% 47.69/6.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 47.69/6.48  ------ Proving...
% 47.69/6.48  ------ Problem Properties 
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  clauses                                 10
% 47.69/6.48  conjectures                             1
% 47.69/6.48  EPR                                     0
% 47.69/6.48  Horn                                    10
% 47.69/6.48  unary                                   10
% 47.69/6.48  binary                                  0
% 47.69/6.48  lits                                    10
% 47.69/6.48  lits eq                                 10
% 47.69/6.48  fd_pure                                 0
% 47.69/6.48  fd_pseudo                               0
% 47.69/6.48  fd_cond                                 0
% 47.69/6.48  fd_pseudo_cond                          0
% 47.69/6.48  AC symbols                              0
% 47.69/6.48  
% 47.69/6.48  ------ Schedule UEQ
% 47.69/6.48  
% 47.69/6.48  ------ pure equality problem: resolution off 
% 47.69/6.48  
% 47.69/6.48  ------ Option_UEQ Time Limit: Unbounded
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  ------ 
% 47.69/6.48  Current options:
% 47.69/6.48  ------ 
% 47.69/6.48  
% 47.69/6.48  ------ Input Options
% 47.69/6.48  
% 47.69/6.48  --out_options                           all
% 47.69/6.48  --tptp_safe_out                         true
% 47.69/6.48  --problem_path                          ""
% 47.69/6.48  --include_path                          ""
% 47.69/6.48  --clausifier                            res/vclausify_rel
% 47.69/6.48  --clausifier_options                    --mode clausify
% 47.69/6.48  --stdin                                 false
% 47.69/6.48  --stats_out                             all
% 47.69/6.48  
% 47.69/6.48  ------ General Options
% 47.69/6.48  
% 47.69/6.48  --fof                                   false
% 47.69/6.48  --time_out_real                         305.
% 47.69/6.48  --time_out_virtual                      -1.
% 47.69/6.48  --symbol_type_check                     false
% 47.69/6.48  --clausify_out                          false
% 47.69/6.48  --sig_cnt_out                           false
% 47.69/6.48  --trig_cnt_out                          false
% 47.69/6.48  --trig_cnt_out_tolerance                1.
% 47.69/6.48  --trig_cnt_out_sk_spl                   false
% 47.69/6.48  --abstr_cl_out                          false
% 47.69/6.48  
% 47.69/6.48  ------ Global Options
% 47.69/6.48  
% 47.69/6.48  --schedule                              default
% 47.69/6.48  --add_important_lit                     false
% 47.69/6.48  --prop_solver_per_cl                    1000
% 47.69/6.48  --min_unsat_core                        false
% 47.69/6.48  --soft_assumptions                      false
% 47.69/6.48  --soft_lemma_size                       3
% 47.69/6.48  --prop_impl_unit_size                   0
% 47.69/6.48  --prop_impl_unit                        []
% 47.69/6.48  --share_sel_clauses                     true
% 47.69/6.48  --reset_solvers                         false
% 47.69/6.48  --bc_imp_inh                            [conj_cone]
% 47.69/6.48  --conj_cone_tolerance                   3.
% 47.69/6.48  --extra_neg_conj                        none
% 47.69/6.48  --large_theory_mode                     true
% 47.69/6.48  --prolific_symb_bound                   200
% 47.69/6.48  --lt_threshold                          2000
% 47.69/6.48  --clause_weak_htbl                      true
% 47.69/6.48  --gc_record_bc_elim                     false
% 47.69/6.48  
% 47.69/6.48  ------ Preprocessing Options
% 47.69/6.48  
% 47.69/6.48  --preprocessing_flag                    true
% 47.69/6.48  --time_out_prep_mult                    0.1
% 47.69/6.48  --splitting_mode                        input
% 47.69/6.48  --splitting_grd                         true
% 47.69/6.48  --splitting_cvd                         false
% 47.69/6.48  --splitting_cvd_svl                     false
% 47.69/6.48  --splitting_nvd                         32
% 47.69/6.48  --sub_typing                            true
% 47.69/6.48  --prep_gs_sim                           true
% 47.69/6.48  --prep_unflatten                        true
% 47.69/6.48  --prep_res_sim                          true
% 47.69/6.48  --prep_upred                            true
% 47.69/6.48  --prep_sem_filter                       exhaustive
% 47.69/6.48  --prep_sem_filter_out                   false
% 47.69/6.48  --pred_elim                             true
% 47.69/6.48  --res_sim_input                         true
% 47.69/6.48  --eq_ax_congr_red                       true
% 47.69/6.48  --pure_diseq_elim                       true
% 47.69/6.48  --brand_transform                       false
% 47.69/6.48  --non_eq_to_eq                          false
% 47.69/6.48  --prep_def_merge                        true
% 47.69/6.48  --prep_def_merge_prop_impl              false
% 47.69/6.48  --prep_def_merge_mbd                    true
% 47.69/6.48  --prep_def_merge_tr_red                 false
% 47.69/6.48  --prep_def_merge_tr_cl                  false
% 47.69/6.48  --smt_preprocessing                     true
% 47.69/6.48  --smt_ac_axioms                         fast
% 47.69/6.48  --preprocessed_out                      false
% 47.69/6.48  --preprocessed_stats                    false
% 47.69/6.48  
% 47.69/6.48  ------ Abstraction refinement Options
% 47.69/6.48  
% 47.69/6.48  --abstr_ref                             []
% 47.69/6.48  --abstr_ref_prep                        false
% 47.69/6.48  --abstr_ref_until_sat                   false
% 47.69/6.48  --abstr_ref_sig_restrict                funpre
% 47.69/6.48  --abstr_ref_af_restrict_to_split_sk     false
% 47.69/6.48  --abstr_ref_under                       []
% 47.69/6.48  
% 47.69/6.48  ------ SAT Options
% 47.69/6.48  
% 47.69/6.48  --sat_mode                              false
% 47.69/6.48  --sat_fm_restart_options                ""
% 47.69/6.48  --sat_gr_def                            false
% 47.69/6.48  --sat_epr_types                         true
% 47.69/6.48  --sat_non_cyclic_types                  false
% 47.69/6.48  --sat_finite_models                     false
% 47.69/6.48  --sat_fm_lemmas                         false
% 47.69/6.48  --sat_fm_prep                           false
% 47.69/6.48  --sat_fm_uc_incr                        true
% 47.69/6.48  --sat_out_model                         small
% 47.69/6.48  --sat_out_clauses                       false
% 47.69/6.48  
% 47.69/6.48  ------ QBF Options
% 47.69/6.48  
% 47.69/6.48  --qbf_mode                              false
% 47.69/6.48  --qbf_elim_univ                         false
% 47.69/6.48  --qbf_dom_inst                          none
% 47.69/6.48  --qbf_dom_pre_inst                      false
% 47.69/6.48  --qbf_sk_in                             false
% 47.69/6.48  --qbf_pred_elim                         true
% 47.69/6.48  --qbf_split                             512
% 47.69/6.48  
% 47.69/6.48  ------ BMC1 Options
% 47.69/6.48  
% 47.69/6.48  --bmc1_incremental                      false
% 47.69/6.48  --bmc1_axioms                           reachable_all
% 47.69/6.48  --bmc1_min_bound                        0
% 47.69/6.48  --bmc1_max_bound                        -1
% 47.69/6.48  --bmc1_max_bound_default                -1
% 47.69/6.48  --bmc1_symbol_reachability              true
% 47.69/6.48  --bmc1_property_lemmas                  false
% 47.69/6.48  --bmc1_k_induction                      false
% 47.69/6.48  --bmc1_non_equiv_states                 false
% 47.69/6.48  --bmc1_deadlock                         false
% 47.69/6.48  --bmc1_ucm                              false
% 47.69/6.48  --bmc1_add_unsat_core                   none
% 47.69/6.48  --bmc1_unsat_core_children              false
% 47.69/6.48  --bmc1_unsat_core_extrapolate_axioms    false
% 47.69/6.48  --bmc1_out_stat                         full
% 47.69/6.48  --bmc1_ground_init                      false
% 47.69/6.48  --bmc1_pre_inst_next_state              false
% 47.69/6.48  --bmc1_pre_inst_state                   false
% 47.69/6.48  --bmc1_pre_inst_reach_state             false
% 47.69/6.48  --bmc1_out_unsat_core                   false
% 47.69/6.48  --bmc1_aig_witness_out                  false
% 47.69/6.48  --bmc1_verbose                          false
% 47.69/6.48  --bmc1_dump_clauses_tptp                false
% 47.69/6.48  --bmc1_dump_unsat_core_tptp             false
% 47.69/6.48  --bmc1_dump_file                        -
% 47.69/6.48  --bmc1_ucm_expand_uc_limit              128
% 47.69/6.48  --bmc1_ucm_n_expand_iterations          6
% 47.69/6.48  --bmc1_ucm_extend_mode                  1
% 47.69/6.48  --bmc1_ucm_init_mode                    2
% 47.69/6.48  --bmc1_ucm_cone_mode                    none
% 47.69/6.48  --bmc1_ucm_reduced_relation_type        0
% 47.69/6.48  --bmc1_ucm_relax_model                  4
% 47.69/6.48  --bmc1_ucm_full_tr_after_sat            true
% 47.69/6.48  --bmc1_ucm_expand_neg_assumptions       false
% 47.69/6.48  --bmc1_ucm_layered_model                none
% 47.69/6.48  --bmc1_ucm_max_lemma_size               10
% 47.69/6.48  
% 47.69/6.48  ------ AIG Options
% 47.69/6.48  
% 47.69/6.48  --aig_mode                              false
% 47.69/6.48  
% 47.69/6.48  ------ Instantiation Options
% 47.69/6.48  
% 47.69/6.48  --instantiation_flag                    false
% 47.69/6.48  --inst_sos_flag                         false
% 47.69/6.48  --inst_sos_phase                        true
% 47.69/6.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.69/6.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.69/6.48  --inst_lit_sel_side                     num_symb
% 47.69/6.48  --inst_solver_per_active                1400
% 47.69/6.48  --inst_solver_calls_frac                1.
% 47.69/6.48  --inst_passive_queue_type               priority_queues
% 47.69/6.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.69/6.48  --inst_passive_queues_freq              [25;2]
% 47.69/6.48  --inst_dismatching                      true
% 47.69/6.48  --inst_eager_unprocessed_to_passive     true
% 47.69/6.48  --inst_prop_sim_given                   true
% 47.69/6.48  --inst_prop_sim_new                     false
% 47.69/6.48  --inst_subs_new                         false
% 47.69/6.48  --inst_eq_res_simp                      false
% 47.69/6.48  --inst_subs_given                       false
% 47.69/6.48  --inst_orphan_elimination               true
% 47.69/6.48  --inst_learning_loop_flag               true
% 47.69/6.48  --inst_learning_start                   3000
% 47.69/6.48  --inst_learning_factor                  2
% 47.69/6.48  --inst_start_prop_sim_after_learn       3
% 47.69/6.48  --inst_sel_renew                        solver
% 47.69/6.48  --inst_lit_activity_flag                true
% 47.69/6.48  --inst_restr_to_given                   false
% 47.69/6.48  --inst_activity_threshold               500
% 47.69/6.48  --inst_out_proof                        true
% 47.69/6.48  
% 47.69/6.48  ------ Resolution Options
% 47.69/6.48  
% 47.69/6.48  --resolution_flag                       false
% 47.69/6.48  --res_lit_sel                           adaptive
% 47.69/6.48  --res_lit_sel_side                      none
% 47.69/6.48  --res_ordering                          kbo
% 47.69/6.48  --res_to_prop_solver                    active
% 47.69/6.48  --res_prop_simpl_new                    false
% 47.69/6.48  --res_prop_simpl_given                  true
% 47.69/6.48  --res_passive_queue_type                priority_queues
% 47.69/6.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.69/6.48  --res_passive_queues_freq               [15;5]
% 47.69/6.48  --res_forward_subs                      full
% 47.69/6.48  --res_backward_subs                     full
% 47.69/6.48  --res_forward_subs_resolution           true
% 47.69/6.48  --res_backward_subs_resolution          true
% 47.69/6.48  --res_orphan_elimination                true
% 47.69/6.48  --res_time_limit                        2.
% 47.69/6.48  --res_out_proof                         true
% 47.69/6.48  
% 47.69/6.48  ------ Superposition Options
% 47.69/6.48  
% 47.69/6.48  --superposition_flag                    true
% 47.69/6.48  --sup_passive_queue_type                priority_queues
% 47.69/6.48  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.69/6.48  --sup_passive_queues_freq               [8;1;4]
% 47.69/6.48  --demod_completeness_check              fast
% 47.69/6.48  --demod_use_ground                      true
% 47.69/6.48  --sup_to_prop_solver                    active
% 47.69/6.48  --sup_prop_simpl_new                    false
% 47.69/6.48  --sup_prop_simpl_given                  false
% 47.69/6.48  --sup_fun_splitting                     true
% 47.69/6.48  --sup_smt_interval                      10000
% 47.69/6.48  
% 47.69/6.48  ------ Superposition Simplification Setup
% 47.69/6.48  
% 47.69/6.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.69/6.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.69/6.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.69/6.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.69/6.48  --sup_full_triv                         [TrivRules]
% 47.69/6.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.69/6.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.69/6.48  --sup_immed_triv                        [TrivRules]
% 47.69/6.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.69/6.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.69/6.48  --sup_immed_bw_main                     []
% 47.69/6.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.69/6.48  --sup_input_triv                        [Unflattening;TrivRules]
% 47.69/6.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.69/6.48  --sup_input_bw                          [BwDemod;BwSubsumption]
% 47.69/6.48  
% 47.69/6.48  ------ Combination Options
% 47.69/6.48  
% 47.69/6.48  --comb_res_mult                         1
% 47.69/6.48  --comb_sup_mult                         1
% 47.69/6.48  --comb_inst_mult                        1000000
% 47.69/6.48  
% 47.69/6.48  ------ Debug Options
% 47.69/6.48  
% 47.69/6.48  --dbg_backtrace                         false
% 47.69/6.48  --dbg_dump_prop_clauses                 false
% 47.69/6.48  --dbg_dump_prop_clauses_file            -
% 47.69/6.48  --dbg_out_stat                          false
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  ------ Proving...
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  % SZS status Theorem for theBenchmark.p
% 47.69/6.48  
% 47.69/6.48   Resolution empty clause
% 47.69/6.48  
% 47.69/6.48  % SZS output start CNFRefutation for theBenchmark.p
% 47.69/6.48  
% 47.69/6.48  fof(f4,axiom,(
% 47.69/6.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f21,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 47.69/6.48    inference(cnf_transformation,[],[f4])).
% 47.69/6.48  
% 47.69/6.48  fof(f12,axiom,(
% 47.69/6.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f29,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 47.69/6.48    inference(cnf_transformation,[],[f12])).
% 47.69/6.48  
% 47.69/6.48  fof(f8,axiom,(
% 47.69/6.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f25,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 47.69/6.48    inference(cnf_transformation,[],[f8])).
% 47.69/6.48  
% 47.69/6.48  fof(f31,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 47.69/6.48    inference(definition_unfolding,[],[f29,f25])).
% 47.69/6.48  
% 47.69/6.48  fof(f34,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 47.69/6.48    inference(definition_unfolding,[],[f21,f31,f31])).
% 47.69/6.48  
% 47.69/6.48  fof(f3,axiom,(
% 47.69/6.48    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f20,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)) )),
% 47.69/6.48    inference(cnf_transformation,[],[f3])).
% 47.69/6.48  
% 47.69/6.48  fof(f32,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1)) )),
% 47.69/6.48    inference(definition_unfolding,[],[f20,f31,f25])).
% 47.69/6.48  
% 47.69/6.48  fof(f5,axiom,(
% 47.69/6.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f22,plain,(
% 47.69/6.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 47.69/6.48    inference(cnf_transformation,[],[f5])).
% 47.69/6.48  
% 47.69/6.48  fof(f7,axiom,(
% 47.69/6.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f24,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 47.69/6.48    inference(cnf_transformation,[],[f7])).
% 47.69/6.48  
% 47.69/6.48  fof(f36,plain,(
% 47.69/6.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 47.69/6.48    inference(definition_unfolding,[],[f24,f25])).
% 47.69/6.48  
% 47.69/6.48  fof(f6,axiom,(
% 47.69/6.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f23,plain,(
% 47.69/6.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 47.69/6.48    inference(cnf_transformation,[],[f6])).
% 47.69/6.48  
% 47.69/6.48  fof(f35,plain,(
% 47.69/6.48    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 47.69/6.48    inference(definition_unfolding,[],[f23,f31])).
% 47.69/6.48  
% 47.69/6.48  fof(f1,axiom,(
% 47.69/6.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f15,plain,(
% 47.69/6.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 47.69/6.48    inference(rectify,[],[f1])).
% 47.69/6.48  
% 47.69/6.48  fof(f19,plain,(
% 47.69/6.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 47.69/6.48    inference(cnf_transformation,[],[f15])).
% 47.69/6.48  
% 47.69/6.48  fof(f33,plain,(
% 47.69/6.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 47.69/6.48    inference(definition_unfolding,[],[f19,f31])).
% 47.69/6.48  
% 47.69/6.48  fof(f11,axiom,(
% 47.69/6.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f28,plain,(
% 47.69/6.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 47.69/6.48    inference(cnf_transformation,[],[f11])).
% 47.69/6.48  
% 47.69/6.48  fof(f9,axiom,(
% 47.69/6.48    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f26,plain,(
% 47.69/6.48    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 47.69/6.48    inference(cnf_transformation,[],[f9])).
% 47.69/6.48  
% 47.69/6.48  fof(f37,plain,(
% 47.69/6.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 47.69/6.48    inference(definition_unfolding,[],[f26,f25,f25])).
% 47.69/6.48  
% 47.69/6.48  fof(f10,axiom,(
% 47.69/6.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f27,plain,(
% 47.69/6.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 47.69/6.48    inference(cnf_transformation,[],[f10])).
% 47.69/6.48  
% 47.69/6.48  fof(f13,conjecture,(
% 47.69/6.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.69/6.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.69/6.48  
% 47.69/6.48  fof(f14,negated_conjecture,(
% 47.69/6.48    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.69/6.48    inference(negated_conjecture,[],[f13])).
% 47.69/6.48  
% 47.69/6.48  fof(f16,plain,(
% 47.69/6.48    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.69/6.48    inference(ennf_transformation,[],[f14])).
% 47.69/6.48  
% 47.69/6.48  fof(f17,plain,(
% 47.69/6.48    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 47.69/6.48    introduced(choice_axiom,[])).
% 47.69/6.48  
% 47.69/6.48  fof(f18,plain,(
% 47.69/6.48    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 47.69/6.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 47.69/6.48  
% 47.69/6.48  fof(f30,plain,(
% 47.69/6.48    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 47.69/6.48    inference(cnf_transformation,[],[f18])).
% 47.69/6.48  
% 47.69/6.48  fof(f38,plain,(
% 47.69/6.48    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 47.69/6.48    inference(definition_unfolding,[],[f30,f31])).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(cnf_transformation,[],[f34]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_0,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(cnf_transformation,[],[f32]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_162,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 47.69/6.48      inference(cnf_transformation,[],[f22]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(cnf_transformation,[],[f36]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_35,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_34,c_3]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(cnf_transformation,[],[f35]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_85,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_35,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
% 47.69/6.48      inference(cnf_transformation,[],[f33]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_36,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_35,c_1]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_105,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_85,c_36]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_252,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_0,c_105]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_274,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_252,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.69/6.48      inference(cnf_transformation,[],[f28]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_107,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_37044,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_274,c_107]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 47.69/6.48      inference(cnf_transformation,[],[f37]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_59,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_120,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_35,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_140,plain,
% 47.69/6.48      ( k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_120,c_36]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_467,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_59,c_59,c_140]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_492,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_467,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1993,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) = k4_xboole_0(X0,k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_274,c_492]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_125,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_7,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 47.69/6.48      inference(cnf_transformation,[],[f27]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_138,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_125,c_7]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_141,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = X0 ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_140,c_138]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_50,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_36]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_142,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_141,c_50]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2073,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_1993,c_140,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_164,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_166,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_164,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_56,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1035,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_166,c_56]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1040,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1035,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2371,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2073,c_1040]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2435,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_2371,c_2073]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3875,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_0,c_2435]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3993,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_3875,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3994,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_3993,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1028,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_166,c_140]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5892,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_3994,c_1028]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5967,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_5892,c_3994]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_46,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_237,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_46,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_247,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_237,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1126,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_247,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1172,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1126,c_247]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_36]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1134,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_247,c_48]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1164,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1134,c_247]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1176,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1172,c_1164]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_370,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),X0) = k5_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_48,c_46]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_371,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X0) = k5_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_370,c_46]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_717,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_371]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1182,plain,
% 47.69/6.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_1176,c_717]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1317,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1126,c_46,c_1182]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5968,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_5967,c_140,c_1317]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_37434,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_37044,c_5968]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_47,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_36,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_187,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_50,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_189,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_187,c_50,c_140,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1460,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_274,c_189]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1480,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1460,c_274]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1481,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1480,c_1028]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1482,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1481,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_12911,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0))))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_47,c_1482]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13229,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_12911,c_47]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1998,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),X1)) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_47,c_492]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13230,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_13229,c_1998]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2378,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2073,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2433,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_2378,c_2073]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_253,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_140,c_105]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_273,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_253,c_140]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1002,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),X1) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_273,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1058,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_1002,c_273]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6849,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_1058,c_492]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6857,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_6849,c_492]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13231,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_13230,c_2433,c_6857]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13434,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_13231]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13531,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_13434,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13465,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_13231,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13494,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_13465,c_5968]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1112,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_247,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1374,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1112,c_46,c_1182]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13495,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_13494,c_1317,c_1374]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13496,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_13495,c_1317]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_218,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_184,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_50]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2282,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_184,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13497,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_13496,c_47,c_218,c_2282]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13711,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_13497]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13907,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_13711,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_37435,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_37434,c_13531,c_13907]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_501,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X1))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_467,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_504,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_501,c_7,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2030,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_492,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_260,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_105,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_266,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_260,c_105]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_267,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_266,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2036,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_2030,c_267,c_1028]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2652,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2073,c_2036]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2711,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_2652,c_2073]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2766,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2711,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2830,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_2766,c_2711]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_11683,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k4_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_504,c_2830]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2381,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2073,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_496,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k5_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_467,c_2]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_507,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,X0)) = X0 ),
% 47.69/6.48      inference(light_normalisation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_496,c_3,c_7,c_50,c_140,c_273]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2429,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_2381,c_140,c_142,c_507]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_186,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_50,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2469,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2429,c_186]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2471,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_2469,c_50]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2462,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2429,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3119,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2471,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_472,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_140,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_477,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))),X0) = k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_273,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_318,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_47,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_523,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_477,c_47,c_318]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_527,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_472,c_523]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_528,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_527,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3185,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_3119,c_528,c_2429]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_81,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_7826,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) = k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_3185,c_81]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8098,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_7826,c_3]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_263,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_105,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4839,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_263,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4912,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_4839,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8139,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8098,c_4912]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8276,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_8139,c_8098]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_22015,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_140,c_8276]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1685,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_1182,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1756,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1685,c_46,c_218]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8216,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8098,c_1756]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_22408,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_22015,c_140,c_8216]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_22536,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_22408,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_22696,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_22536,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_42160,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_22696,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1019,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_166,c_105]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1048,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1019,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_82994,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2435,c_1048]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_83846,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_82994,c_2435]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_84143,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) = k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_42160,c_83846]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_11706,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_467,c_2830]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_768,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_528,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1539,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_768,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1563,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1539,c_768]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_11893,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_11706,c_6,c_492,c_1563]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_84485,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_84143,c_11893]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_27929,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_11893,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_751,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_4,c_528]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_785,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_751,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_39517,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_785,c_504]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_39584,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_39517,c_785]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_84486,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_84485,c_7,c_27929,c_39584]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_88022,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_11683,c_84486]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_27892,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_11893,c_140]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_27917,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_11893,c_5]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28059,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_27917,c_11893]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28060,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))))))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_28059,c_11893]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2771,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2711,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2823,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_2771,c_140]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_491,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_467,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2824,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_2823,c_6,c_467,c_491]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_16449,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2824,c_492]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_16466,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_16449,c_492]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28061,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_28060,c_16466]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_64,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_75,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_64,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6106,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_3,c_75]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6116,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_142,c_75]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6128,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2711,c_75]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_500,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,X2))))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_467,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_505,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))))))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_500,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6640,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6128,c_6,c_505]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6641,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6640,c_1028]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6642,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6641,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6675,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6116,c_6642]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6676,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6675,c_492,c_505]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6677,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6676,c_1028]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6678,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6677,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6682,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6678,c_6642]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6689,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6106,c_6682]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28062,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_28061,c_6689,c_16466]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28103,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_27892,c_28062]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28104,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_28103,c_140]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28105,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_28104,c_528]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48635,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_28105,c_2824]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48641,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_48635,c_7,c_504]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_88604,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X0,X0),k1_xboole_0)),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_88022,c_48641]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_42015,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_4912,c_22696]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_43052,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_42015,c_5,c_42160]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_554,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0))) = X0 ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_507,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_44596,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)),k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0))))) = k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_43052,c_554]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_44677,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)),X0))) = X0 ),
% 47.69/6.48      inference(demodulation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_44596,c_3,c_7,c_1028,c_11683,c_13497]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_92,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_102,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_92,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_30978,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1))),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_140,c_102]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_30988,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_166,c_102]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_206,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_140,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_31728,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_30988,c_206,c_1317]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_31729,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3))),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_31728,c_13497]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_31745,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))))) = k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)),X2)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_30978,c_31729]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1941,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_267,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_31746,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),X2)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_31745,c_267,c_1941]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1003,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_142,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1057,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_1003,c_142]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_31747,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),X2)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_31746,c_1057]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_261,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_105,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_265,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k4_xboole_0(X1,X2),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_261,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_31748,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_31747,c_166,c_265]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_44678,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X0)))) = X0 ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_44677,c_8098,c_31748]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_44679,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X0)))) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_44678,c_3]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_44680,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = X0 ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_44679,c_7,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1433,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_5,c_274]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_45118,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_44680,c_1433]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_45236,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0))) = X0 ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_45118,c_44680]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_45787,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_45236,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_67481,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_4912,c_45787]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_42002,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_5,c_22696]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_43068,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_42002,c_5,c_42160]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_67794,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k1_xboole_0,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_45787,c_43068]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_67823,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)),k5_xboole_0(k1_xboole_0,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_67794,c_42160]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_67824,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)),X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_67823,c_46]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_67825,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_67824,c_8098]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_69025,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_67481,c_5,c_67825]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_74487,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X1),X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1)))),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_69025,c_102]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_74852,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X1),X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X1)),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_74487,c_69025]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2638,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_273,c_2036]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2723,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_2638,c_273]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4029,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))),k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2723,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4044,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_4029,c_318]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4045,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_4044,c_1317]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4046,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X0)))),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_4045,c_1317]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4047,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_4046,c_318,c_554]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5248,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_4047,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_24062,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_5248,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_24116,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_24062,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_25491,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_24116,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_25768,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_25491,c_24116]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_67642,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0),X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_45787,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_74853,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X1),X2)))))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),X2) ),
% 47.69/6.48      inference(demodulation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_74852,c_140,c_24116,c_25768,c_67642]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_74854,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),X2)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_74853,c_140,c_67642]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8152,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8098,c_105]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8264,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_8152,c_8098]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8923,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2723,c_8264]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_9037,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_8923,c_2723]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_126,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13696,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_13497]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28235,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_13696]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_406,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_186,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_420,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_406,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6354,plain,
% 47.69/6.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_420,c_1182]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6356,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)),X3)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_420,c_420]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6385,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6356,c_420]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6386,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6385,c_186,c_1374]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6396,plain,
% 47.69/6.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X2) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_6354,c_6386]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_6397,plain,
% 47.69/6.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X2) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_6396,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28272,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_6397,c_13696]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28615,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_28272,c_46]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_28669,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_28235,c_28615]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_49133,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_126,c_1374,c_28669]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_49134,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_49133,c_28669]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_49135,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)))))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_49134,c_28669]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_49273,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))))),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_9037,c_49135]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8915,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2036,c_8264]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_9045,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_8915,c_2036]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48966,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_48641,c_9045]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_50203,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_49273,c_48966]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13774,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_13497,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13790,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_13774,c_528,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13973,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_13790,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_14080,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_13973,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_50204,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_50203,c_14080,c_28669]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_50205,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_50204,c_46,c_14080]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_50206,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_50205,c_46,c_1998]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2641,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_189,c_2036]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2721,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_2641,c_189]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_11479,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2723,c_2721]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_11595,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_11479,c_528,c_2723]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48630,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_28105,c_504]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48664,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X1)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_48630,c_504]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_50207,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),X1),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1))))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(demodulation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_50206,c_50,c_8098,c_11595,c_48664]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_322,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_47,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34570,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_11683,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34592,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_11683,c_2]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34778,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_34592,c_1374,c_24116]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34803,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))))),k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,X1)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_34570,c_34778]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_50208,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(demodulation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_50207,c_273,c_322,c_24116,c_34803]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_70804,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X1,X1))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_50208,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_70819,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_70804,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_74855,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X1)),X2) ),
% 47.69/6.48      inference(demodulation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_74854,c_140,c_1998,c_13497,c_70819]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_88605,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_88604,c_3,c_166,c_11683,c_74855]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48934,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_48641,c_1040]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_49084,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_48934,c_48641]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_88606,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_88605,c_49084]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_725,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_371,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_10177,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_725,c_725,c_1182]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_91845,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_10177,c_88606]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_345,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_46,c_48]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5641,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_345,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5653,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_5641,c_1182]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_48912,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_48641,c_8276]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_49112,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_48912,c_48641]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1466,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_274,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1467,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1466,c_140,c_1182]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1468,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1467,c_46]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_49113,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_49112,c_1468]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_92420,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_91845,c_5653,c_49113]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_92421,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_92420,c_8098]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_93883,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_92421,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13447,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_13231,c_8264]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13516,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_13447,c_13231]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_2593,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2471,c_8]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3569,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2471,c_2593]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3641,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))))) = X0 ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_3569,c_2471]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3642,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)))) = X0 ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_3641,c_528]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4945,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_3642,c_4]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4973,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_4945,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1006,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_318,c_166]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1054,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X1,k5_xboole_0(X0,X0))) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_1006,c_318]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4974,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X1),k1_xboole_0))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_4973,c_1054]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_4975,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)))) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_4974,c_3,c_50]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34991,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)))))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_13516,c_4975]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_35139,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_34991,c_13516]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1679,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_1182,c_318]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1763,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1679,c_1182]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_691,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_8,c_318]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_1764,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_1763,c_46,c_140,c_691]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_35140,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_35139,c_1764]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_35141,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_35140,c_8098,c_28105]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_53571,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_35141,c_0]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_53667,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_53571,c_5968]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_53668,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_53667,c_1317]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_53669,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_53668,c_13531,c_13907]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3155,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2462,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_3156,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_3155,c_2462]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13781,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_13497,c_3156]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13785,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_13781,c_3156]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_13786,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_13785,c_528]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_53670,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_53669,c_13786]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_91888,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_53670,c_88606]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8326,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_528,c_504]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_8462,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_8326,c_528]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_92363,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_91888,c_8462,c_48641]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_93956,plain,
% 47.69/6.48      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_93883,c_37435,c_92363]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_93957,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_93956,c_81]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_94834,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_88606,c_93957]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_94969,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_93957,c_1040]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_95107,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_94969,c_93957]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_95266,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_94834,c_95107]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_95267,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_95266,c_92421]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34522,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_528,c_11683]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_34858,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_34522,c_528]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_95387,plain,
% 47.69/6.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_95267,c_34858]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_104641,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_95387,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_104918,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_104641,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_118935,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_104918,c_50208]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_118953,plain,
% 47.69/6.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_118935,c_50,c_1317]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_125240,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),X0),k5_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_118953,c_1482]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_125310,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X1),X0),k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_125240,c_118953]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_256,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_6,c_105]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_270,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_256,c_6]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_104626,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))),k5_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0)))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_95387,c_270]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_104940,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))),k5_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_104626,c_95387]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_104941,plain,
% 47.69/6.48      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X1),k5_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 47.69/6.48      inference(light_normalisation,[status(thm)],[c_104940,c_467]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_118936,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),X0)) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_104918,c_11683]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_125311,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X1)) = k5_xboole_0(X0,X1) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_125310,c_5,c_104941,c_118936]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_125696,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_2,c_125311]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_5931,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_1028,c_36]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_32868,plain,
% 47.69/6.48      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 47.69/6.48      inference(superposition,[status(thm)],[c_270,c_5931]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_126255,plain,
% 47.69/6.48      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 47.69/6.48      inference(light_normalisation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_125696,c_2,c_32868,c_37435]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_133957,plain,
% 47.69/6.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 47.69/6.48      inference(light_normalisation,
% 47.69/6.48                [status(thm)],
% 47.69/6.48                [c_162,c_162,c_37435,c_126255]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_9,negated_conjecture,
% 47.69/6.48      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 47.69/6.48      inference(cnf_transformation,[],[f38]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_43,plain,
% 47.69/6.48      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_8,c_9]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_133958,plain,
% 47.69/6.48      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
% 47.69/6.48      inference(demodulation,[status(thm)],[c_133957,c_43]) ).
% 47.69/6.48  
% 47.69/6.48  cnf(c_133965,plain,
% 47.69/6.48      ( $false ),
% 47.69/6.48      inference(equality_resolution_simp,[status(thm)],[c_133958]) ).
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  % SZS output end CNFRefutation for theBenchmark.p
% 47.69/6.48  
% 47.69/6.48  ------                               Statistics
% 47.69/6.48  
% 47.69/6.48  ------ General
% 47.69/6.48  
% 47.69/6.48  abstr_ref_over_cycles:                  0
% 47.69/6.48  abstr_ref_under_cycles:                 0
% 47.69/6.48  gc_basic_clause_elim:                   0
% 47.69/6.48  forced_gc_time:                         0
% 47.69/6.48  parsing_time:                           0.01
% 47.69/6.48  unif_index_cands_time:                  0.
% 47.69/6.48  unif_index_add_time:                    0.
% 47.69/6.48  orderings_time:                         0.
% 47.69/6.48  out_proof_time:                         0.022
% 47.69/6.48  total_time:                             5.845
% 47.69/6.48  num_of_symbols:                         36
% 47.69/6.48  num_of_terms:                           277048
% 47.69/6.48  
% 47.69/6.48  ------ Preprocessing
% 47.69/6.48  
% 47.69/6.48  num_of_splits:                          0
% 47.69/6.48  num_of_split_atoms:                     0
% 47.69/6.48  num_of_reused_defs:                     0
% 47.69/6.48  num_eq_ax_congr_red:                    0
% 47.69/6.48  num_of_sem_filtered_clauses:            0
% 47.69/6.48  num_of_subtypes:                        0
% 47.69/6.48  monotx_restored_types:                  0
% 47.69/6.48  sat_num_of_epr_types:                   0
% 47.69/6.48  sat_num_of_non_cyclic_types:            0
% 47.69/6.48  sat_guarded_non_collapsed_types:        0
% 47.69/6.48  num_pure_diseq_elim:                    0
% 47.69/6.48  simp_replaced_by:                       0
% 47.69/6.48  res_preprocessed:                       24
% 47.69/6.48  prep_upred:                             0
% 47.69/6.48  prep_unflattend:                        0
% 47.69/6.48  smt_new_axioms:                         0
% 47.69/6.48  pred_elim_cands:                        0
% 47.69/6.48  pred_elim:                              0
% 47.69/6.48  pred_elim_cl:                           0
% 47.69/6.48  pred_elim_cycles:                       0
% 47.69/6.48  merged_defs:                            0
% 47.69/6.48  merged_defs_ncl:                        0
% 47.69/6.48  bin_hyper_res:                          0
% 47.69/6.48  prep_cycles:                            2
% 47.69/6.48  pred_elim_time:                         0.
% 47.69/6.48  splitting_time:                         0.
% 47.69/6.48  sem_filter_time:                        0.
% 47.69/6.48  monotx_time:                            0.
% 47.69/6.48  subtype_inf_time:                       0.
% 47.69/6.48  
% 47.69/6.48  ------ Problem properties
% 47.69/6.48  
% 47.69/6.48  clauses:                                10
% 47.69/6.48  conjectures:                            1
% 47.69/6.48  epr:                                    0
% 47.69/6.48  horn:                                   10
% 47.69/6.48  ground:                                 1
% 47.69/6.48  unary:                                  10
% 47.69/6.48  binary:                                 0
% 47.69/6.48  lits:                                   10
% 47.69/6.48  lits_eq:                                10
% 47.69/6.48  fd_pure:                                0
% 47.69/6.48  fd_pseudo:                              0
% 47.69/6.48  fd_cond:                                0
% 47.69/6.48  fd_pseudo_cond:                         0
% 47.69/6.48  ac_symbols:                             0
% 47.69/6.48  
% 47.69/6.48  ------ Propositional Solver
% 47.69/6.48  
% 47.69/6.48  prop_solver_calls:                      13
% 47.69/6.48  prop_fast_solver_calls:                 60
% 47.69/6.48  smt_solver_calls:                       0
% 47.69/6.48  smt_fast_solver_calls:                  0
% 47.69/6.48  prop_num_of_clauses:                    586
% 47.69/6.48  prop_preprocess_simplified:             385
% 47.69/6.48  prop_fo_subsumed:                       0
% 47.69/6.48  prop_solver_time:                       0.
% 47.69/6.48  smt_solver_time:                        0.
% 47.69/6.48  smt_fast_solver_time:                   0.
% 47.69/6.48  prop_fast_solver_time:                  0.
% 47.69/6.48  prop_unsat_core_time:                   0.
% 47.69/6.48  
% 47.69/6.48  ------ QBF
% 47.69/6.48  
% 47.69/6.48  qbf_q_res:                              0
% 47.69/6.48  qbf_num_tautologies:                    0
% 47.69/6.48  qbf_prep_cycles:                        0
% 47.69/6.48  
% 47.69/6.48  ------ BMC1
% 47.69/6.48  
% 47.69/6.48  bmc1_current_bound:                     -1
% 47.69/6.48  bmc1_last_solved_bound:                 -1
% 47.69/6.48  bmc1_unsat_core_size:                   -1
% 47.69/6.48  bmc1_unsat_core_parents_size:           -1
% 47.69/6.48  bmc1_merge_next_fun:                    0
% 47.69/6.48  bmc1_unsat_core_clauses_time:           0.
% 47.69/6.48  
% 47.69/6.48  ------ Instantiation
% 47.69/6.48  
% 47.69/6.48  inst_num_of_clauses:                    0
% 47.69/6.48  inst_num_in_passive:                    0
% 47.69/6.48  inst_num_in_active:                     0
% 47.69/6.48  inst_num_in_unprocessed:                0
% 47.69/6.48  inst_num_of_loops:                      0
% 47.69/6.48  inst_num_of_learning_restarts:          0
% 47.69/6.48  inst_num_moves_active_passive:          0
% 47.69/6.48  inst_lit_activity:                      0
% 47.69/6.48  inst_lit_activity_moves:                0
% 47.69/6.48  inst_num_tautologies:                   0
% 47.69/6.48  inst_num_prop_implied:                  0
% 47.69/6.48  inst_num_existing_simplified:           0
% 47.69/6.48  inst_num_eq_res_simplified:             0
% 47.69/6.48  inst_num_child_elim:                    0
% 47.69/6.48  inst_num_of_dismatching_blockings:      0
% 47.69/6.48  inst_num_of_non_proper_insts:           0
% 47.69/6.48  inst_num_of_duplicates:                 0
% 47.69/6.48  inst_inst_num_from_inst_to_res:         0
% 47.69/6.48  inst_dismatching_checking_time:         0.
% 47.69/6.48  
% 47.69/6.48  ------ Resolution
% 47.69/6.48  
% 47.69/6.48  res_num_of_clauses:                     0
% 47.69/6.48  res_num_in_passive:                     0
% 47.69/6.48  res_num_in_active:                      0
% 47.69/6.48  res_num_of_loops:                       26
% 47.69/6.48  res_forward_subset_subsumed:            0
% 47.69/6.48  res_backward_subset_subsumed:           0
% 47.69/6.48  res_forward_subsumed:                   0
% 47.69/6.48  res_backward_subsumed:                  0
% 47.69/6.48  res_forward_subsumption_resolution:     0
% 47.69/6.48  res_backward_subsumption_resolution:    0
% 47.69/6.48  res_clause_to_clause_subsumption:       363157
% 47.69/6.48  res_orphan_elimination:                 0
% 47.69/6.48  res_tautology_del:                      0
% 47.69/6.48  res_num_eq_res_simplified:              0
% 47.69/6.48  res_num_sel_changes:                    0
% 47.69/6.48  res_moves_from_active_to_pass:          0
% 47.69/6.48  
% 47.69/6.48  ------ Superposition
% 47.69/6.48  
% 47.69/6.48  sup_time_total:                         0.
% 47.69/6.48  sup_time_generating:                    0.
% 47.69/6.48  sup_time_sim_full:                      0.
% 47.69/6.48  sup_time_sim_immed:                     0.
% 47.69/6.48  
% 47.69/6.48  sup_num_of_clauses:                     11459
% 47.69/6.48  sup_num_in_active:                      229
% 47.69/6.48  sup_num_in_passive:                     11230
% 47.69/6.48  sup_num_of_loops:                       316
% 47.69/6.48  sup_fw_superposition:                   29255
% 47.69/6.48  sup_bw_superposition:                   27190
% 47.69/6.48  sup_immediate_simplified:               51112
% 47.69/6.48  sup_given_eliminated:                   11
% 47.69/6.48  comparisons_done:                       0
% 47.69/6.48  comparisons_avoided:                    0
% 47.69/6.48  
% 47.69/6.48  ------ Simplifications
% 47.69/6.48  
% 47.69/6.48  
% 47.69/6.48  sim_fw_subset_subsumed:                 0
% 47.69/6.48  sim_bw_subset_subsumed:                 0
% 47.69/6.48  sim_fw_subsumed:                        3676
% 47.69/6.48  sim_bw_subsumed:                        256
% 47.69/6.48  sim_fw_subsumption_res:                 0
% 47.69/6.48  sim_bw_subsumption_res:                 0
% 47.69/6.48  sim_tautology_del:                      0
% 47.69/6.48  sim_eq_tautology_del:                   19595
% 47.69/6.48  sim_eq_res_simp:                        0
% 47.69/6.48  sim_fw_demodulated:                     57408
% 47.69/6.48  sim_bw_demodulated:                     561
% 47.69/6.48  sim_light_normalised:                   19267
% 47.69/6.48  sim_joinable_taut:                      0
% 47.69/6.48  sim_joinable_simp:                      0
% 47.69/6.48  sim_ac_normalised:                      0
% 47.69/6.48  sim_smt_subsumption:                    0
% 47.69/6.48  
%------------------------------------------------------------------------------
