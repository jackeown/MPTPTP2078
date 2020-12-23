%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:07 EST 2020

% Result     : Theorem 23.28s
% Output     : CNFRefutation 23.28s
% Verified   : 
% Statistics : Number of formulae       :  141 (4011 expanded)
%              Number of clauses        :  112 (1722 expanded)
%              Number of leaves         :   12 (1074 expanded)
%              Depth                    :   25
%              Number of atoms          :  142 (4012 expanded)
%              Number of equality atoms :  141 (4011 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f25,f17,f17,f17,f17])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)
   => k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f26,f17,f17,f23])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_45,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_48,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_45,c_2])).

cnf(c_467,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_6,c_48])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_84,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_483,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_467,c_84])).

cnf(c_41,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_62,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_41,c_5])).

cnf(c_68,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_62,c_5])).

cnf(c_2269,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X1)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X0),X1) ),
    inference(superposition,[status(thm)],[c_483,c_68])).

cnf(c_2357,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_2269,c_483])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8739,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(superposition,[status(thm)],[c_2357,c_7])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_28,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_44,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_28,c_4])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_78,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_222,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_44,c_78])).

cnf(c_256,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_222,c_6])).

cnf(c_258,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_256,c_44])).

cnf(c_8761,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1),k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_8739,c_258])).

cnf(c_53,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_2,c_41])).

cnf(c_57,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_53,c_41])).

cnf(c_197,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X0)) ),
    inference(superposition,[status(thm)],[c_44,c_7])).

cnf(c_213,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X0,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_197,c_3])).

cnf(c_141,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) ),
    inference(superposition,[status(thm)],[c_3,c_7])).

cnf(c_168,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_141,c_3])).

cnf(c_169,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1),k4_xboole_0(X1,k2_xboole_0(X0,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_168,c_2])).

cnf(c_170,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_169,c_1])).

cnf(c_214,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X1),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_213,c_2,c_3,c_170])).

cnf(c_63,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_2])).

cnf(c_54,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_41,c_2])).

cnf(c_56,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_54,c_2])).

cnf(c_495,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_56,c_48])).

cnf(c_199,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_44,c_2])).

cnf(c_212,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_199,c_1])).

cnf(c_235,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_212,c_2])).

cnf(c_497,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_495,c_235])).

cnf(c_1110,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_497])).

cnf(c_1678,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X0) ),
    inference(superposition,[status(thm)],[c_63,c_1110])).

cnf(c_305,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_258,c_5])).

cnf(c_314,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_305,c_2])).

cnf(c_336,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_314,c_2])).

cnf(c_354,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_336,c_1])).

cnf(c_801,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_63,c_354])).

cnf(c_820,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_801,c_63])).

cnf(c_1725,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1678,c_820])).

cnf(c_8762,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_8761,c_3,c_28,c_57,c_214,c_256,c_1725])).

cnf(c_329,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_314])).

cnf(c_431,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_329,c_5])).

cnf(c_439,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_431,c_5,c_256])).

cnf(c_859,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_439])).

cnf(c_748,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_354])).

cnf(c_973,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_748])).

cnf(c_1013,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_973,c_748])).

cnf(c_1474,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_859,c_1013])).

cnf(c_1514,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1474,c_28])).

cnf(c_6093,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1514])).

cnf(c_9899,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_8762,c_6093])).

cnf(c_9927,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_9899,c_5,c_483])).

cnf(c_80,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_87,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_80,c_5])).

cnf(c_790,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_63])).

cnf(c_14370,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_87,c_790])).

cnf(c_14409,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_9927,c_14370])).

cnf(c_14849,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_14409,c_258])).

cnf(c_488,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_6,c_56])).

cnf(c_502,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_488,c_6])).

cnf(c_14850,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_14849,c_28,c_502])).

cnf(c_800,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_483,c_63])).

cnf(c_821,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_800,c_2])).

cnf(c_3733,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_821,c_41])).

cnf(c_3773,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3733,c_5,c_41])).

cnf(c_9822,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_8762])).

cnf(c_10009,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = X1 ),
    inference(light_normalisation,[status(thm)],[c_9822,c_314])).

cnf(c_43,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_358,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_43])).

cnf(c_10010,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_10009,c_28,c_358])).

cnf(c_10482,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_10010,c_43])).

cnf(c_11037,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3773,c_10482])).

cnf(c_550,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_41,c_483])).

cnf(c_3350,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_550])).

cnf(c_5781,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_3773,c_3350])).

cnf(c_548,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_483])).

cnf(c_2886,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_497,c_548])).

cnf(c_2938,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2886,c_41,c_748])).

cnf(c_3741,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_821,c_48])).

cnf(c_3765,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_3741,c_1514])).

cnf(c_5851,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5781,c_2938,c_3765])).

cnf(c_11126,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_11037,c_5851])).

cnf(c_28345,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_14850,c_11126])).

cnf(c_9879,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_8762,c_354])).

cnf(c_9940,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_9879,c_8762])).

cnf(c_28468,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_28345,c_9940])).

cnf(c_11483,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_11126,c_5])).

cnf(c_8,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_27,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_59417,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_11483,c_27])).

cnf(c_65,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_65,c_5])).

cnf(c_304,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_258,c_5])).

cnf(c_315,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_304,c_256])).

cnf(c_1605,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_66,c_315])).

cnf(c_6513,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_84,c_1605])).

cnf(c_16894,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1013,c_6513])).

cnf(c_59418,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_59417,c_1,c_16894])).

cnf(c_60177,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_28468,c_59418])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:09:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.28/3.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.28/3.52  
% 23.28/3.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.28/3.52  
% 23.28/3.52  ------  iProver source info
% 23.28/3.52  
% 23.28/3.52  git: date: 2020-06-30 10:37:57 +0100
% 23.28/3.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.28/3.52  git: non_committed_changes: false
% 23.28/3.52  git: last_make_outside_of_git: false
% 23.28/3.52  
% 23.28/3.52  ------ 
% 23.28/3.52  
% 23.28/3.52  ------ Input Options
% 23.28/3.52  
% 23.28/3.52  --out_options                           all
% 23.28/3.52  --tptp_safe_out                         true
% 23.28/3.52  --problem_path                          ""
% 23.28/3.52  --include_path                          ""
% 23.28/3.52  --clausifier                            res/vclausify_rel
% 23.28/3.52  --clausifier_options                    --mode clausify
% 23.28/3.52  --stdin                                 false
% 23.28/3.52  --stats_out                             all
% 23.28/3.52  
% 23.28/3.52  ------ General Options
% 23.28/3.52  
% 23.28/3.52  --fof                                   false
% 23.28/3.52  --time_out_real                         305.
% 23.28/3.52  --time_out_virtual                      -1.
% 23.28/3.52  --symbol_type_check                     false
% 23.28/3.52  --clausify_out                          false
% 23.28/3.52  --sig_cnt_out                           false
% 23.28/3.52  --trig_cnt_out                          false
% 23.28/3.52  --trig_cnt_out_tolerance                1.
% 23.28/3.52  --trig_cnt_out_sk_spl                   false
% 23.28/3.52  --abstr_cl_out                          false
% 23.28/3.52  
% 23.28/3.52  ------ Global Options
% 23.28/3.52  
% 23.28/3.52  --schedule                              default
% 23.28/3.52  --add_important_lit                     false
% 23.28/3.52  --prop_solver_per_cl                    1000
% 23.28/3.52  --min_unsat_core                        false
% 23.28/3.52  --soft_assumptions                      false
% 23.28/3.52  --soft_lemma_size                       3
% 23.28/3.52  --prop_impl_unit_size                   0
% 23.28/3.52  --prop_impl_unit                        []
% 23.28/3.52  --share_sel_clauses                     true
% 23.28/3.52  --reset_solvers                         false
% 23.28/3.52  --bc_imp_inh                            [conj_cone]
% 23.28/3.52  --conj_cone_tolerance                   3.
% 23.28/3.52  --extra_neg_conj                        none
% 23.28/3.52  --large_theory_mode                     true
% 23.28/3.52  --prolific_symb_bound                   200
% 23.28/3.52  --lt_threshold                          2000
% 23.28/3.52  --clause_weak_htbl                      true
% 23.28/3.52  --gc_record_bc_elim                     false
% 23.28/3.52  
% 23.28/3.52  ------ Preprocessing Options
% 23.28/3.52  
% 23.28/3.52  --preprocessing_flag                    true
% 23.28/3.52  --time_out_prep_mult                    0.1
% 23.28/3.52  --splitting_mode                        input
% 23.28/3.52  --splitting_grd                         true
% 23.28/3.52  --splitting_cvd                         false
% 23.28/3.52  --splitting_cvd_svl                     false
% 23.28/3.52  --splitting_nvd                         32
% 23.28/3.52  --sub_typing                            true
% 23.28/3.52  --prep_gs_sim                           true
% 23.28/3.52  --prep_unflatten                        true
% 23.28/3.52  --prep_res_sim                          true
% 23.28/3.52  --prep_upred                            true
% 23.28/3.52  --prep_sem_filter                       exhaustive
% 23.28/3.52  --prep_sem_filter_out                   false
% 23.28/3.52  --pred_elim                             true
% 23.28/3.52  --res_sim_input                         true
% 23.28/3.52  --eq_ax_congr_red                       true
% 23.28/3.52  --pure_diseq_elim                       true
% 23.28/3.52  --brand_transform                       false
% 23.28/3.52  --non_eq_to_eq                          false
% 23.28/3.52  --prep_def_merge                        true
% 23.28/3.52  --prep_def_merge_prop_impl              false
% 23.28/3.52  --prep_def_merge_mbd                    true
% 23.28/3.52  --prep_def_merge_tr_red                 false
% 23.28/3.52  --prep_def_merge_tr_cl                  false
% 23.28/3.52  --smt_preprocessing                     true
% 23.28/3.52  --smt_ac_axioms                         fast
% 23.28/3.52  --preprocessed_out                      false
% 23.28/3.52  --preprocessed_stats                    false
% 23.28/3.52  
% 23.28/3.52  ------ Abstraction refinement Options
% 23.28/3.52  
% 23.28/3.52  --abstr_ref                             []
% 23.28/3.52  --abstr_ref_prep                        false
% 23.28/3.52  --abstr_ref_until_sat                   false
% 23.28/3.52  --abstr_ref_sig_restrict                funpre
% 23.28/3.52  --abstr_ref_af_restrict_to_split_sk     false
% 23.28/3.52  --abstr_ref_under                       []
% 23.28/3.52  
% 23.28/3.52  ------ SAT Options
% 23.28/3.52  
% 23.28/3.52  --sat_mode                              false
% 23.28/3.52  --sat_fm_restart_options                ""
% 23.28/3.52  --sat_gr_def                            false
% 23.28/3.52  --sat_epr_types                         true
% 23.28/3.52  --sat_non_cyclic_types                  false
% 23.28/3.52  --sat_finite_models                     false
% 23.28/3.52  --sat_fm_lemmas                         false
% 23.28/3.52  --sat_fm_prep                           false
% 23.28/3.52  --sat_fm_uc_incr                        true
% 23.28/3.52  --sat_out_model                         small
% 23.28/3.52  --sat_out_clauses                       false
% 23.28/3.52  
% 23.28/3.52  ------ QBF Options
% 23.28/3.52  
% 23.28/3.52  --qbf_mode                              false
% 23.28/3.52  --qbf_elim_univ                         false
% 23.28/3.52  --qbf_dom_inst                          none
% 23.28/3.52  --qbf_dom_pre_inst                      false
% 23.28/3.52  --qbf_sk_in                             false
% 23.28/3.52  --qbf_pred_elim                         true
% 23.28/3.52  --qbf_split                             512
% 23.28/3.52  
% 23.28/3.52  ------ BMC1 Options
% 23.28/3.52  
% 23.28/3.52  --bmc1_incremental                      false
% 23.28/3.52  --bmc1_axioms                           reachable_all
% 23.28/3.52  --bmc1_min_bound                        0
% 23.28/3.52  --bmc1_max_bound                        -1
% 23.28/3.52  --bmc1_max_bound_default                -1
% 23.28/3.52  --bmc1_symbol_reachability              true
% 23.28/3.52  --bmc1_property_lemmas                  false
% 23.28/3.52  --bmc1_k_induction                      false
% 23.28/3.52  --bmc1_non_equiv_states                 false
% 23.28/3.52  --bmc1_deadlock                         false
% 23.28/3.52  --bmc1_ucm                              false
% 23.28/3.52  --bmc1_add_unsat_core                   none
% 23.28/3.52  --bmc1_unsat_core_children              false
% 23.28/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 23.28/3.52  --bmc1_out_stat                         full
% 23.28/3.52  --bmc1_ground_init                      false
% 23.28/3.52  --bmc1_pre_inst_next_state              false
% 23.28/3.52  --bmc1_pre_inst_state                   false
% 23.28/3.52  --bmc1_pre_inst_reach_state             false
% 23.28/3.52  --bmc1_out_unsat_core                   false
% 23.28/3.52  --bmc1_aig_witness_out                  false
% 23.28/3.52  --bmc1_verbose                          false
% 23.28/3.52  --bmc1_dump_clauses_tptp                false
% 23.28/3.52  --bmc1_dump_unsat_core_tptp             false
% 23.28/3.52  --bmc1_dump_file                        -
% 23.28/3.52  --bmc1_ucm_expand_uc_limit              128
% 23.28/3.52  --bmc1_ucm_n_expand_iterations          6
% 23.28/3.52  --bmc1_ucm_extend_mode                  1
% 23.28/3.52  --bmc1_ucm_init_mode                    2
% 23.28/3.52  --bmc1_ucm_cone_mode                    none
% 23.28/3.52  --bmc1_ucm_reduced_relation_type        0
% 23.28/3.52  --bmc1_ucm_relax_model                  4
% 23.28/3.52  --bmc1_ucm_full_tr_after_sat            true
% 23.28/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 23.28/3.52  --bmc1_ucm_layered_model                none
% 23.28/3.52  --bmc1_ucm_max_lemma_size               10
% 23.28/3.52  
% 23.28/3.52  ------ AIG Options
% 23.28/3.52  
% 23.28/3.52  --aig_mode                              false
% 23.28/3.52  
% 23.28/3.52  ------ Instantiation Options
% 23.28/3.52  
% 23.28/3.52  --instantiation_flag                    true
% 23.28/3.52  --inst_sos_flag                         false
% 23.28/3.52  --inst_sos_phase                        true
% 23.28/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.28/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.28/3.52  --inst_lit_sel_side                     num_symb
% 23.28/3.52  --inst_solver_per_active                1400
% 23.28/3.52  --inst_solver_calls_frac                1.
% 23.28/3.52  --inst_passive_queue_type               priority_queues
% 23.28/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.28/3.52  --inst_passive_queues_freq              [25;2]
% 23.28/3.52  --inst_dismatching                      true
% 23.28/3.52  --inst_eager_unprocessed_to_passive     true
% 23.28/3.52  --inst_prop_sim_given                   true
% 23.28/3.52  --inst_prop_sim_new                     false
% 23.28/3.52  --inst_subs_new                         false
% 23.28/3.52  --inst_eq_res_simp                      false
% 23.28/3.52  --inst_subs_given                       false
% 23.28/3.52  --inst_orphan_elimination               true
% 23.28/3.52  --inst_learning_loop_flag               true
% 23.28/3.52  --inst_learning_start                   3000
% 23.28/3.52  --inst_learning_factor                  2
% 23.28/3.52  --inst_start_prop_sim_after_learn       3
% 23.28/3.52  --inst_sel_renew                        solver
% 23.28/3.52  --inst_lit_activity_flag                true
% 23.28/3.52  --inst_restr_to_given                   false
% 23.28/3.52  --inst_activity_threshold               500
% 23.28/3.52  --inst_out_proof                        true
% 23.28/3.52  
% 23.28/3.52  ------ Resolution Options
% 23.28/3.52  
% 23.28/3.52  --resolution_flag                       true
% 23.28/3.52  --res_lit_sel                           adaptive
% 23.28/3.52  --res_lit_sel_side                      none
% 23.28/3.52  --res_ordering                          kbo
% 23.28/3.52  --res_to_prop_solver                    active
% 23.28/3.52  --res_prop_simpl_new                    false
% 23.28/3.52  --res_prop_simpl_given                  true
% 23.28/3.52  --res_passive_queue_type                priority_queues
% 23.28/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.28/3.52  --res_passive_queues_freq               [15;5]
% 23.28/3.52  --res_forward_subs                      full
% 23.28/3.52  --res_backward_subs                     full
% 23.28/3.52  --res_forward_subs_resolution           true
% 23.28/3.52  --res_backward_subs_resolution          true
% 23.28/3.52  --res_orphan_elimination                true
% 23.28/3.52  --res_time_limit                        2.
% 23.28/3.52  --res_out_proof                         true
% 23.28/3.52  
% 23.28/3.52  ------ Superposition Options
% 23.28/3.52  
% 23.28/3.52  --superposition_flag                    true
% 23.28/3.52  --sup_passive_queue_type                priority_queues
% 23.28/3.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.28/3.52  --sup_passive_queues_freq               [8;1;4]
% 23.28/3.52  --demod_completeness_check              fast
% 23.28/3.52  --demod_use_ground                      true
% 23.28/3.52  --sup_to_prop_solver                    passive
% 23.28/3.52  --sup_prop_simpl_new                    true
% 23.28/3.52  --sup_prop_simpl_given                  true
% 23.28/3.52  --sup_fun_splitting                     false
% 23.28/3.52  --sup_smt_interval                      50000
% 23.28/3.52  
% 23.28/3.52  ------ Superposition Simplification Setup
% 23.28/3.52  
% 23.28/3.52  --sup_indices_passive                   []
% 23.28/3.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.52  --sup_full_triv                         [TrivRules;PropSubs]
% 23.28/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.28/3.52  --sup_full_bw                           [BwDemod]
% 23.28/3.52  --sup_immed_triv                        [TrivRules]
% 23.28/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.28/3.52  --sup_immed_bw_main                     []
% 23.28/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.28/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 23.28/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.28/3.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.28/3.52  
% 23.28/3.52  ------ Combination Options
% 23.28/3.52  
% 23.28/3.52  --comb_res_mult                         3
% 23.28/3.52  --comb_sup_mult                         2
% 23.28/3.52  --comb_inst_mult                        10
% 23.28/3.52  
% 23.28/3.52  ------ Debug Options
% 23.28/3.52  
% 23.28/3.52  --dbg_backtrace                         false
% 23.28/3.52  --dbg_dump_prop_clauses                 false
% 23.28/3.52  --dbg_dump_prop_clauses_file            -
% 23.28/3.52  --dbg_out_stat                          false
% 23.28/3.52  ------ Parsing...
% 23.28/3.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.28/3.52  
% 23.28/3.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 23.28/3.52  
% 23.28/3.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.28/3.52  
% 23.28/3.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.28/3.52  ------ Proving...
% 23.28/3.52  ------ Problem Properties 
% 23.28/3.52  
% 23.28/3.52  
% 23.28/3.52  clauses                                 9
% 23.28/3.52  conjectures                             1
% 23.28/3.52  EPR                                     0
% 23.28/3.52  Horn                                    9
% 23.28/3.52  unary                                   9
% 23.28/3.52  binary                                  0
% 23.28/3.52  lits                                    9
% 23.28/3.52  lits eq                                 9
% 23.28/3.52  fd_pure                                 0
% 23.28/3.52  fd_pseudo                               0
% 23.28/3.52  fd_cond                                 0
% 23.28/3.52  fd_pseudo_cond                          0
% 23.28/3.52  AC symbols                              0
% 23.28/3.52  
% 23.28/3.52  ------ Schedule UEQ
% 23.28/3.52  
% 23.28/3.52  ------ pure equality problem: resolution off 
% 23.28/3.52  
% 23.28/3.52  ------ Option_UEQ Time Limit: Unbounded
% 23.28/3.52  
% 23.28/3.52  
% 23.28/3.52  ------ 
% 23.28/3.52  Current options:
% 23.28/3.52  ------ 
% 23.28/3.52  
% 23.28/3.52  ------ Input Options
% 23.28/3.52  
% 23.28/3.52  --out_options                           all
% 23.28/3.52  --tptp_safe_out                         true
% 23.28/3.52  --problem_path                          ""
% 23.28/3.52  --include_path                          ""
% 23.28/3.52  --clausifier                            res/vclausify_rel
% 23.28/3.52  --clausifier_options                    --mode clausify
% 23.28/3.52  --stdin                                 false
% 23.28/3.52  --stats_out                             all
% 23.28/3.52  
% 23.28/3.52  ------ General Options
% 23.28/3.52  
% 23.28/3.52  --fof                                   false
% 23.28/3.52  --time_out_real                         305.
% 23.28/3.52  --time_out_virtual                      -1.
% 23.28/3.52  --symbol_type_check                     false
% 23.28/3.52  --clausify_out                          false
% 23.28/3.52  --sig_cnt_out                           false
% 23.28/3.52  --trig_cnt_out                          false
% 23.28/3.52  --trig_cnt_out_tolerance                1.
% 23.28/3.52  --trig_cnt_out_sk_spl                   false
% 23.28/3.52  --abstr_cl_out                          false
% 23.28/3.52  
% 23.28/3.52  ------ Global Options
% 23.28/3.52  
% 23.28/3.52  --schedule                              default
% 23.28/3.52  --add_important_lit                     false
% 23.28/3.52  --prop_solver_per_cl                    1000
% 23.28/3.52  --min_unsat_core                        false
% 23.28/3.52  --soft_assumptions                      false
% 23.28/3.52  --soft_lemma_size                       3
% 23.28/3.52  --prop_impl_unit_size                   0
% 23.28/3.52  --prop_impl_unit                        []
% 23.28/3.52  --share_sel_clauses                     true
% 23.28/3.52  --reset_solvers                         false
% 23.28/3.52  --bc_imp_inh                            [conj_cone]
% 23.28/3.52  --conj_cone_tolerance                   3.
% 23.28/3.52  --extra_neg_conj                        none
% 23.28/3.52  --large_theory_mode                     true
% 23.28/3.52  --prolific_symb_bound                   200
% 23.28/3.52  --lt_threshold                          2000
% 23.28/3.52  --clause_weak_htbl                      true
% 23.28/3.52  --gc_record_bc_elim                     false
% 23.28/3.52  
% 23.28/3.52  ------ Preprocessing Options
% 23.28/3.52  
% 23.28/3.52  --preprocessing_flag                    true
% 23.28/3.52  --time_out_prep_mult                    0.1
% 23.28/3.52  --splitting_mode                        input
% 23.28/3.52  --splitting_grd                         true
% 23.28/3.52  --splitting_cvd                         false
% 23.28/3.52  --splitting_cvd_svl                     false
% 23.28/3.52  --splitting_nvd                         32
% 23.28/3.52  --sub_typing                            true
% 23.28/3.52  --prep_gs_sim                           true
% 23.28/3.52  --prep_unflatten                        true
% 23.28/3.52  --prep_res_sim                          true
% 23.28/3.52  --prep_upred                            true
% 23.28/3.52  --prep_sem_filter                       exhaustive
% 23.28/3.52  --prep_sem_filter_out                   false
% 23.28/3.52  --pred_elim                             true
% 23.28/3.52  --res_sim_input                         true
% 23.28/3.52  --eq_ax_congr_red                       true
% 23.28/3.52  --pure_diseq_elim                       true
% 23.28/3.52  --brand_transform                       false
% 23.28/3.52  --non_eq_to_eq                          false
% 23.28/3.52  --prep_def_merge                        true
% 23.28/3.52  --prep_def_merge_prop_impl              false
% 23.28/3.52  --prep_def_merge_mbd                    true
% 23.28/3.52  --prep_def_merge_tr_red                 false
% 23.28/3.52  --prep_def_merge_tr_cl                  false
% 23.28/3.52  --smt_preprocessing                     true
% 23.28/3.52  --smt_ac_axioms                         fast
% 23.28/3.52  --preprocessed_out                      false
% 23.28/3.52  --preprocessed_stats                    false
% 23.28/3.52  
% 23.28/3.52  ------ Abstraction refinement Options
% 23.28/3.52  
% 23.28/3.52  --abstr_ref                             []
% 23.28/3.52  --abstr_ref_prep                        false
% 23.28/3.52  --abstr_ref_until_sat                   false
% 23.28/3.52  --abstr_ref_sig_restrict                funpre
% 23.28/3.52  --abstr_ref_af_restrict_to_split_sk     false
% 23.28/3.52  --abstr_ref_under                       []
% 23.28/3.52  
% 23.28/3.52  ------ SAT Options
% 23.28/3.52  
% 23.28/3.52  --sat_mode                              false
% 23.28/3.52  --sat_fm_restart_options                ""
% 23.28/3.52  --sat_gr_def                            false
% 23.28/3.52  --sat_epr_types                         true
% 23.28/3.52  --sat_non_cyclic_types                  false
% 23.28/3.52  --sat_finite_models                     false
% 23.28/3.52  --sat_fm_lemmas                         false
% 23.28/3.52  --sat_fm_prep                           false
% 23.28/3.52  --sat_fm_uc_incr                        true
% 23.28/3.52  --sat_out_model                         small
% 23.28/3.52  --sat_out_clauses                       false
% 23.28/3.52  
% 23.28/3.52  ------ QBF Options
% 23.28/3.52  
% 23.28/3.52  --qbf_mode                              false
% 23.28/3.52  --qbf_elim_univ                         false
% 23.28/3.52  --qbf_dom_inst                          none
% 23.28/3.52  --qbf_dom_pre_inst                      false
% 23.28/3.52  --qbf_sk_in                             false
% 23.28/3.52  --qbf_pred_elim                         true
% 23.28/3.52  --qbf_split                             512
% 23.28/3.52  
% 23.28/3.52  ------ BMC1 Options
% 23.28/3.52  
% 23.28/3.52  --bmc1_incremental                      false
% 23.28/3.52  --bmc1_axioms                           reachable_all
% 23.28/3.52  --bmc1_min_bound                        0
% 23.28/3.52  --bmc1_max_bound                        -1
% 23.28/3.52  --bmc1_max_bound_default                -1
% 23.28/3.52  --bmc1_symbol_reachability              true
% 23.28/3.52  --bmc1_property_lemmas                  false
% 23.28/3.52  --bmc1_k_induction                      false
% 23.28/3.52  --bmc1_non_equiv_states                 false
% 23.28/3.52  --bmc1_deadlock                         false
% 23.28/3.52  --bmc1_ucm                              false
% 23.28/3.52  --bmc1_add_unsat_core                   none
% 23.28/3.52  --bmc1_unsat_core_children              false
% 23.28/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 23.28/3.52  --bmc1_out_stat                         full
% 23.28/3.52  --bmc1_ground_init                      false
% 23.28/3.52  --bmc1_pre_inst_next_state              false
% 23.28/3.52  --bmc1_pre_inst_state                   false
% 23.28/3.52  --bmc1_pre_inst_reach_state             false
% 23.28/3.52  --bmc1_out_unsat_core                   false
% 23.28/3.52  --bmc1_aig_witness_out                  false
% 23.28/3.52  --bmc1_verbose                          false
% 23.28/3.52  --bmc1_dump_clauses_tptp                false
% 23.28/3.52  --bmc1_dump_unsat_core_tptp             false
% 23.28/3.52  --bmc1_dump_file                        -
% 23.28/3.52  --bmc1_ucm_expand_uc_limit              128
% 23.28/3.52  --bmc1_ucm_n_expand_iterations          6
% 23.28/3.52  --bmc1_ucm_extend_mode                  1
% 23.28/3.52  --bmc1_ucm_init_mode                    2
% 23.28/3.52  --bmc1_ucm_cone_mode                    none
% 23.28/3.52  --bmc1_ucm_reduced_relation_type        0
% 23.28/3.52  --bmc1_ucm_relax_model                  4
% 23.28/3.52  --bmc1_ucm_full_tr_after_sat            true
% 23.28/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 23.28/3.52  --bmc1_ucm_layered_model                none
% 23.28/3.52  --bmc1_ucm_max_lemma_size               10
% 23.28/3.52  
% 23.28/3.52  ------ AIG Options
% 23.28/3.52  
% 23.28/3.52  --aig_mode                              false
% 23.28/3.52  
% 23.28/3.52  ------ Instantiation Options
% 23.28/3.52  
% 23.28/3.52  --instantiation_flag                    false
% 23.28/3.52  --inst_sos_flag                         false
% 23.28/3.52  --inst_sos_phase                        true
% 23.28/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.28/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.28/3.52  --inst_lit_sel_side                     num_symb
% 23.28/3.52  --inst_solver_per_active                1400
% 23.28/3.52  --inst_solver_calls_frac                1.
% 23.28/3.52  --inst_passive_queue_type               priority_queues
% 23.28/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.28/3.52  --inst_passive_queues_freq              [25;2]
% 23.28/3.52  --inst_dismatching                      true
% 23.28/3.52  --inst_eager_unprocessed_to_passive     true
% 23.28/3.52  --inst_prop_sim_given                   true
% 23.28/3.52  --inst_prop_sim_new                     false
% 23.28/3.52  --inst_subs_new                         false
% 23.28/3.52  --inst_eq_res_simp                      false
% 23.28/3.52  --inst_subs_given                       false
% 23.28/3.52  --inst_orphan_elimination               true
% 23.28/3.52  --inst_learning_loop_flag               true
% 23.28/3.52  --inst_learning_start                   3000
% 23.28/3.52  --inst_learning_factor                  2
% 23.28/3.52  --inst_start_prop_sim_after_learn       3
% 23.28/3.52  --inst_sel_renew                        solver
% 23.28/3.52  --inst_lit_activity_flag                true
% 23.28/3.52  --inst_restr_to_given                   false
% 23.28/3.52  --inst_activity_threshold               500
% 23.28/3.52  --inst_out_proof                        true
% 23.28/3.52  
% 23.28/3.52  ------ Resolution Options
% 23.28/3.52  
% 23.28/3.52  --resolution_flag                       false
% 23.28/3.52  --res_lit_sel                           adaptive
% 23.28/3.52  --res_lit_sel_side                      none
% 23.28/3.52  --res_ordering                          kbo
% 23.28/3.52  --res_to_prop_solver                    active
% 23.28/3.52  --res_prop_simpl_new                    false
% 23.28/3.52  --res_prop_simpl_given                  true
% 23.28/3.52  --res_passive_queue_type                priority_queues
% 23.28/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.28/3.52  --res_passive_queues_freq               [15;5]
% 23.28/3.52  --res_forward_subs                      full
% 23.28/3.52  --res_backward_subs                     full
% 23.28/3.52  --res_forward_subs_resolution           true
% 23.28/3.52  --res_backward_subs_resolution          true
% 23.28/3.52  --res_orphan_elimination                true
% 23.28/3.52  --res_time_limit                        2.
% 23.28/3.52  --res_out_proof                         true
% 23.28/3.52  
% 23.28/3.52  ------ Superposition Options
% 23.28/3.52  
% 23.28/3.52  --superposition_flag                    true
% 23.28/3.52  --sup_passive_queue_type                priority_queues
% 23.28/3.52  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.28/3.52  --sup_passive_queues_freq               [8;1;4]
% 23.28/3.52  --demod_completeness_check              fast
% 23.28/3.52  --demod_use_ground                      true
% 23.28/3.52  --sup_to_prop_solver                    active
% 23.28/3.52  --sup_prop_simpl_new                    false
% 23.28/3.52  --sup_prop_simpl_given                  false
% 23.28/3.52  --sup_fun_splitting                     true
% 23.28/3.52  --sup_smt_interval                      10000
% 23.28/3.52  
% 23.28/3.52  ------ Superposition Simplification Setup
% 23.28/3.52  
% 23.28/3.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.28/3.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.28/3.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.52  --sup_full_triv                         [TrivRules]
% 23.28/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.28/3.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.28/3.52  --sup_immed_triv                        [TrivRules]
% 23.28/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.52  --sup_immed_bw_main                     []
% 23.28/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.28/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 23.28/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.52  --sup_input_bw                          [BwDemod;BwSubsumption]
% 23.28/3.52  
% 23.28/3.52  ------ Combination Options
% 23.28/3.52  
% 23.28/3.52  --comb_res_mult                         1
% 23.28/3.52  --comb_sup_mult                         1
% 23.28/3.52  --comb_inst_mult                        1000000
% 23.28/3.52  
% 23.28/3.52  ------ Debug Options
% 23.28/3.52  
% 23.28/3.52  --dbg_backtrace                         false
% 23.28/3.52  --dbg_dump_prop_clauses                 false
% 23.28/3.52  --dbg_dump_prop_clauses_file            -
% 23.28/3.52  --dbg_out_stat                          false
% 23.28/3.52  
% 23.28/3.52  
% 23.28/3.52  
% 23.28/3.52  
% 23.28/3.52  ------ Proving...
% 23.28/3.52  
% 23.28/3.52  
% 23.28/3.52  % SZS status Theorem for theBenchmark.p
% 23.28/3.52  
% 23.28/3.52   Resolution empty clause
% 23.28/3.52  
% 23.28/3.52  % SZS output start CNFRefutation for theBenchmark.p
% 23.28/3.52  
% 23.28/3.52  fof(f9,axiom,(
% 23.28/3.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f24,plain,(
% 23.28/3.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 23.28/3.52    inference(cnf_transformation,[],[f9])).
% 23.28/3.52  
% 23.28/3.52  fof(f8,axiom,(
% 23.28/3.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f23,plain,(
% 23.28/3.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.28/3.52    inference(cnf_transformation,[],[f8])).
% 23.28/3.52  
% 23.28/3.52  fof(f27,plain,(
% 23.28/3.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 23.28/3.52    inference(definition_unfolding,[],[f24,f23])).
% 23.28/3.52  
% 23.28/3.52  fof(f6,axiom,(
% 23.28/3.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f21,plain,(
% 23.28/3.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 23.28/3.52    inference(cnf_transformation,[],[f6])).
% 23.28/3.52  
% 23.28/3.52  fof(f4,axiom,(
% 23.28/3.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f19,plain,(
% 23.28/3.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.28/3.52    inference(cnf_transformation,[],[f4])).
% 23.28/3.52  
% 23.28/3.52  fof(f1,axiom,(
% 23.28/3.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f16,plain,(
% 23.28/3.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.28/3.52    inference(cnf_transformation,[],[f1])).
% 23.28/3.52  
% 23.28/3.52  fof(f7,axiom,(
% 23.28/3.52    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f22,plain,(
% 23.28/3.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 23.28/3.52    inference(cnf_transformation,[],[f7])).
% 23.28/3.52  
% 23.28/3.52  fof(f10,axiom,(
% 23.28/3.52    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f25,plain,(
% 23.28/3.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.28/3.52    inference(cnf_transformation,[],[f10])).
% 23.28/3.52  
% 23.28/3.52  fof(f2,axiom,(
% 23.28/3.52    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f17,plain,(
% 23.28/3.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 23.28/3.52    inference(cnf_transformation,[],[f2])).
% 23.28/3.52  
% 23.28/3.52  fof(f28,plain,(
% 23.28/3.52    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) )),
% 23.28/3.52    inference(definition_unfolding,[],[f25,f17,f17,f17,f17])).
% 23.28/3.52  
% 23.28/3.52  fof(f3,axiom,(
% 23.28/3.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f18,plain,(
% 23.28/3.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.28/3.52    inference(cnf_transformation,[],[f3])).
% 23.28/3.52  
% 23.28/3.52  fof(f5,axiom,(
% 23.28/3.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f20,plain,(
% 23.28/3.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.28/3.52    inference(cnf_transformation,[],[f5])).
% 23.28/3.52  
% 23.28/3.52  fof(f11,conjecture,(
% 23.28/3.52    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.28/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.52  
% 23.28/3.52  fof(f12,negated_conjecture,(
% 23.28/3.52    ~! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.28/3.52    inference(negated_conjecture,[],[f11])).
% 23.28/3.52  
% 23.28/3.52  fof(f13,plain,(
% 23.28/3.52    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)),
% 23.28/3.52    inference(ennf_transformation,[],[f12])).
% 23.28/3.52  
% 23.28/3.52  fof(f14,plain,(
% 23.28/3.52    ? [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) => k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 23.28/3.52    introduced(choice_axiom,[])).
% 23.28/3.52  
% 23.28/3.52  fof(f15,plain,(
% 23.28/3.52    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 23.28/3.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 23.28/3.52  
% 23.28/3.52  fof(f26,plain,(
% 23.28/3.52    k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1)),
% 23.28/3.52    inference(cnf_transformation,[],[f15])).
% 23.28/3.52  
% 23.28/3.52  fof(f29,plain,(
% 23.28/3.52    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 23.28/3.52    inference(definition_unfolding,[],[f26,f17,f17,f23])).
% 23.28/3.52  
% 23.28/3.52  cnf(c_6,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 23.28/3.52      inference(cnf_transformation,[],[f27]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_4,plain,
% 23.28/3.52      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 23.28/3.52      inference(cnf_transformation,[],[f21]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_2,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 23.28/3.52      inference(cnf_transformation,[],[f19]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_45,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_48,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_45,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_467,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_6,c_48]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_0,plain,
% 23.28/3.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 23.28/3.52      inference(cnf_transformation,[],[f16]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_84,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_483,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_467,c_84]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_41,plain,
% 23.28/3.52      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_5,plain,
% 23.28/3.52      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.28/3.52      inference(cnf_transformation,[],[f22]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_62,plain,
% 23.28/3.52      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_41,c_5]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_68,plain,
% 23.28/3.52      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 23.28/3.52      inference(demodulation,[status(thm)],[c_62,c_5]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_2269,plain,
% 23.28/3.52      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X1)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X0),X1) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_483,c_68]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_2357,plain,
% 23.28/3.52      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 23.28/3.52      inference(demodulation,[status(thm)],[c_2269,c_483]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_7,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) ),
% 23.28/3.52      inference(cnf_transformation,[],[f28]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_8739,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_2357,c_7]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_1,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.28/3.52      inference(cnf_transformation,[],[f18]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_28,plain,
% 23.28/3.52      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_44,plain,
% 23.28/3.52      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_28,c_4]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_3,plain,
% 23.28/3.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.28/3.52      inference(cnf_transformation,[],[f20]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_78,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_222,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_44,c_78]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_256,plain,
% 23.28/3.52      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_222,c_6]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_258,plain,
% 23.28/3.52      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.28/3.52      inference(demodulation,[status(thm)],[c_256,c_44]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_8761,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1),k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_8739,c_258]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_53,plain,
% 23.28/3.52      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_2,c_41]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_57,plain,
% 23.28/3.52      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 23.28/3.52      inference(demodulation,[status(thm)],[c_53,c_41]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_197,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X0)) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_44,c_7]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_213,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X0,X0)))) ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_197,c_3]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_141,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_3,c_7]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_168,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),X1),k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))) ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_141,c_3]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_169,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1),k4_xboole_0(X1,k2_xboole_0(X0,k1_xboole_0))) ),
% 23.28/3.52      inference(demodulation,[status(thm)],[c_168,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_170,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1),X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_169,c_1]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_214,plain,
% 23.28/3.52      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X1),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 23.28/3.52      inference(demodulation,[status(thm)],[c_213,c_2,c_3,c_170]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_63,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_5,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_54,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_41,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_56,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_54,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_495,plain,
% 23.28/3.52      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_56,c_48]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_199,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_44,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_212,plain,
% 23.28/3.52      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 23.28/3.52      inference(light_normalisation,[status(thm)],[c_199,c_1]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_235,plain,
% 23.28/3.52      ( k2_xboole_0(X0,X0) = X0 ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_212,c_2]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_497,plain,
% 23.28/3.52      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 23.28/3.52      inference(demodulation,[status(thm)],[c_495,c_235]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_1110,plain,
% 23.28/3.52      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_0,c_497]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_1678,plain,
% 23.28/3.52      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X0) ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_63,c_1110]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_305,plain,
% 23.28/3.52      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.28/3.52      inference(superposition,[status(thm)],[c_258,c_5]) ).
% 23.28/3.52  
% 23.28/3.52  cnf(c_314,plain,
% 23.28/3.53      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_305,c_2]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_336,plain,
% 23.28/3.53      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_314,c_2]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_354,plain,
% 23.28/3.53      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_336,c_1]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_801,plain,
% 23.28/3.53      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_63,c_354]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_820,plain,
% 23.28/3.53      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_801,c_63]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_1725,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_1678,c_820]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_8762,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 23.28/3.53      inference(demodulation,
% 23.28/3.53                [status(thm)],
% 23.28/3.53                [c_8761,c_3,c_28,c_57,c_214,c_256,c_1725]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_329,plain,
% 23.28/3.53      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_6,c_314]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_431,plain,
% 23.28/3.53      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_329,c_5]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_439,plain,
% 23.28/3.53      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_431,c_5,c_256]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_859,plain,
% 23.28/3.53      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_0,c_439]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_748,plain,
% 23.28/3.53      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_0,c_354]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_973,plain,
% 23.28/3.53      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_2,c_748]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_1013,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_973,c_748]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_1474,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,X0)) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_859,c_1013]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_1514,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_1474,c_28]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_6093,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_0,c_1514]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_9899,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_8762,c_6093]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_9927,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_9899,c_5,c_483]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_80,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_87,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_80,c_5]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_790,plain,
% 23.28/3.53      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_0,c_63]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_14370,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_87,c_790]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_14409,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_9927,c_14370]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_14849,plain,
% 23.28/3.53      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_14409,c_258]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_488,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_6,c_56]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_502,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_488,c_6]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_14850,plain,
% 23.28/3.53      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_14849,c_28,c_502]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_800,plain,
% 23.28/3.53      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_483,c_63]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_821,plain,
% 23.28/3.53      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_800,c_2]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_3733,plain,
% 23.28/3.53      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_821,c_41]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_3773,plain,
% 23.28/3.53      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_3733,c_5,c_41]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_9822,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = X0 ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_4,c_8762]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_10009,plain,
% 23.28/3.53      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = X1 ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_9822,c_314]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_43,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_358,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_0,c_43]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_10010,plain,
% 23.28/3.53      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_10009,c_28,c_358]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_10482,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_10010,c_43]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_11037,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X1,X0)) = X0 ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_3773,c_10482]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_550,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_41,c_483]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_3350,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_0,c_550]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_5781,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_3773,c_3350]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_548,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_4,c_483]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_2886,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_497,c_548]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_2938,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_2886,c_41,c_748]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_3741,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_821,c_48]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_3765,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,X0) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_3741,c_1514]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_5851,plain,
% 23.28/3.53      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_5781,c_2938,c_3765]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_11126,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_11037,c_5851]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_28345,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_14850,c_11126]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_9879,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_8762,c_354]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_9940,plain,
% 23.28/3.53      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_9879,c_8762]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_28468,plain,
% 23.28/3.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.28/3.53      inference(light_normalisation,[status(thm)],[c_28345,c_9940]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_11483,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_11126,c_5]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_8,negated_conjecture,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.53      inference(cnf_transformation,[],[f29]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_27,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_59417,plain,
% 23.28/3.53      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_11483,c_27]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_65,plain,
% 23.28/3.53      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_66,plain,
% 23.28/3.53      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_65,c_5]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_304,plain,
% 23.28/3.53      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_258,c_5]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_315,plain,
% 23.28/3.53      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_304,c_256]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_1605,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_66,c_315]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_6513,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_84,c_1605]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_16894,plain,
% 23.28/3.53      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_1013,c_6513]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_59418,plain,
% 23.28/3.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.53      inference(demodulation,[status(thm)],[c_59417,c_1,c_16894]) ).
% 23.28/3.53  
% 23.28/3.53  cnf(c_60177,plain,
% 23.28/3.53      ( $false ),
% 23.28/3.53      inference(superposition,[status(thm)],[c_28468,c_59418]) ).
% 23.28/3.53  
% 23.28/3.53  
% 23.28/3.53  % SZS output end CNFRefutation for theBenchmark.p
% 23.28/3.53  
% 23.28/3.53  ------                               Statistics
% 23.28/3.53  
% 23.28/3.53  ------ General
% 23.28/3.53  
% 23.28/3.53  abstr_ref_over_cycles:                  0
% 23.28/3.53  abstr_ref_under_cycles:                 0
% 23.28/3.53  gc_basic_clause_elim:                   0
% 23.28/3.53  forced_gc_time:                         0
% 23.28/3.53  parsing_time:                           0.008
% 23.28/3.53  unif_index_cands_time:                  0.
% 23.28/3.53  unif_index_add_time:                    0.
% 23.28/3.53  orderings_time:                         0.
% 23.28/3.53  out_proof_time:                         0.008
% 23.28/3.53  total_time:                             2.67
% 23.28/3.53  num_of_symbols:                         37
% 23.28/3.53  num_of_terms:                           110707
% 23.28/3.53  
% 23.28/3.53  ------ Preprocessing
% 23.28/3.53  
% 23.28/3.53  num_of_splits:                          0
% 23.28/3.53  num_of_split_atoms:                     1
% 23.28/3.53  num_of_reused_defs:                     0
% 23.28/3.53  num_eq_ax_congr_red:                    0
% 23.28/3.53  num_of_sem_filtered_clauses:            0
% 23.28/3.53  num_of_subtypes:                        0
% 23.28/3.53  monotx_restored_types:                  0
% 23.28/3.53  sat_num_of_epr_types:                   0
% 23.28/3.53  sat_num_of_non_cyclic_types:            0
% 23.28/3.53  sat_guarded_non_collapsed_types:        0
% 23.28/3.53  num_pure_diseq_elim:                    0
% 23.28/3.53  simp_replaced_by:                       0
% 23.28/3.53  res_preprocessed:                       22
% 23.28/3.53  prep_upred:                             0
% 23.28/3.53  prep_unflattend:                        0
% 23.28/3.53  smt_new_axioms:                         0
% 23.28/3.53  pred_elim_cands:                        0
% 23.28/3.53  pred_elim:                              0
% 23.28/3.53  pred_elim_cl:                           0
% 23.28/3.53  pred_elim_cycles:                       0
% 23.28/3.53  merged_defs:                            0
% 23.28/3.53  merged_defs_ncl:                        0
% 23.28/3.53  bin_hyper_res:                          0
% 23.28/3.53  prep_cycles:                            2
% 23.28/3.53  pred_elim_time:                         0.
% 23.28/3.53  splitting_time:                         0.
% 23.28/3.53  sem_filter_time:                        0.
% 23.28/3.53  monotx_time:                            0.
% 23.28/3.53  subtype_inf_time:                       0.
% 23.28/3.53  
% 23.28/3.53  ------ Problem properties
% 23.28/3.53  
% 23.28/3.53  clauses:                                9
% 23.28/3.53  conjectures:                            1
% 23.28/3.53  epr:                                    0
% 23.28/3.53  horn:                                   9
% 23.28/3.53  ground:                                 1
% 23.28/3.53  unary:                                  9
% 23.28/3.53  binary:                                 0
% 23.28/3.53  lits:                                   9
% 23.28/3.53  lits_eq:                                9
% 23.28/3.53  fd_pure:                                0
% 23.28/3.53  fd_pseudo:                              0
% 23.28/3.53  fd_cond:                                0
% 23.28/3.53  fd_pseudo_cond:                         0
% 23.28/3.53  ac_symbols:                             1
% 23.28/3.53  
% 23.28/3.53  ------ Propositional Solver
% 23.28/3.53  
% 23.28/3.53  prop_solver_calls:                      13
% 23.28/3.53  prop_fast_solver_calls:                 56
% 23.28/3.53  smt_solver_calls:                       0
% 23.28/3.53  smt_fast_solver_calls:                  0
% 23.28/3.53  prop_num_of_clauses:                    333
% 23.28/3.53  prop_preprocess_simplified:             377
% 23.28/3.53  prop_fo_subsumed:                       0
% 23.28/3.53  prop_solver_time:                       0.
% 23.28/3.53  smt_solver_time:                        0.
% 23.28/3.53  smt_fast_solver_time:                   0.
% 23.28/3.53  prop_fast_solver_time:                  0.
% 23.28/3.53  prop_unsat_core_time:                   0.
% 23.28/3.53  
% 23.28/3.53  ------ QBF
% 23.28/3.53  
% 23.28/3.53  qbf_q_res:                              0
% 23.28/3.53  qbf_num_tautologies:                    0
% 23.28/3.53  qbf_prep_cycles:                        0
% 23.28/3.53  
% 23.28/3.53  ------ BMC1
% 23.28/3.53  
% 23.28/3.53  bmc1_current_bound:                     -1
% 23.28/3.53  bmc1_last_solved_bound:                 -1
% 23.28/3.53  bmc1_unsat_core_size:                   -1
% 23.28/3.53  bmc1_unsat_core_parents_size:           -1
% 23.28/3.53  bmc1_merge_next_fun:                    0
% 23.28/3.53  bmc1_unsat_core_clauses_time:           0.
% 23.28/3.53  
% 23.28/3.53  ------ Instantiation
% 23.28/3.53  
% 23.28/3.53  inst_num_of_clauses:                    0
% 23.28/3.53  inst_num_in_passive:                    0
% 23.28/3.53  inst_num_in_active:                     0
% 23.28/3.53  inst_num_in_unprocessed:                0
% 23.28/3.53  inst_num_of_loops:                      0
% 23.28/3.53  inst_num_of_learning_restarts:          0
% 23.28/3.53  inst_num_moves_active_passive:          0
% 23.28/3.53  inst_lit_activity:                      0
% 23.28/3.53  inst_lit_activity_moves:                0
% 23.28/3.53  inst_num_tautologies:                   0
% 23.28/3.53  inst_num_prop_implied:                  0
% 23.28/3.53  inst_num_existing_simplified:           0
% 23.28/3.53  inst_num_eq_res_simplified:             0
% 23.28/3.53  inst_num_child_elim:                    0
% 23.28/3.53  inst_num_of_dismatching_blockings:      0
% 23.28/3.53  inst_num_of_non_proper_insts:           0
% 23.28/3.53  inst_num_of_duplicates:                 0
% 23.28/3.53  inst_inst_num_from_inst_to_res:         0
% 23.28/3.53  inst_dismatching_checking_time:         0.
% 23.28/3.53  
% 23.28/3.53  ------ Resolution
% 23.28/3.53  
% 23.28/3.53  res_num_of_clauses:                     0
% 23.28/3.53  res_num_in_passive:                     0
% 23.28/3.53  res_num_in_active:                      0
% 23.28/3.53  res_num_of_loops:                       24
% 23.28/3.53  res_forward_subset_subsumed:            0
% 23.28/3.53  res_backward_subset_subsumed:           0
% 23.28/3.53  res_forward_subsumed:                   0
% 23.28/3.53  res_backward_subsumed:                  0
% 23.28/3.53  res_forward_subsumption_resolution:     0
% 23.28/3.53  res_backward_subsumption_resolution:    0
% 23.28/3.53  res_clause_to_clause_subsumption:       221668
% 23.28/3.53  res_orphan_elimination:                 0
% 23.28/3.53  res_tautology_del:                      0
% 23.28/3.53  res_num_eq_res_simplified:              0
% 23.28/3.53  res_num_sel_changes:                    0
% 23.28/3.53  res_moves_from_active_to_pass:          0
% 23.28/3.53  
% 23.28/3.53  ------ Superposition
% 23.28/3.53  
% 23.28/3.53  sup_time_total:                         0.
% 23.28/3.53  sup_time_generating:                    0.
% 23.28/3.53  sup_time_sim_full:                      0.
% 23.28/3.53  sup_time_sim_immed:                     0.
% 23.28/3.53  
% 23.28/3.53  sup_num_of_clauses:                     6447
% 23.28/3.53  sup_num_in_active:                      173
% 23.28/3.53  sup_num_in_passive:                     6274
% 23.28/3.53  sup_num_of_loops:                       200
% 23.28/3.53  sup_fw_superposition:                   21054
% 23.28/3.53  sup_bw_superposition:                   16719
% 23.28/3.53  sup_immediate_simplified:               18019
% 23.28/3.53  sup_given_eliminated:                   6
% 23.28/3.53  comparisons_done:                       0
% 23.28/3.53  comparisons_avoided:                    0
% 23.28/3.53  
% 23.28/3.53  ------ Simplifications
% 23.28/3.53  
% 23.28/3.53  
% 23.28/3.53  sim_fw_subset_subsumed:                 0
% 23.28/3.53  sim_bw_subset_subsumed:                 0
% 23.28/3.53  sim_fw_subsumed:                        2331
% 23.28/3.53  sim_bw_subsumed:                        63
% 23.28/3.53  sim_fw_subsumption_res:                 0
% 23.28/3.53  sim_bw_subsumption_res:                 0
% 23.28/3.53  sim_tautology_del:                      0
% 23.28/3.53  sim_eq_tautology_del:                   5072
% 23.28/3.53  sim_eq_res_simp:                        0
% 23.28/3.53  sim_fw_demodulated:                     14537
% 23.28/3.53  sim_bw_demodulated:                     176
% 23.28/3.53  sim_light_normalised:                   7331
% 23.28/3.53  sim_joinable_taut:                      317
% 23.28/3.53  sim_joinable_simp:                      0
% 23.28/3.53  sim_ac_normalised:                      0
% 23.28/3.53  sim_smt_subsumption:                    0
% 23.28/3.53  
%------------------------------------------------------------------------------
