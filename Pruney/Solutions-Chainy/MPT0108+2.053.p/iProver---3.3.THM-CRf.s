%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:35 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :   90 (2503 expanded)
%              Number of clauses        :   59 ( 791 expanded)
%              Number of leaves         :   12 ( 741 expanded)
%              Depth                    :   25
%              Number of atoms          :   91 (2504 expanded)
%              Number of equality atoms :   90 (2503 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f25,f17])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f21,f17,f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f17,f27])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f22,f17,f17])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_23,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_4,c_1,c_0])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_24,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_2,c_1,c_0])).

cnf(c_32,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23,c_24])).

cnf(c_59,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_32])).

cnf(c_57,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_32,c_7])).

cnf(c_99,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_32,c_57])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_111,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_99,c_6])).

cnf(c_112,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_111,c_57])).

cnf(c_160,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_59,c_112])).

cnf(c_170,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_160,c_6])).

cnf(c_181,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_170,c_112])).

cnf(c_186,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_181])).

cnf(c_263,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_24])).

cnf(c_3039,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_186,c_263])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_1,c_0])).

cnf(c_53,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7,c_21])).

cnf(c_22606,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3039,c_53])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_266,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_24])).

cnf(c_280,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_266,c_6,c_111])).

cnf(c_290,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_280,c_1])).

cnf(c_33,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_365,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_280,c_33])).

cnf(c_499,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_290,c_365])).

cnf(c_301,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_290])).

cnf(c_510,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_365,c_301])).

cnf(c_329,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_290,c_301])).

cnf(c_347,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_329,c_280])).

cnf(c_444,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_347])).

cnf(c_530,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_510,c_444])).

cnf(c_540,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_499,c_530])).

cnf(c_1275,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_24,c_540])).

cnf(c_1352,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1275,c_280])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_22,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0])).

cnf(c_75,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(superposition,[status(thm)],[c_22,c_7])).

cnf(c_13873,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
    inference(superposition,[status(thm)],[c_1352,c_75])).

cnf(c_13903,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1352,c_1])).

cnf(c_14013,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_13873,c_13903])).

cnf(c_61,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_22])).

cnf(c_1674,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_24,c_61])).

cnf(c_34,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_810,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_24,c_34])).

cnf(c_1809,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1674,c_810])).

cnf(c_14014,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_14013,c_1809])).

cnf(c_22607,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_22606,c_14014])).

cnf(c_514,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_365,c_22])).

cnf(c_337,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_301,c_22])).

cnf(c_341,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_337,c_32])).

cnf(c_528,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_514,c_341])).

cnf(c_22608,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_22607,c_6,c_528])).

cnf(c_22609,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22608])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.44/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/1.52  
% 7.44/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.44/1.52  
% 7.44/1.52  ------  iProver source info
% 7.44/1.52  
% 7.44/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.44/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.44/1.52  git: non_committed_changes: false
% 7.44/1.52  git: last_make_outside_of_git: false
% 7.44/1.52  
% 7.44/1.52  ------ 
% 7.44/1.52  
% 7.44/1.52  ------ Input Options
% 7.44/1.52  
% 7.44/1.52  --out_options                           all
% 7.44/1.52  --tptp_safe_out                         true
% 7.44/1.52  --problem_path                          ""
% 7.44/1.52  --include_path                          ""
% 7.44/1.52  --clausifier                            res/vclausify_rel
% 7.44/1.52  --clausifier_options                    --mode clausify
% 7.44/1.52  --stdin                                 false
% 7.44/1.52  --stats_out                             all
% 7.44/1.52  
% 7.44/1.52  ------ General Options
% 7.44/1.52  
% 7.44/1.52  --fof                                   false
% 7.44/1.52  --time_out_real                         305.
% 7.44/1.52  --time_out_virtual                      -1.
% 7.44/1.52  --symbol_type_check                     false
% 7.44/1.52  --clausify_out                          false
% 7.44/1.52  --sig_cnt_out                           false
% 7.44/1.52  --trig_cnt_out                          false
% 7.44/1.52  --trig_cnt_out_tolerance                1.
% 7.44/1.52  --trig_cnt_out_sk_spl                   false
% 7.44/1.52  --abstr_cl_out                          false
% 7.44/1.52  
% 7.44/1.52  ------ Global Options
% 7.44/1.52  
% 7.44/1.52  --schedule                              default
% 7.44/1.52  --add_important_lit                     false
% 7.44/1.52  --prop_solver_per_cl                    1000
% 7.44/1.52  --min_unsat_core                        false
% 7.44/1.52  --soft_assumptions                      false
% 7.44/1.52  --soft_lemma_size                       3
% 7.44/1.52  --prop_impl_unit_size                   0
% 7.44/1.52  --prop_impl_unit                        []
% 7.44/1.52  --share_sel_clauses                     true
% 7.44/1.52  --reset_solvers                         false
% 7.44/1.52  --bc_imp_inh                            [conj_cone]
% 7.44/1.52  --conj_cone_tolerance                   3.
% 7.44/1.52  --extra_neg_conj                        none
% 7.44/1.52  --large_theory_mode                     true
% 7.44/1.52  --prolific_symb_bound                   200
% 7.44/1.52  --lt_threshold                          2000
% 7.44/1.52  --clause_weak_htbl                      true
% 7.44/1.52  --gc_record_bc_elim                     false
% 7.44/1.52  
% 7.44/1.52  ------ Preprocessing Options
% 7.44/1.52  
% 7.44/1.52  --preprocessing_flag                    true
% 7.44/1.52  --time_out_prep_mult                    0.1
% 7.44/1.52  --splitting_mode                        input
% 7.44/1.52  --splitting_grd                         true
% 7.44/1.52  --splitting_cvd                         false
% 7.44/1.52  --splitting_cvd_svl                     false
% 7.44/1.52  --splitting_nvd                         32
% 7.44/1.52  --sub_typing                            true
% 7.44/1.52  --prep_gs_sim                           true
% 7.44/1.52  --prep_unflatten                        true
% 7.44/1.52  --prep_res_sim                          true
% 7.44/1.52  --prep_upred                            true
% 7.44/1.52  --prep_sem_filter                       exhaustive
% 7.44/1.52  --prep_sem_filter_out                   false
% 7.44/1.52  --pred_elim                             true
% 7.44/1.52  --res_sim_input                         true
% 7.44/1.52  --eq_ax_congr_red                       true
% 7.44/1.52  --pure_diseq_elim                       true
% 7.44/1.52  --brand_transform                       false
% 7.44/1.52  --non_eq_to_eq                          false
% 7.44/1.52  --prep_def_merge                        true
% 7.44/1.52  --prep_def_merge_prop_impl              false
% 7.44/1.52  --prep_def_merge_mbd                    true
% 7.44/1.52  --prep_def_merge_tr_red                 false
% 7.44/1.52  --prep_def_merge_tr_cl                  false
% 7.44/1.52  --smt_preprocessing                     true
% 7.44/1.52  --smt_ac_axioms                         fast
% 7.44/1.52  --preprocessed_out                      false
% 7.44/1.52  --preprocessed_stats                    false
% 7.44/1.52  
% 7.44/1.52  ------ Abstraction refinement Options
% 7.44/1.52  
% 7.44/1.52  --abstr_ref                             []
% 7.44/1.52  --abstr_ref_prep                        false
% 7.44/1.52  --abstr_ref_until_sat                   false
% 7.44/1.52  --abstr_ref_sig_restrict                funpre
% 7.44/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.52  --abstr_ref_under                       []
% 7.44/1.52  
% 7.44/1.52  ------ SAT Options
% 7.44/1.52  
% 7.44/1.52  --sat_mode                              false
% 7.44/1.52  --sat_fm_restart_options                ""
% 7.44/1.52  --sat_gr_def                            false
% 7.44/1.52  --sat_epr_types                         true
% 7.44/1.52  --sat_non_cyclic_types                  false
% 7.44/1.52  --sat_finite_models                     false
% 7.44/1.52  --sat_fm_lemmas                         false
% 7.44/1.52  --sat_fm_prep                           false
% 7.44/1.52  --sat_fm_uc_incr                        true
% 7.44/1.52  --sat_out_model                         small
% 7.44/1.52  --sat_out_clauses                       false
% 7.44/1.52  
% 7.44/1.52  ------ QBF Options
% 7.44/1.52  
% 7.44/1.52  --qbf_mode                              false
% 7.44/1.52  --qbf_elim_univ                         false
% 7.44/1.52  --qbf_dom_inst                          none
% 7.44/1.52  --qbf_dom_pre_inst                      false
% 7.44/1.52  --qbf_sk_in                             false
% 7.44/1.52  --qbf_pred_elim                         true
% 7.44/1.52  --qbf_split                             512
% 7.44/1.52  
% 7.44/1.52  ------ BMC1 Options
% 7.44/1.52  
% 7.44/1.52  --bmc1_incremental                      false
% 7.44/1.52  --bmc1_axioms                           reachable_all
% 7.44/1.52  --bmc1_min_bound                        0
% 7.44/1.52  --bmc1_max_bound                        -1
% 7.44/1.52  --bmc1_max_bound_default                -1
% 7.44/1.52  --bmc1_symbol_reachability              true
% 7.44/1.52  --bmc1_property_lemmas                  false
% 7.44/1.52  --bmc1_k_induction                      false
% 7.44/1.52  --bmc1_non_equiv_states                 false
% 7.44/1.52  --bmc1_deadlock                         false
% 7.44/1.52  --bmc1_ucm                              false
% 7.44/1.52  --bmc1_add_unsat_core                   none
% 7.44/1.52  --bmc1_unsat_core_children              false
% 7.44/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.52  --bmc1_out_stat                         full
% 7.44/1.52  --bmc1_ground_init                      false
% 7.44/1.52  --bmc1_pre_inst_next_state              false
% 7.44/1.52  --bmc1_pre_inst_state                   false
% 7.44/1.52  --bmc1_pre_inst_reach_state             false
% 7.44/1.52  --bmc1_out_unsat_core                   false
% 7.44/1.52  --bmc1_aig_witness_out                  false
% 7.44/1.52  --bmc1_verbose                          false
% 7.44/1.52  --bmc1_dump_clauses_tptp                false
% 7.44/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.52  --bmc1_dump_file                        -
% 7.44/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.52  --bmc1_ucm_extend_mode                  1
% 7.44/1.52  --bmc1_ucm_init_mode                    2
% 7.44/1.52  --bmc1_ucm_cone_mode                    none
% 7.44/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.52  --bmc1_ucm_relax_model                  4
% 7.44/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.52  --bmc1_ucm_layered_model                none
% 7.44/1.52  --bmc1_ucm_max_lemma_size               10
% 7.44/1.52  
% 7.44/1.52  ------ AIG Options
% 7.44/1.52  
% 7.44/1.52  --aig_mode                              false
% 7.44/1.52  
% 7.44/1.52  ------ Instantiation Options
% 7.44/1.52  
% 7.44/1.52  --instantiation_flag                    true
% 7.44/1.52  --inst_sos_flag                         false
% 7.44/1.52  --inst_sos_phase                        true
% 7.44/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.52  --inst_lit_sel_side                     num_symb
% 7.44/1.52  --inst_solver_per_active                1400
% 7.44/1.52  --inst_solver_calls_frac                1.
% 7.44/1.52  --inst_passive_queue_type               priority_queues
% 7.44/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.52  --inst_passive_queues_freq              [25;2]
% 7.44/1.52  --inst_dismatching                      true
% 7.44/1.52  --inst_eager_unprocessed_to_passive     true
% 7.44/1.52  --inst_prop_sim_given                   true
% 7.44/1.52  --inst_prop_sim_new                     false
% 7.44/1.52  --inst_subs_new                         false
% 7.44/1.52  --inst_eq_res_simp                      false
% 7.44/1.52  --inst_subs_given                       false
% 7.44/1.52  --inst_orphan_elimination               true
% 7.44/1.52  --inst_learning_loop_flag               true
% 7.44/1.52  --inst_learning_start                   3000
% 7.44/1.52  --inst_learning_factor                  2
% 7.44/1.52  --inst_start_prop_sim_after_learn       3
% 7.44/1.52  --inst_sel_renew                        solver
% 7.44/1.52  --inst_lit_activity_flag                true
% 7.44/1.52  --inst_restr_to_given                   false
% 7.44/1.52  --inst_activity_threshold               500
% 7.44/1.52  --inst_out_proof                        true
% 7.44/1.52  
% 7.44/1.52  ------ Resolution Options
% 7.44/1.52  
% 7.44/1.52  --resolution_flag                       true
% 7.44/1.52  --res_lit_sel                           adaptive
% 7.44/1.52  --res_lit_sel_side                      none
% 7.44/1.52  --res_ordering                          kbo
% 7.44/1.52  --res_to_prop_solver                    active
% 7.44/1.52  --res_prop_simpl_new                    false
% 7.44/1.52  --res_prop_simpl_given                  true
% 7.44/1.52  --res_passive_queue_type                priority_queues
% 7.44/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.52  --res_passive_queues_freq               [15;5]
% 7.44/1.52  --res_forward_subs                      full
% 7.44/1.52  --res_backward_subs                     full
% 7.44/1.52  --res_forward_subs_resolution           true
% 7.44/1.52  --res_backward_subs_resolution          true
% 7.44/1.52  --res_orphan_elimination                true
% 7.44/1.52  --res_time_limit                        2.
% 7.44/1.52  --res_out_proof                         true
% 7.44/1.52  
% 7.44/1.52  ------ Superposition Options
% 7.44/1.52  
% 7.44/1.52  --superposition_flag                    true
% 7.44/1.52  --sup_passive_queue_type                priority_queues
% 7.44/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.52  --demod_completeness_check              fast
% 7.44/1.52  --demod_use_ground                      true
% 7.44/1.52  --sup_to_prop_solver                    passive
% 7.44/1.52  --sup_prop_simpl_new                    true
% 7.44/1.52  --sup_prop_simpl_given                  true
% 7.44/1.52  --sup_fun_splitting                     false
% 7.44/1.52  --sup_smt_interval                      50000
% 7.44/1.52  
% 7.44/1.52  ------ Superposition Simplification Setup
% 7.44/1.52  
% 7.44/1.52  --sup_indices_passive                   []
% 7.44/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.52  --sup_full_bw                           [BwDemod]
% 7.44/1.52  --sup_immed_triv                        [TrivRules]
% 7.44/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.52  --sup_immed_bw_main                     []
% 7.44/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.52  
% 7.44/1.52  ------ Combination Options
% 7.44/1.52  
% 7.44/1.52  --comb_res_mult                         3
% 7.44/1.52  --comb_sup_mult                         2
% 7.44/1.52  --comb_inst_mult                        10
% 7.44/1.52  
% 7.44/1.52  ------ Debug Options
% 7.44/1.52  
% 7.44/1.52  --dbg_backtrace                         false
% 7.44/1.52  --dbg_dump_prop_clauses                 false
% 7.44/1.52  --dbg_dump_prop_clauses_file            -
% 7.44/1.52  --dbg_out_stat                          false
% 7.44/1.52  ------ Parsing...
% 7.44/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.44/1.52  
% 7.44/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.44/1.52  
% 7.44/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.44/1.52  
% 7.44/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.44/1.52  ------ Proving...
% 7.44/1.52  ------ Problem Properties 
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  clauses                                 9
% 7.44/1.52  conjectures                             1
% 7.44/1.52  EPR                                     0
% 7.44/1.52  Horn                                    9
% 7.44/1.52  unary                                   9
% 7.44/1.52  binary                                  0
% 7.44/1.52  lits                                    9
% 7.44/1.52  lits eq                                 9
% 7.44/1.52  fd_pure                                 0
% 7.44/1.52  fd_pseudo                               0
% 7.44/1.52  fd_cond                                 0
% 7.44/1.52  fd_pseudo_cond                          0
% 7.44/1.52  AC symbols                              1
% 7.44/1.52  
% 7.44/1.52  ------ Schedule UEQ
% 7.44/1.52  
% 7.44/1.52  ------ pure equality problem: resolution off 
% 7.44/1.52  
% 7.44/1.52  ------ Option_UEQ Time Limit: Unbounded
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  ------ 
% 7.44/1.52  Current options:
% 7.44/1.52  ------ 
% 7.44/1.52  
% 7.44/1.52  ------ Input Options
% 7.44/1.52  
% 7.44/1.52  --out_options                           all
% 7.44/1.52  --tptp_safe_out                         true
% 7.44/1.52  --problem_path                          ""
% 7.44/1.52  --include_path                          ""
% 7.44/1.52  --clausifier                            res/vclausify_rel
% 7.44/1.52  --clausifier_options                    --mode clausify
% 7.44/1.52  --stdin                                 false
% 7.44/1.52  --stats_out                             all
% 7.44/1.52  
% 7.44/1.52  ------ General Options
% 7.44/1.52  
% 7.44/1.52  --fof                                   false
% 7.44/1.52  --time_out_real                         305.
% 7.44/1.52  --time_out_virtual                      -1.
% 7.44/1.52  --symbol_type_check                     false
% 7.44/1.52  --clausify_out                          false
% 7.44/1.52  --sig_cnt_out                           false
% 7.44/1.52  --trig_cnt_out                          false
% 7.44/1.52  --trig_cnt_out_tolerance                1.
% 7.44/1.52  --trig_cnt_out_sk_spl                   false
% 7.44/1.52  --abstr_cl_out                          false
% 7.44/1.52  
% 7.44/1.52  ------ Global Options
% 7.44/1.52  
% 7.44/1.52  --schedule                              default
% 7.44/1.52  --add_important_lit                     false
% 7.44/1.52  --prop_solver_per_cl                    1000
% 7.44/1.52  --min_unsat_core                        false
% 7.44/1.52  --soft_assumptions                      false
% 7.44/1.52  --soft_lemma_size                       3
% 7.44/1.52  --prop_impl_unit_size                   0
% 7.44/1.52  --prop_impl_unit                        []
% 7.44/1.52  --share_sel_clauses                     true
% 7.44/1.52  --reset_solvers                         false
% 7.44/1.52  --bc_imp_inh                            [conj_cone]
% 7.44/1.52  --conj_cone_tolerance                   3.
% 7.44/1.52  --extra_neg_conj                        none
% 7.44/1.52  --large_theory_mode                     true
% 7.44/1.52  --prolific_symb_bound                   200
% 7.44/1.52  --lt_threshold                          2000
% 7.44/1.52  --clause_weak_htbl                      true
% 7.44/1.52  --gc_record_bc_elim                     false
% 7.44/1.52  
% 7.44/1.52  ------ Preprocessing Options
% 7.44/1.52  
% 7.44/1.52  --preprocessing_flag                    true
% 7.44/1.52  --time_out_prep_mult                    0.1
% 7.44/1.52  --splitting_mode                        input
% 7.44/1.52  --splitting_grd                         true
% 7.44/1.52  --splitting_cvd                         false
% 7.44/1.52  --splitting_cvd_svl                     false
% 7.44/1.52  --splitting_nvd                         32
% 7.44/1.52  --sub_typing                            true
% 7.44/1.52  --prep_gs_sim                           true
% 7.44/1.52  --prep_unflatten                        true
% 7.44/1.52  --prep_res_sim                          true
% 7.44/1.52  --prep_upred                            true
% 7.44/1.52  --prep_sem_filter                       exhaustive
% 7.44/1.52  --prep_sem_filter_out                   false
% 7.44/1.52  --pred_elim                             true
% 7.44/1.52  --res_sim_input                         true
% 7.44/1.52  --eq_ax_congr_red                       true
% 7.44/1.52  --pure_diseq_elim                       true
% 7.44/1.52  --brand_transform                       false
% 7.44/1.52  --non_eq_to_eq                          false
% 7.44/1.52  --prep_def_merge                        true
% 7.44/1.52  --prep_def_merge_prop_impl              false
% 7.44/1.52  --prep_def_merge_mbd                    true
% 7.44/1.52  --prep_def_merge_tr_red                 false
% 7.44/1.52  --prep_def_merge_tr_cl                  false
% 7.44/1.52  --smt_preprocessing                     true
% 7.44/1.52  --smt_ac_axioms                         fast
% 7.44/1.52  --preprocessed_out                      false
% 7.44/1.52  --preprocessed_stats                    false
% 7.44/1.52  
% 7.44/1.52  ------ Abstraction refinement Options
% 7.44/1.52  
% 7.44/1.52  --abstr_ref                             []
% 7.44/1.52  --abstr_ref_prep                        false
% 7.44/1.52  --abstr_ref_until_sat                   false
% 7.44/1.52  --abstr_ref_sig_restrict                funpre
% 7.44/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.52  --abstr_ref_under                       []
% 7.44/1.52  
% 7.44/1.52  ------ SAT Options
% 7.44/1.52  
% 7.44/1.52  --sat_mode                              false
% 7.44/1.52  --sat_fm_restart_options                ""
% 7.44/1.52  --sat_gr_def                            false
% 7.44/1.52  --sat_epr_types                         true
% 7.44/1.52  --sat_non_cyclic_types                  false
% 7.44/1.52  --sat_finite_models                     false
% 7.44/1.52  --sat_fm_lemmas                         false
% 7.44/1.52  --sat_fm_prep                           false
% 7.44/1.52  --sat_fm_uc_incr                        true
% 7.44/1.52  --sat_out_model                         small
% 7.44/1.52  --sat_out_clauses                       false
% 7.44/1.52  
% 7.44/1.52  ------ QBF Options
% 7.44/1.52  
% 7.44/1.52  --qbf_mode                              false
% 7.44/1.52  --qbf_elim_univ                         false
% 7.44/1.52  --qbf_dom_inst                          none
% 7.44/1.52  --qbf_dom_pre_inst                      false
% 7.44/1.52  --qbf_sk_in                             false
% 7.44/1.52  --qbf_pred_elim                         true
% 7.44/1.52  --qbf_split                             512
% 7.44/1.52  
% 7.44/1.52  ------ BMC1 Options
% 7.44/1.52  
% 7.44/1.52  --bmc1_incremental                      false
% 7.44/1.52  --bmc1_axioms                           reachable_all
% 7.44/1.52  --bmc1_min_bound                        0
% 7.44/1.52  --bmc1_max_bound                        -1
% 7.44/1.52  --bmc1_max_bound_default                -1
% 7.44/1.52  --bmc1_symbol_reachability              true
% 7.44/1.52  --bmc1_property_lemmas                  false
% 7.44/1.52  --bmc1_k_induction                      false
% 7.44/1.52  --bmc1_non_equiv_states                 false
% 7.44/1.52  --bmc1_deadlock                         false
% 7.44/1.52  --bmc1_ucm                              false
% 7.44/1.52  --bmc1_add_unsat_core                   none
% 7.44/1.52  --bmc1_unsat_core_children              false
% 7.44/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.52  --bmc1_out_stat                         full
% 7.44/1.52  --bmc1_ground_init                      false
% 7.44/1.52  --bmc1_pre_inst_next_state              false
% 7.44/1.52  --bmc1_pre_inst_state                   false
% 7.44/1.52  --bmc1_pre_inst_reach_state             false
% 7.44/1.52  --bmc1_out_unsat_core                   false
% 7.44/1.52  --bmc1_aig_witness_out                  false
% 7.44/1.52  --bmc1_verbose                          false
% 7.44/1.52  --bmc1_dump_clauses_tptp                false
% 7.44/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.52  --bmc1_dump_file                        -
% 7.44/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.52  --bmc1_ucm_extend_mode                  1
% 7.44/1.52  --bmc1_ucm_init_mode                    2
% 7.44/1.52  --bmc1_ucm_cone_mode                    none
% 7.44/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.52  --bmc1_ucm_relax_model                  4
% 7.44/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.52  --bmc1_ucm_layered_model                none
% 7.44/1.52  --bmc1_ucm_max_lemma_size               10
% 7.44/1.52  
% 7.44/1.52  ------ AIG Options
% 7.44/1.52  
% 7.44/1.52  --aig_mode                              false
% 7.44/1.52  
% 7.44/1.52  ------ Instantiation Options
% 7.44/1.52  
% 7.44/1.52  --instantiation_flag                    false
% 7.44/1.52  --inst_sos_flag                         false
% 7.44/1.52  --inst_sos_phase                        true
% 7.44/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.52  --inst_lit_sel_side                     num_symb
% 7.44/1.52  --inst_solver_per_active                1400
% 7.44/1.52  --inst_solver_calls_frac                1.
% 7.44/1.52  --inst_passive_queue_type               priority_queues
% 7.44/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.52  --inst_passive_queues_freq              [25;2]
% 7.44/1.52  --inst_dismatching                      true
% 7.44/1.52  --inst_eager_unprocessed_to_passive     true
% 7.44/1.52  --inst_prop_sim_given                   true
% 7.44/1.52  --inst_prop_sim_new                     false
% 7.44/1.52  --inst_subs_new                         false
% 7.44/1.52  --inst_eq_res_simp                      false
% 7.44/1.52  --inst_subs_given                       false
% 7.44/1.52  --inst_orphan_elimination               true
% 7.44/1.52  --inst_learning_loop_flag               true
% 7.44/1.52  --inst_learning_start                   3000
% 7.44/1.52  --inst_learning_factor                  2
% 7.44/1.52  --inst_start_prop_sim_after_learn       3
% 7.44/1.52  --inst_sel_renew                        solver
% 7.44/1.52  --inst_lit_activity_flag                true
% 7.44/1.52  --inst_restr_to_given                   false
% 7.44/1.52  --inst_activity_threshold               500
% 7.44/1.52  --inst_out_proof                        true
% 7.44/1.52  
% 7.44/1.52  ------ Resolution Options
% 7.44/1.52  
% 7.44/1.52  --resolution_flag                       false
% 7.44/1.52  --res_lit_sel                           adaptive
% 7.44/1.52  --res_lit_sel_side                      none
% 7.44/1.52  --res_ordering                          kbo
% 7.44/1.52  --res_to_prop_solver                    active
% 7.44/1.52  --res_prop_simpl_new                    false
% 7.44/1.52  --res_prop_simpl_given                  true
% 7.44/1.52  --res_passive_queue_type                priority_queues
% 7.44/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.52  --res_passive_queues_freq               [15;5]
% 7.44/1.52  --res_forward_subs                      full
% 7.44/1.52  --res_backward_subs                     full
% 7.44/1.52  --res_forward_subs_resolution           true
% 7.44/1.52  --res_backward_subs_resolution          true
% 7.44/1.52  --res_orphan_elimination                true
% 7.44/1.52  --res_time_limit                        2.
% 7.44/1.52  --res_out_proof                         true
% 7.44/1.52  
% 7.44/1.52  ------ Superposition Options
% 7.44/1.52  
% 7.44/1.52  --superposition_flag                    true
% 7.44/1.52  --sup_passive_queue_type                priority_queues
% 7.44/1.52  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.52  --demod_completeness_check              fast
% 7.44/1.52  --demod_use_ground                      true
% 7.44/1.52  --sup_to_prop_solver                    active
% 7.44/1.52  --sup_prop_simpl_new                    false
% 7.44/1.52  --sup_prop_simpl_given                  false
% 7.44/1.52  --sup_fun_splitting                     true
% 7.44/1.52  --sup_smt_interval                      10000
% 7.44/1.52  
% 7.44/1.52  ------ Superposition Simplification Setup
% 7.44/1.52  
% 7.44/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.44/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.44/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.52  --sup_full_triv                         [TrivRules]
% 7.44/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.44/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.44/1.52  --sup_immed_triv                        [TrivRules]
% 7.44/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.52  --sup_immed_bw_main                     []
% 7.44/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.44/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.52  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.44/1.52  
% 7.44/1.52  ------ Combination Options
% 7.44/1.52  
% 7.44/1.52  --comb_res_mult                         1
% 7.44/1.52  --comb_sup_mult                         1
% 7.44/1.52  --comb_inst_mult                        1000000
% 7.44/1.52  
% 7.44/1.52  ------ Debug Options
% 7.44/1.52  
% 7.44/1.52  --dbg_backtrace                         false
% 7.44/1.52  --dbg_dump_prop_clauses                 false
% 7.44/1.52  --dbg_dump_prop_clauses_file            -
% 7.44/1.52  --dbg_out_stat                          false
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  ------ Proving...
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  % SZS status Theorem for theBenchmark.p
% 7.44/1.52  
% 7.44/1.52   Resolution empty clause
% 7.44/1.52  
% 7.44/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.44/1.52  
% 7.44/1.52  fof(f9,axiom,(
% 7.44/1.52    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f24,plain,(
% 7.44/1.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.44/1.52    inference(cnf_transformation,[],[f9])).
% 7.44/1.52  
% 7.44/1.52  fof(f6,axiom,(
% 7.44/1.52    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f21,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.44/1.52    inference(cnf_transformation,[],[f6])).
% 7.44/1.52  
% 7.44/1.52  fof(f10,axiom,(
% 7.44/1.52    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f25,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.44/1.52    inference(cnf_transformation,[],[f10])).
% 7.44/1.52  
% 7.44/1.52  fof(f2,axiom,(
% 7.44/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f17,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.44/1.52    inference(cnf_transformation,[],[f2])).
% 7.44/1.52  
% 7.44/1.52  fof(f27,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.44/1.52    inference(definition_unfolding,[],[f25,f17])).
% 7.44/1.52  
% 7.44/1.52  fof(f29,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 7.44/1.52    inference(definition_unfolding,[],[f21,f17,f27])).
% 7.44/1.52  
% 7.44/1.52  fof(f3,axiom,(
% 7.44/1.52    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f18,plain,(
% 7.44/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.44/1.52    inference(cnf_transformation,[],[f3])).
% 7.44/1.52  
% 7.44/1.52  fof(f1,axiom,(
% 7.44/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f16,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.44/1.52    inference(cnf_transformation,[],[f1])).
% 7.44/1.52  
% 7.44/1.52  fof(f4,axiom,(
% 7.44/1.52    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f19,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.44/1.52    inference(cnf_transformation,[],[f4])).
% 7.44/1.52  
% 7.44/1.52  fof(f28,plain,(
% 7.44/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 7.44/1.52    inference(definition_unfolding,[],[f19,f27])).
% 7.44/1.52  
% 7.44/1.52  fof(f8,axiom,(
% 7.44/1.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f23,plain,(
% 7.44/1.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.44/1.52    inference(cnf_transformation,[],[f8])).
% 7.44/1.52  
% 7.44/1.52  fof(f11,conjecture,(
% 7.44/1.52    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f12,negated_conjecture,(
% 7.44/1.52    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 7.44/1.52    inference(negated_conjecture,[],[f11])).
% 7.44/1.52  
% 7.44/1.52  fof(f13,plain,(
% 7.44/1.52    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 7.44/1.52    inference(ennf_transformation,[],[f12])).
% 7.44/1.52  
% 7.44/1.52  fof(f14,plain,(
% 7.44/1.52    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 7.44/1.52    introduced(choice_axiom,[])).
% 7.44/1.52  
% 7.44/1.52  fof(f15,plain,(
% 7.44/1.52    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 7.44/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 7.44/1.52  
% 7.44/1.52  fof(f26,plain,(
% 7.44/1.52    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 7.44/1.52    inference(cnf_transformation,[],[f15])).
% 7.44/1.52  
% 7.44/1.52  fof(f31,plain,(
% 7.44/1.52    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 7.44/1.52    inference(definition_unfolding,[],[f26,f17,f27])).
% 7.44/1.52  
% 7.44/1.52  fof(f5,axiom,(
% 7.44/1.52    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f20,plain,(
% 7.44/1.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.44/1.52    inference(cnf_transformation,[],[f5])).
% 7.44/1.52  
% 7.44/1.52  fof(f7,axiom,(
% 7.44/1.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.44/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.52  
% 7.44/1.52  fof(f22,plain,(
% 7.44/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.44/1.52    inference(cnf_transformation,[],[f7])).
% 7.44/1.52  
% 7.44/1.52  fof(f30,plain,(
% 7.44/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.44/1.52    inference(definition_unfolding,[],[f22,f17,f17])).
% 7.44/1.52  
% 7.44/1.52  cnf(c_7,plain,
% 7.44/1.52      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.44/1.52      inference(cnf_transformation,[],[f24]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_4,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.44/1.52      inference(cnf_transformation,[],[f29]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_1,plain,
% 7.44/1.52      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.44/1.52      inference(cnf_transformation,[],[f18]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_0,plain,
% 7.44/1.52      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.44/1.52      inference(cnf_transformation,[],[f16]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_23,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 7.44/1.52      inference(theory_normalisation,[status(thm)],[c_4,c_1,c_0]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_2,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.44/1.52      inference(cnf_transformation,[],[f28]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_24,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 7.44/1.52      inference(theory_normalisation,[status(thm)],[c_2,c_1,c_0]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_32,plain,
% 7.44/1.52      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.44/1.52      inference(light_normalisation,[status(thm)],[c_23,c_24]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_59,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_7,c_32]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_57,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_32,c_7]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_99,plain,
% 7.44/1.52      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_32,c_57]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_6,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.44/1.52      inference(cnf_transformation,[],[f23]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_111,plain,
% 7.44/1.52      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.44/1.52      inference(light_normalisation,[status(thm)],[c_99,c_6]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_112,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_111,c_57]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_160,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_59,c_112]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_170,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_160,c_6]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_181,plain,
% 7.44/1.52      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_170,c_112]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_186,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_7,c_181]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_263,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_0,c_24]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_3039,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_186,c_263]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_8,negated_conjecture,
% 7.44/1.52      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 7.44/1.52      inference(cnf_transformation,[],[f31]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_21,negated_conjecture,
% 7.44/1.52      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
% 7.44/1.52      inference(theory_normalisation,[status(thm)],[c_8,c_1,c_0]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_53,plain,
% 7.44/1.52      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_7,c_21]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_22606,plain,
% 7.44/1.52      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_3039,c_53]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_3,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.44/1.52      inference(cnf_transformation,[],[f20]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_266,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_3,c_24]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_280,plain,
% 7.44/1.52      ( k3_xboole_0(X0,X0) = X0 ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_266,c_6,c_111]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_290,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_280,c_1]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_33,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_365,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_280,c_33]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_499,plain,
% 7.44/1.52      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_290,c_365]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_301,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_0,c_290]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_510,plain,
% 7.44/1.52      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_365,c_301]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_329,plain,
% 7.44/1.52      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_290,c_301]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_347,plain,
% 7.44/1.52      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_329,c_280]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_444,plain,
% 7.44/1.52      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_0,c_347]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_530,plain,
% 7.44/1.52      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 7.44/1.52      inference(light_normalisation,[status(thm)],[c_510,c_444]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_540,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_499,c_530]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_1275,plain,
% 7.44/1.52      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,X0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_24,c_540]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_1352,plain,
% 7.44/1.52      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
% 7.44/1.52      inference(light_normalisation,[status(thm)],[c_1275,c_280]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_5,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.44/1.52      inference(cnf_transformation,[],[f30]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_22,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.44/1.52      inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_75,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_22,c_7]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_13873,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_1352,c_75]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_13903,plain,
% 7.44/1.52      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_1352,c_1]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_14013,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X2),X3)) ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_13873,c_13903]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_61,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_0,c_22]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_1674,plain,
% 7.44/1.52      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_24,c_61]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_34,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_810,plain,
% 7.44/1.52      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_24,c_34]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_1809,plain,
% 7.44/1.52      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
% 7.44/1.52      inference(light_normalisation,[status(thm)],[c_1674,c_810]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_14014,plain,
% 7.44/1.52      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 7.44/1.52      inference(light_normalisation,[status(thm)],[c_14013,c_1809]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_22607,plain,
% 7.44/1.52      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_22606,c_14014]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_514,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_365,c_22]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_337,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.44/1.52      inference(superposition,[status(thm)],[c_301,c_22]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_341,plain,
% 7.44/1.52      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_337,c_32]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_528,plain,
% 7.44/1.52      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.44/1.52      inference(light_normalisation,[status(thm)],[c_514,c_341]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_22608,plain,
% 7.44/1.52      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 7.44/1.52      inference(demodulation,[status(thm)],[c_22607,c_6,c_528]) ).
% 7.44/1.52  
% 7.44/1.52  cnf(c_22609,plain,
% 7.44/1.52      ( $false ),
% 7.44/1.52      inference(equality_resolution_simp,[status(thm)],[c_22608]) ).
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.44/1.52  
% 7.44/1.52  ------                               Statistics
% 7.44/1.52  
% 7.44/1.52  ------ General
% 7.44/1.52  
% 7.44/1.52  abstr_ref_over_cycles:                  0
% 7.44/1.52  abstr_ref_under_cycles:                 0
% 7.44/1.52  gc_basic_clause_elim:                   0
% 7.44/1.52  forced_gc_time:                         0
% 7.44/1.52  parsing_time:                           0.009
% 7.44/1.52  unif_index_cands_time:                  0.
% 7.44/1.52  unif_index_add_time:                    0.
% 7.44/1.52  orderings_time:                         0.
% 7.44/1.52  out_proof_time:                         0.019
% 7.44/1.52  total_time:                             0.677
% 7.44/1.52  num_of_symbols:                         36
% 7.44/1.52  num_of_terms:                           41730
% 7.44/1.52  
% 7.44/1.52  ------ Preprocessing
% 7.44/1.52  
% 7.44/1.52  num_of_splits:                          0
% 7.44/1.52  num_of_split_atoms:                     0
% 7.44/1.52  num_of_reused_defs:                     0
% 7.44/1.52  num_eq_ax_congr_red:                    0
% 7.44/1.52  num_of_sem_filtered_clauses:            0
% 7.44/1.52  num_of_subtypes:                        0
% 7.44/1.52  monotx_restored_types:                  0
% 7.44/1.52  sat_num_of_epr_types:                   0
% 7.44/1.52  sat_num_of_non_cyclic_types:            0
% 7.44/1.52  sat_guarded_non_collapsed_types:        0
% 7.44/1.52  num_pure_diseq_elim:                    0
% 7.44/1.52  simp_replaced_by:                       0
% 7.44/1.52  res_preprocessed:                       22
% 7.44/1.52  prep_upred:                             0
% 7.44/1.52  prep_unflattend:                        0
% 7.44/1.52  smt_new_axioms:                         0
% 7.44/1.52  pred_elim_cands:                        0
% 7.44/1.52  pred_elim:                              0
% 7.44/1.52  pred_elim_cl:                           0
% 7.44/1.52  pred_elim_cycles:                       0
% 7.44/1.52  merged_defs:                            0
% 7.44/1.52  merged_defs_ncl:                        0
% 7.44/1.52  bin_hyper_res:                          0
% 7.44/1.52  prep_cycles:                            2
% 7.44/1.52  pred_elim_time:                         0.
% 7.44/1.52  splitting_time:                         0.
% 7.44/1.52  sem_filter_time:                        0.
% 7.44/1.52  monotx_time:                            0.001
% 7.44/1.52  subtype_inf_time:                       0.
% 7.44/1.52  
% 7.44/1.52  ------ Problem properties
% 7.44/1.52  
% 7.44/1.52  clauses:                                9
% 7.44/1.52  conjectures:                            1
% 7.44/1.52  epr:                                    0
% 7.44/1.52  horn:                                   9
% 7.44/1.52  ground:                                 1
% 7.44/1.52  unary:                                  9
% 7.44/1.52  binary:                                 0
% 7.44/1.52  lits:                                   9
% 7.44/1.52  lits_eq:                                9
% 7.44/1.52  fd_pure:                                0
% 7.44/1.52  fd_pseudo:                              0
% 7.44/1.52  fd_cond:                                0
% 7.44/1.52  fd_pseudo_cond:                         0
% 7.44/1.52  ac_symbols:                             2
% 7.44/1.52  
% 7.44/1.52  ------ Propositional Solver
% 7.44/1.52  
% 7.44/1.52  prop_solver_calls:                      13
% 7.44/1.52  prop_fast_solver_calls:                 56
% 7.44/1.52  smt_solver_calls:                       0
% 7.44/1.52  smt_fast_solver_calls:                  0
% 7.44/1.52  prop_num_of_clauses:                    193
% 7.44/1.52  prop_preprocess_simplified:             361
% 7.44/1.52  prop_fo_subsumed:                       0
% 7.44/1.52  prop_solver_time:                       0.
% 7.44/1.52  smt_solver_time:                        0.
% 7.44/1.52  smt_fast_solver_time:                   0.
% 7.44/1.52  prop_fast_solver_time:                  0.
% 7.44/1.52  prop_unsat_core_time:                   0.
% 7.44/1.52  
% 7.44/1.52  ------ QBF
% 7.44/1.52  
% 7.44/1.52  qbf_q_res:                              0
% 7.44/1.52  qbf_num_tautologies:                    0
% 7.44/1.52  qbf_prep_cycles:                        0
% 7.44/1.52  
% 7.44/1.52  ------ BMC1
% 7.44/1.52  
% 7.44/1.52  bmc1_current_bound:                     -1
% 7.44/1.52  bmc1_last_solved_bound:                 -1
% 7.44/1.52  bmc1_unsat_core_size:                   -1
% 7.44/1.52  bmc1_unsat_core_parents_size:           -1
% 7.44/1.52  bmc1_merge_next_fun:                    0
% 7.44/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.44/1.52  
% 7.44/1.52  ------ Instantiation
% 7.44/1.52  
% 7.44/1.52  inst_num_of_clauses:                    0
% 7.44/1.52  inst_num_in_passive:                    0
% 7.44/1.52  inst_num_in_active:                     0
% 7.44/1.52  inst_num_in_unprocessed:                0
% 7.44/1.52  inst_num_of_loops:                      0
% 7.44/1.52  inst_num_of_learning_restarts:          0
% 7.44/1.52  inst_num_moves_active_passive:          0
% 7.44/1.52  inst_lit_activity:                      0
% 7.44/1.52  inst_lit_activity_moves:                0
% 7.44/1.52  inst_num_tautologies:                   0
% 7.44/1.52  inst_num_prop_implied:                  0
% 7.44/1.52  inst_num_existing_simplified:           0
% 7.44/1.52  inst_num_eq_res_simplified:             0
% 7.44/1.52  inst_num_child_elim:                    0
% 7.44/1.52  inst_num_of_dismatching_blockings:      0
% 7.44/1.52  inst_num_of_non_proper_insts:           0
% 7.44/1.52  inst_num_of_duplicates:                 0
% 7.44/1.52  inst_inst_num_from_inst_to_res:         0
% 7.44/1.52  inst_dismatching_checking_time:         0.
% 7.44/1.52  
% 7.44/1.52  ------ Resolution
% 7.44/1.52  
% 7.44/1.52  res_num_of_clauses:                     0
% 7.44/1.52  res_num_in_passive:                     0
% 7.44/1.52  res_num_in_active:                      0
% 7.44/1.52  res_num_of_loops:                       24
% 7.44/1.52  res_forward_subset_subsumed:            0
% 7.44/1.52  res_backward_subset_subsumed:           0
% 7.44/1.52  res_forward_subsumed:                   0
% 7.44/1.52  res_backward_subsumed:                  0
% 7.44/1.52  res_forward_subsumption_resolution:     0
% 7.44/1.52  res_backward_subsumption_resolution:    0
% 7.44/1.52  res_clause_to_clause_subsumption:       47609
% 7.44/1.52  res_orphan_elimination:                 0
% 7.44/1.52  res_tautology_del:                      0
% 7.44/1.52  res_num_eq_res_simplified:              0
% 7.44/1.52  res_num_sel_changes:                    0
% 7.44/1.52  res_moves_from_active_to_pass:          0
% 7.44/1.52  
% 7.44/1.52  ------ Superposition
% 7.44/1.52  
% 7.44/1.52  sup_time_total:                         0.
% 7.44/1.52  sup_time_generating:                    0.
% 7.44/1.52  sup_time_sim_full:                      0.
% 7.44/1.52  sup_time_sim_immed:                     0.
% 7.44/1.52  
% 7.44/1.52  sup_num_of_clauses:                     2196
% 7.44/1.52  sup_num_in_active:                      114
% 7.44/1.52  sup_num_in_passive:                     2082
% 7.44/1.52  sup_num_of_loops:                       123
% 7.44/1.52  sup_fw_superposition:                   8609
% 7.44/1.52  sup_bw_superposition:                   5927
% 7.44/1.52  sup_immediate_simplified:               6466
% 7.44/1.52  sup_given_eliminated:                   2
% 7.44/1.52  comparisons_done:                       0
% 7.44/1.52  comparisons_avoided:                    0
% 7.44/1.52  
% 7.44/1.52  ------ Simplifications
% 7.44/1.52  
% 7.44/1.52  
% 7.44/1.52  sim_fw_subset_subsumed:                 0
% 7.44/1.52  sim_bw_subset_subsumed:                 0
% 7.44/1.52  sim_fw_subsumed:                        582
% 7.44/1.52  sim_bw_subsumed:                        10
% 7.44/1.52  sim_fw_subsumption_res:                 0
% 7.44/1.52  sim_bw_subsumption_res:                 0
% 7.44/1.52  sim_tautology_del:                      0
% 7.44/1.52  sim_eq_tautology_del:                   2196
% 7.44/1.52  sim_eq_res_simp:                        0
% 7.44/1.52  sim_fw_demodulated:                     5015
% 7.44/1.52  sim_bw_demodulated:                     71
% 7.44/1.52  sim_light_normalised:                   2442
% 7.44/1.52  sim_joinable_taut:                      184
% 7.44/1.52  sim_joinable_simp:                      0
% 7.44/1.52  sim_ac_normalised:                      0
% 7.44/1.52  sim_smt_subsumption:                    0
% 7.44/1.52  
%------------------------------------------------------------------------------
