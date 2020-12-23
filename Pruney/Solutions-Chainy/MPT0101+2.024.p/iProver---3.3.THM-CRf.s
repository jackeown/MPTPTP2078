%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:01 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  120 (2050 expanded)
%              Number of clauses        :   77 ( 803 expanded)
%              Number of leaves         :   17 ( 576 expanded)
%              Depth                    :   25
%              Number of atoms          :  121 (2051 expanded)
%              Number of equality atoms :  120 (2050 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f30,f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f36,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f36,f22,f22,f30])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f22,f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f30])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_91,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_95,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_91,c_4])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_54,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_39,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8,c_6])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_39,c_39])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_37,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_7])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_38,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37,c_3])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_66,c_38])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_45,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_67,c_45])).

cnf(c_253,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_54,c_68])).

cnf(c_311,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_253,c_37])).

cnf(c_748,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_311,c_6])).

cnf(c_5174,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_95,c_748])).

cnf(c_5302,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5174,c_748])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_40,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_13,c_6])).

cnf(c_11,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_41,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_40,c_11])).

cnf(c_44,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_41])).

cnf(c_22206,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5302,c_44])).

cnf(c_86,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_12,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_560,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X1,X0))),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_86,c_12])).

cnf(c_77,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_84,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_77,c_1])).

cnf(c_88,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_578,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_560,c_1,c_4,c_7,c_84,c_88])).

cnf(c_1298,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_54,c_578])).

cnf(c_196,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_84])).

cnf(c_1342,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1298,c_196])).

cnf(c_2509,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_1342])).

cnf(c_2579,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2509,c_1342])).

cnf(c_5235,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_748,c_2579])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_377,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_259,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_4,c_68])).

cnf(c_305,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_259,c_68])).

cnf(c_382,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_377,c_39,c_305])).

cnf(c_383,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_382,c_37,c_54])).

cnf(c_803,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_383,c_7])).

cnf(c_884,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_803,c_6])).

cnf(c_57,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_45,c_7])).

cnf(c_898,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_884,c_6,c_57])).

cnf(c_1807,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_898])).

cnf(c_2515,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_578,c_1342])).

cnf(c_2576,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2515,c_1342])).

cnf(c_2695,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2576,c_5])).

cnf(c_2729,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_2695,c_311])).

cnf(c_2881,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)),k1_xboole_0) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1807,c_2729])).

cnf(c_2682,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X2,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1807,c_2576])).

cnf(c_1825,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_898,c_4])).

cnf(c_1828,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_898,c_578])).

cnf(c_1865,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1828,c_1342])).

cnf(c_1867,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1825,c_1865])).

cnf(c_2739,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_2682,c_1867])).

cnf(c_2930,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2881,c_2739])).

cnf(c_3020,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_2930,c_6])).

cnf(c_3032,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_3020,c_45])).

cnf(c_14818,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_3032,c_4])).

cnf(c_22207,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_22206,c_5235,c_14818])).

cnf(c_10,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_750,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_311,c_9])).

cnf(c_767,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_750,c_37,c_38])).

cnf(c_5350,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_767])).

cnf(c_5495,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5350,c_2729])).

cnf(c_22208,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_22207,c_5495])).

cnf(c_22517,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_0,c_22208])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.31/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/1.51  
% 7.31/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.31/1.51  
% 7.31/1.51  ------  iProver source info
% 7.31/1.51  
% 7.31/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.31/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.31/1.51  git: non_committed_changes: false
% 7.31/1.51  git: last_make_outside_of_git: false
% 7.31/1.51  
% 7.31/1.51  ------ 
% 7.31/1.51  
% 7.31/1.51  ------ Input Options
% 7.31/1.51  
% 7.31/1.51  --out_options                           all
% 7.31/1.51  --tptp_safe_out                         true
% 7.31/1.51  --problem_path                          ""
% 7.31/1.51  --include_path                          ""
% 7.31/1.51  --clausifier                            res/vclausify_rel
% 7.31/1.51  --clausifier_options                    --mode clausify
% 7.31/1.51  --stdin                                 false
% 7.31/1.51  --stats_out                             all
% 7.31/1.51  
% 7.31/1.51  ------ General Options
% 7.31/1.51  
% 7.31/1.51  --fof                                   false
% 7.31/1.51  --time_out_real                         305.
% 7.31/1.51  --time_out_virtual                      -1.
% 7.31/1.51  --symbol_type_check                     false
% 7.31/1.51  --clausify_out                          false
% 7.31/1.51  --sig_cnt_out                           false
% 7.31/1.51  --trig_cnt_out                          false
% 7.31/1.51  --trig_cnt_out_tolerance                1.
% 7.31/1.51  --trig_cnt_out_sk_spl                   false
% 7.31/1.51  --abstr_cl_out                          false
% 7.31/1.51  
% 7.31/1.51  ------ Global Options
% 7.31/1.51  
% 7.31/1.51  --schedule                              default
% 7.31/1.51  --add_important_lit                     false
% 7.31/1.51  --prop_solver_per_cl                    1000
% 7.31/1.51  --min_unsat_core                        false
% 7.31/1.51  --soft_assumptions                      false
% 7.31/1.51  --soft_lemma_size                       3
% 7.31/1.51  --prop_impl_unit_size                   0
% 7.31/1.51  --prop_impl_unit                        []
% 7.31/1.51  --share_sel_clauses                     true
% 7.31/1.51  --reset_solvers                         false
% 7.31/1.51  --bc_imp_inh                            [conj_cone]
% 7.31/1.51  --conj_cone_tolerance                   3.
% 7.31/1.51  --extra_neg_conj                        none
% 7.31/1.51  --large_theory_mode                     true
% 7.31/1.51  --prolific_symb_bound                   200
% 7.31/1.51  --lt_threshold                          2000
% 7.31/1.51  --clause_weak_htbl                      true
% 7.31/1.51  --gc_record_bc_elim                     false
% 7.31/1.51  
% 7.31/1.51  ------ Preprocessing Options
% 7.31/1.51  
% 7.31/1.51  --preprocessing_flag                    true
% 7.31/1.51  --time_out_prep_mult                    0.1
% 7.31/1.51  --splitting_mode                        input
% 7.31/1.51  --splitting_grd                         true
% 7.31/1.51  --splitting_cvd                         false
% 7.31/1.51  --splitting_cvd_svl                     false
% 7.31/1.51  --splitting_nvd                         32
% 7.31/1.51  --sub_typing                            true
% 7.31/1.51  --prep_gs_sim                           true
% 7.31/1.51  --prep_unflatten                        true
% 7.31/1.51  --prep_res_sim                          true
% 7.31/1.51  --prep_upred                            true
% 7.31/1.51  --prep_sem_filter                       exhaustive
% 7.31/1.51  --prep_sem_filter_out                   false
% 7.31/1.51  --pred_elim                             true
% 7.31/1.51  --res_sim_input                         true
% 7.31/1.51  --eq_ax_congr_red                       true
% 7.31/1.51  --pure_diseq_elim                       true
% 7.31/1.51  --brand_transform                       false
% 7.31/1.51  --non_eq_to_eq                          false
% 7.31/1.51  --prep_def_merge                        true
% 7.31/1.51  --prep_def_merge_prop_impl              false
% 7.31/1.51  --prep_def_merge_mbd                    true
% 7.31/1.51  --prep_def_merge_tr_red                 false
% 7.31/1.51  --prep_def_merge_tr_cl                  false
% 7.31/1.51  --smt_preprocessing                     true
% 7.31/1.51  --smt_ac_axioms                         fast
% 7.31/1.51  --preprocessed_out                      false
% 7.31/1.51  --preprocessed_stats                    false
% 7.31/1.51  
% 7.31/1.51  ------ Abstraction refinement Options
% 7.31/1.51  
% 7.31/1.51  --abstr_ref                             []
% 7.31/1.51  --abstr_ref_prep                        false
% 7.31/1.51  --abstr_ref_until_sat                   false
% 7.31/1.51  --abstr_ref_sig_restrict                funpre
% 7.31/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.31/1.51  --abstr_ref_under                       []
% 7.31/1.51  
% 7.31/1.51  ------ SAT Options
% 7.31/1.51  
% 7.31/1.51  --sat_mode                              false
% 7.31/1.51  --sat_fm_restart_options                ""
% 7.31/1.51  --sat_gr_def                            false
% 7.31/1.51  --sat_epr_types                         true
% 7.31/1.51  --sat_non_cyclic_types                  false
% 7.31/1.51  --sat_finite_models                     false
% 7.31/1.51  --sat_fm_lemmas                         false
% 7.31/1.51  --sat_fm_prep                           false
% 7.31/1.51  --sat_fm_uc_incr                        true
% 7.31/1.51  --sat_out_model                         small
% 7.31/1.51  --sat_out_clauses                       false
% 7.31/1.51  
% 7.31/1.51  ------ QBF Options
% 7.31/1.51  
% 7.31/1.51  --qbf_mode                              false
% 7.31/1.51  --qbf_elim_univ                         false
% 7.31/1.51  --qbf_dom_inst                          none
% 7.31/1.51  --qbf_dom_pre_inst                      false
% 7.31/1.51  --qbf_sk_in                             false
% 7.31/1.51  --qbf_pred_elim                         true
% 7.31/1.51  --qbf_split                             512
% 7.31/1.51  
% 7.31/1.51  ------ BMC1 Options
% 7.31/1.51  
% 7.31/1.51  --bmc1_incremental                      false
% 7.31/1.51  --bmc1_axioms                           reachable_all
% 7.31/1.51  --bmc1_min_bound                        0
% 7.31/1.51  --bmc1_max_bound                        -1
% 7.31/1.51  --bmc1_max_bound_default                -1
% 7.31/1.51  --bmc1_symbol_reachability              true
% 7.31/1.51  --bmc1_property_lemmas                  false
% 7.31/1.51  --bmc1_k_induction                      false
% 7.31/1.51  --bmc1_non_equiv_states                 false
% 7.31/1.51  --bmc1_deadlock                         false
% 7.31/1.51  --bmc1_ucm                              false
% 7.31/1.51  --bmc1_add_unsat_core                   none
% 7.31/1.51  --bmc1_unsat_core_children              false
% 7.31/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.31/1.51  --bmc1_out_stat                         full
% 7.31/1.51  --bmc1_ground_init                      false
% 7.31/1.51  --bmc1_pre_inst_next_state              false
% 7.31/1.51  --bmc1_pre_inst_state                   false
% 7.31/1.51  --bmc1_pre_inst_reach_state             false
% 7.31/1.51  --bmc1_out_unsat_core                   false
% 7.31/1.51  --bmc1_aig_witness_out                  false
% 7.31/1.51  --bmc1_verbose                          false
% 7.31/1.51  --bmc1_dump_clauses_tptp                false
% 7.31/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.31/1.51  --bmc1_dump_file                        -
% 7.31/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.31/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.31/1.51  --bmc1_ucm_extend_mode                  1
% 7.31/1.51  --bmc1_ucm_init_mode                    2
% 7.31/1.51  --bmc1_ucm_cone_mode                    none
% 7.31/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.31/1.51  --bmc1_ucm_relax_model                  4
% 7.31/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.31/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.31/1.51  --bmc1_ucm_layered_model                none
% 7.31/1.51  --bmc1_ucm_max_lemma_size               10
% 7.31/1.51  
% 7.31/1.51  ------ AIG Options
% 7.31/1.51  
% 7.31/1.51  --aig_mode                              false
% 7.31/1.51  
% 7.31/1.51  ------ Instantiation Options
% 7.31/1.51  
% 7.31/1.51  --instantiation_flag                    true
% 7.31/1.51  --inst_sos_flag                         false
% 7.31/1.51  --inst_sos_phase                        true
% 7.31/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.31/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.31/1.51  --inst_lit_sel_side                     num_symb
% 7.31/1.51  --inst_solver_per_active                1400
% 7.31/1.51  --inst_solver_calls_frac                1.
% 7.31/1.51  --inst_passive_queue_type               priority_queues
% 7.31/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.31/1.51  --inst_passive_queues_freq              [25;2]
% 7.31/1.51  --inst_dismatching                      true
% 7.31/1.51  --inst_eager_unprocessed_to_passive     true
% 7.31/1.51  --inst_prop_sim_given                   true
% 7.31/1.51  --inst_prop_sim_new                     false
% 7.31/1.51  --inst_subs_new                         false
% 7.31/1.51  --inst_eq_res_simp                      false
% 7.31/1.51  --inst_subs_given                       false
% 7.31/1.51  --inst_orphan_elimination               true
% 7.31/1.51  --inst_learning_loop_flag               true
% 7.31/1.51  --inst_learning_start                   3000
% 7.31/1.51  --inst_learning_factor                  2
% 7.31/1.51  --inst_start_prop_sim_after_learn       3
% 7.31/1.51  --inst_sel_renew                        solver
% 7.31/1.51  --inst_lit_activity_flag                true
% 7.31/1.51  --inst_restr_to_given                   false
% 7.31/1.51  --inst_activity_threshold               500
% 7.31/1.51  --inst_out_proof                        true
% 7.31/1.51  
% 7.31/1.51  ------ Resolution Options
% 7.31/1.51  
% 7.31/1.51  --resolution_flag                       true
% 7.31/1.51  --res_lit_sel                           adaptive
% 7.31/1.51  --res_lit_sel_side                      none
% 7.31/1.51  --res_ordering                          kbo
% 7.31/1.51  --res_to_prop_solver                    active
% 7.31/1.51  --res_prop_simpl_new                    false
% 7.31/1.51  --res_prop_simpl_given                  true
% 7.31/1.51  --res_passive_queue_type                priority_queues
% 7.31/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.31/1.51  --res_passive_queues_freq               [15;5]
% 7.31/1.51  --res_forward_subs                      full
% 7.31/1.51  --res_backward_subs                     full
% 7.31/1.51  --res_forward_subs_resolution           true
% 7.31/1.51  --res_backward_subs_resolution          true
% 7.31/1.51  --res_orphan_elimination                true
% 7.31/1.51  --res_time_limit                        2.
% 7.31/1.51  --res_out_proof                         true
% 7.31/1.51  
% 7.31/1.51  ------ Superposition Options
% 7.31/1.51  
% 7.31/1.51  --superposition_flag                    true
% 7.31/1.51  --sup_passive_queue_type                priority_queues
% 7.31/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.31/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.31/1.51  --demod_completeness_check              fast
% 7.31/1.51  --demod_use_ground                      true
% 7.31/1.51  --sup_to_prop_solver                    passive
% 7.31/1.51  --sup_prop_simpl_new                    true
% 7.31/1.51  --sup_prop_simpl_given                  true
% 7.31/1.51  --sup_fun_splitting                     false
% 7.31/1.51  --sup_smt_interval                      50000
% 7.31/1.51  
% 7.31/1.51  ------ Superposition Simplification Setup
% 7.31/1.51  
% 7.31/1.51  --sup_indices_passive                   []
% 7.31/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.31/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.51  --sup_full_bw                           [BwDemod]
% 7.31/1.51  --sup_immed_triv                        [TrivRules]
% 7.31/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.51  --sup_immed_bw_main                     []
% 7.31/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.31/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.31/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.31/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.31/1.51  
% 7.31/1.51  ------ Combination Options
% 7.31/1.51  
% 7.31/1.51  --comb_res_mult                         3
% 7.31/1.51  --comb_sup_mult                         2
% 7.31/1.51  --comb_inst_mult                        10
% 7.31/1.51  
% 7.31/1.51  ------ Debug Options
% 7.31/1.51  
% 7.31/1.51  --dbg_backtrace                         false
% 7.31/1.51  --dbg_dump_prop_clauses                 false
% 7.31/1.51  --dbg_dump_prop_clauses_file            -
% 7.31/1.51  --dbg_out_stat                          false
% 7.31/1.51  ------ Parsing...
% 7.31/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.31/1.51  
% 7.31/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.31/1.51  
% 7.31/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.31/1.51  
% 7.31/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.31/1.51  ------ Proving...
% 7.31/1.51  ------ Problem Properties 
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  clauses                                 14
% 7.31/1.51  conjectures                             1
% 7.31/1.51  EPR                                     0
% 7.31/1.51  Horn                                    14
% 7.31/1.51  unary                                   14
% 7.31/1.51  binary                                  0
% 7.31/1.51  lits                                    14
% 7.31/1.51  lits eq                                 14
% 7.31/1.51  fd_pure                                 0
% 7.31/1.51  fd_pseudo                               0
% 7.31/1.51  fd_cond                                 0
% 7.31/1.51  fd_pseudo_cond                          0
% 7.31/1.51  AC symbols                              0
% 7.31/1.51  
% 7.31/1.51  ------ Schedule UEQ
% 7.31/1.51  
% 7.31/1.51  ------ pure equality problem: resolution off 
% 7.31/1.51  
% 7.31/1.51  ------ Option_UEQ Time Limit: Unbounded
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  ------ 
% 7.31/1.51  Current options:
% 7.31/1.51  ------ 
% 7.31/1.51  
% 7.31/1.51  ------ Input Options
% 7.31/1.51  
% 7.31/1.51  --out_options                           all
% 7.31/1.51  --tptp_safe_out                         true
% 7.31/1.51  --problem_path                          ""
% 7.31/1.51  --include_path                          ""
% 7.31/1.51  --clausifier                            res/vclausify_rel
% 7.31/1.51  --clausifier_options                    --mode clausify
% 7.31/1.51  --stdin                                 false
% 7.31/1.51  --stats_out                             all
% 7.31/1.51  
% 7.31/1.51  ------ General Options
% 7.31/1.51  
% 7.31/1.51  --fof                                   false
% 7.31/1.51  --time_out_real                         305.
% 7.31/1.51  --time_out_virtual                      -1.
% 7.31/1.51  --symbol_type_check                     false
% 7.31/1.51  --clausify_out                          false
% 7.31/1.51  --sig_cnt_out                           false
% 7.31/1.51  --trig_cnt_out                          false
% 7.31/1.51  --trig_cnt_out_tolerance                1.
% 7.31/1.51  --trig_cnt_out_sk_spl                   false
% 7.31/1.51  --abstr_cl_out                          false
% 7.31/1.51  
% 7.31/1.51  ------ Global Options
% 7.31/1.51  
% 7.31/1.51  --schedule                              default
% 7.31/1.51  --add_important_lit                     false
% 7.31/1.51  --prop_solver_per_cl                    1000
% 7.31/1.51  --min_unsat_core                        false
% 7.31/1.51  --soft_assumptions                      false
% 7.31/1.51  --soft_lemma_size                       3
% 7.31/1.51  --prop_impl_unit_size                   0
% 7.31/1.51  --prop_impl_unit                        []
% 7.31/1.51  --share_sel_clauses                     true
% 7.31/1.51  --reset_solvers                         false
% 7.31/1.51  --bc_imp_inh                            [conj_cone]
% 7.31/1.51  --conj_cone_tolerance                   3.
% 7.31/1.51  --extra_neg_conj                        none
% 7.31/1.51  --large_theory_mode                     true
% 7.31/1.51  --prolific_symb_bound                   200
% 7.31/1.51  --lt_threshold                          2000
% 7.31/1.51  --clause_weak_htbl                      true
% 7.31/1.51  --gc_record_bc_elim                     false
% 7.31/1.51  
% 7.31/1.51  ------ Preprocessing Options
% 7.31/1.51  
% 7.31/1.51  --preprocessing_flag                    true
% 7.31/1.51  --time_out_prep_mult                    0.1
% 7.31/1.51  --splitting_mode                        input
% 7.31/1.51  --splitting_grd                         true
% 7.31/1.51  --splitting_cvd                         false
% 7.31/1.51  --splitting_cvd_svl                     false
% 7.31/1.51  --splitting_nvd                         32
% 7.31/1.51  --sub_typing                            true
% 7.31/1.51  --prep_gs_sim                           true
% 7.31/1.51  --prep_unflatten                        true
% 7.31/1.51  --prep_res_sim                          true
% 7.31/1.51  --prep_upred                            true
% 7.31/1.51  --prep_sem_filter                       exhaustive
% 7.31/1.51  --prep_sem_filter_out                   false
% 7.31/1.51  --pred_elim                             true
% 7.31/1.51  --res_sim_input                         true
% 7.31/1.51  --eq_ax_congr_red                       true
% 7.31/1.51  --pure_diseq_elim                       true
% 7.31/1.51  --brand_transform                       false
% 7.31/1.51  --non_eq_to_eq                          false
% 7.31/1.51  --prep_def_merge                        true
% 7.31/1.51  --prep_def_merge_prop_impl              false
% 7.31/1.51  --prep_def_merge_mbd                    true
% 7.31/1.51  --prep_def_merge_tr_red                 false
% 7.31/1.51  --prep_def_merge_tr_cl                  false
% 7.31/1.51  --smt_preprocessing                     true
% 7.31/1.51  --smt_ac_axioms                         fast
% 7.31/1.51  --preprocessed_out                      false
% 7.31/1.51  --preprocessed_stats                    false
% 7.31/1.51  
% 7.31/1.51  ------ Abstraction refinement Options
% 7.31/1.51  
% 7.31/1.51  --abstr_ref                             []
% 7.31/1.51  --abstr_ref_prep                        false
% 7.31/1.51  --abstr_ref_until_sat                   false
% 7.31/1.51  --abstr_ref_sig_restrict                funpre
% 7.31/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.31/1.51  --abstr_ref_under                       []
% 7.31/1.51  
% 7.31/1.51  ------ SAT Options
% 7.31/1.51  
% 7.31/1.51  --sat_mode                              false
% 7.31/1.51  --sat_fm_restart_options                ""
% 7.31/1.51  --sat_gr_def                            false
% 7.31/1.51  --sat_epr_types                         true
% 7.31/1.51  --sat_non_cyclic_types                  false
% 7.31/1.51  --sat_finite_models                     false
% 7.31/1.51  --sat_fm_lemmas                         false
% 7.31/1.51  --sat_fm_prep                           false
% 7.31/1.51  --sat_fm_uc_incr                        true
% 7.31/1.51  --sat_out_model                         small
% 7.31/1.51  --sat_out_clauses                       false
% 7.31/1.51  
% 7.31/1.51  ------ QBF Options
% 7.31/1.51  
% 7.31/1.51  --qbf_mode                              false
% 7.31/1.51  --qbf_elim_univ                         false
% 7.31/1.51  --qbf_dom_inst                          none
% 7.31/1.51  --qbf_dom_pre_inst                      false
% 7.31/1.51  --qbf_sk_in                             false
% 7.31/1.51  --qbf_pred_elim                         true
% 7.31/1.51  --qbf_split                             512
% 7.31/1.51  
% 7.31/1.51  ------ BMC1 Options
% 7.31/1.51  
% 7.31/1.51  --bmc1_incremental                      false
% 7.31/1.51  --bmc1_axioms                           reachable_all
% 7.31/1.51  --bmc1_min_bound                        0
% 7.31/1.51  --bmc1_max_bound                        -1
% 7.31/1.51  --bmc1_max_bound_default                -1
% 7.31/1.51  --bmc1_symbol_reachability              true
% 7.31/1.51  --bmc1_property_lemmas                  false
% 7.31/1.51  --bmc1_k_induction                      false
% 7.31/1.51  --bmc1_non_equiv_states                 false
% 7.31/1.51  --bmc1_deadlock                         false
% 7.31/1.51  --bmc1_ucm                              false
% 7.31/1.51  --bmc1_add_unsat_core                   none
% 7.31/1.51  --bmc1_unsat_core_children              false
% 7.31/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.31/1.51  --bmc1_out_stat                         full
% 7.31/1.51  --bmc1_ground_init                      false
% 7.31/1.51  --bmc1_pre_inst_next_state              false
% 7.31/1.51  --bmc1_pre_inst_state                   false
% 7.31/1.51  --bmc1_pre_inst_reach_state             false
% 7.31/1.51  --bmc1_out_unsat_core                   false
% 7.31/1.51  --bmc1_aig_witness_out                  false
% 7.31/1.51  --bmc1_verbose                          false
% 7.31/1.51  --bmc1_dump_clauses_tptp                false
% 7.31/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.31/1.51  --bmc1_dump_file                        -
% 7.31/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.31/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.31/1.51  --bmc1_ucm_extend_mode                  1
% 7.31/1.51  --bmc1_ucm_init_mode                    2
% 7.31/1.51  --bmc1_ucm_cone_mode                    none
% 7.31/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.31/1.51  --bmc1_ucm_relax_model                  4
% 7.31/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.31/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.31/1.51  --bmc1_ucm_layered_model                none
% 7.31/1.51  --bmc1_ucm_max_lemma_size               10
% 7.31/1.51  
% 7.31/1.51  ------ AIG Options
% 7.31/1.51  
% 7.31/1.51  --aig_mode                              false
% 7.31/1.51  
% 7.31/1.51  ------ Instantiation Options
% 7.31/1.51  
% 7.31/1.51  --instantiation_flag                    false
% 7.31/1.51  --inst_sos_flag                         false
% 7.31/1.51  --inst_sos_phase                        true
% 7.31/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.31/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.31/1.51  --inst_lit_sel_side                     num_symb
% 7.31/1.51  --inst_solver_per_active                1400
% 7.31/1.51  --inst_solver_calls_frac                1.
% 7.31/1.51  --inst_passive_queue_type               priority_queues
% 7.31/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.31/1.51  --inst_passive_queues_freq              [25;2]
% 7.31/1.51  --inst_dismatching                      true
% 7.31/1.51  --inst_eager_unprocessed_to_passive     true
% 7.31/1.51  --inst_prop_sim_given                   true
% 7.31/1.51  --inst_prop_sim_new                     false
% 7.31/1.51  --inst_subs_new                         false
% 7.31/1.51  --inst_eq_res_simp                      false
% 7.31/1.51  --inst_subs_given                       false
% 7.31/1.51  --inst_orphan_elimination               true
% 7.31/1.51  --inst_learning_loop_flag               true
% 7.31/1.51  --inst_learning_start                   3000
% 7.31/1.51  --inst_learning_factor                  2
% 7.31/1.51  --inst_start_prop_sim_after_learn       3
% 7.31/1.51  --inst_sel_renew                        solver
% 7.31/1.51  --inst_lit_activity_flag                true
% 7.31/1.51  --inst_restr_to_given                   false
% 7.31/1.51  --inst_activity_threshold               500
% 7.31/1.51  --inst_out_proof                        true
% 7.31/1.51  
% 7.31/1.51  ------ Resolution Options
% 7.31/1.51  
% 7.31/1.51  --resolution_flag                       false
% 7.31/1.51  --res_lit_sel                           adaptive
% 7.31/1.51  --res_lit_sel_side                      none
% 7.31/1.51  --res_ordering                          kbo
% 7.31/1.51  --res_to_prop_solver                    active
% 7.31/1.51  --res_prop_simpl_new                    false
% 7.31/1.51  --res_prop_simpl_given                  true
% 7.31/1.51  --res_passive_queue_type                priority_queues
% 7.31/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.31/1.51  --res_passive_queues_freq               [15;5]
% 7.31/1.51  --res_forward_subs                      full
% 7.31/1.51  --res_backward_subs                     full
% 7.31/1.51  --res_forward_subs_resolution           true
% 7.31/1.51  --res_backward_subs_resolution          true
% 7.31/1.51  --res_orphan_elimination                true
% 7.31/1.51  --res_time_limit                        2.
% 7.31/1.51  --res_out_proof                         true
% 7.31/1.51  
% 7.31/1.51  ------ Superposition Options
% 7.31/1.51  
% 7.31/1.51  --superposition_flag                    true
% 7.31/1.51  --sup_passive_queue_type                priority_queues
% 7.31/1.51  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.31/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.31/1.51  --demod_completeness_check              fast
% 7.31/1.51  --demod_use_ground                      true
% 7.31/1.51  --sup_to_prop_solver                    active
% 7.31/1.51  --sup_prop_simpl_new                    false
% 7.31/1.51  --sup_prop_simpl_given                  false
% 7.31/1.51  --sup_fun_splitting                     true
% 7.31/1.51  --sup_smt_interval                      10000
% 7.31/1.51  
% 7.31/1.51  ------ Superposition Simplification Setup
% 7.31/1.51  
% 7.31/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.31/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.31/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.51  --sup_full_triv                         [TrivRules]
% 7.31/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.31/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.31/1.51  --sup_immed_triv                        [TrivRules]
% 7.31/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.51  --sup_immed_bw_main                     []
% 7.31/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.31/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.31/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.51  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.31/1.51  
% 7.31/1.51  ------ Combination Options
% 7.31/1.51  
% 7.31/1.51  --comb_res_mult                         1
% 7.31/1.51  --comb_sup_mult                         1
% 7.31/1.51  --comb_inst_mult                        1000000
% 7.31/1.51  
% 7.31/1.51  ------ Debug Options
% 7.31/1.51  
% 7.31/1.51  --dbg_backtrace                         false
% 7.31/1.51  --dbg_dump_prop_clauses                 false
% 7.31/1.51  --dbg_dump_prop_clauses_file            -
% 7.31/1.51  --dbg_out_stat                          false
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  ------ Proving...
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  % SZS status Theorem for theBenchmark.p
% 7.31/1.51  
% 7.31/1.51   Resolution empty clause
% 7.31/1.51  
% 7.31/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.31/1.51  
% 7.31/1.51  fof(f1,axiom,(
% 7.31/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f21,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f1])).
% 7.31/1.51  
% 7.31/1.51  fof(f7,axiom,(
% 7.31/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f27,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f7])).
% 7.31/1.51  
% 7.31/1.51  fof(f6,axiom,(
% 7.31/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f26,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.31/1.51    inference(cnf_transformation,[],[f6])).
% 7.31/1.51  
% 7.31/1.51  fof(f9,axiom,(
% 7.31/1.51    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f29,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.31/1.51    inference(cnf_transformation,[],[f9])).
% 7.31/1.51  
% 7.31/1.51  fof(f11,axiom,(
% 7.31/1.51    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f31,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.31/1.51    inference(cnf_transformation,[],[f11])).
% 7.31/1.51  
% 7.31/1.51  fof(f10,axiom,(
% 7.31/1.51    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f30,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f10])).
% 7.31/1.51  
% 7.31/1.51  fof(f39,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.31/1.51    inference(definition_unfolding,[],[f31,f30,f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f8,axiom,(
% 7.31/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f28,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f8])).
% 7.31/1.51  
% 7.31/1.51  fof(f4,axiom,(
% 7.31/1.51    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f24,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.31/1.51    inference(cnf_transformation,[],[f4])).
% 7.31/1.51  
% 7.31/1.51  fof(f37,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 7.31/1.51    inference(definition_unfolding,[],[f24,f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f5,axiom,(
% 7.31/1.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f25,plain,(
% 7.31/1.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f5])).
% 7.31/1.51  
% 7.31/1.51  fof(f38,plain,(
% 7.31/1.51    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.31/1.51    inference(definition_unfolding,[],[f25,f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f3,axiom,(
% 7.31/1.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f23,plain,(
% 7.31/1.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.31/1.51    inference(cnf_transformation,[],[f3])).
% 7.31/1.51  
% 7.31/1.51  fof(f16,conjecture,(
% 7.31/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f17,negated_conjecture,(
% 7.31/1.51    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.31/1.51    inference(negated_conjecture,[],[f16])).
% 7.31/1.51  
% 7.31/1.51  fof(f18,plain,(
% 7.31/1.51    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.31/1.51    inference(ennf_transformation,[],[f17])).
% 7.31/1.51  
% 7.31/1.51  fof(f19,plain,(
% 7.31/1.51    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.31/1.51    introduced(choice_axiom,[])).
% 7.31/1.51  
% 7.31/1.51  fof(f20,plain,(
% 7.31/1.51    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.31/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 7.31/1.51  
% 7.31/1.51  fof(f36,plain,(
% 7.31/1.51    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.31/1.51    inference(cnf_transformation,[],[f20])).
% 7.31/1.51  
% 7.31/1.51  fof(f2,axiom,(
% 7.31/1.51    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f22,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.31/1.51    inference(cnf_transformation,[],[f2])).
% 7.31/1.51  
% 7.31/1.51  fof(f43,plain,(
% 7.31/1.51    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 7.31/1.51    inference(definition_unfolding,[],[f36,f22,f22,f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f14,axiom,(
% 7.31/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f34,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.31/1.51    inference(cnf_transformation,[],[f14])).
% 7.31/1.51  
% 7.31/1.51  fof(f15,axiom,(
% 7.31/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f35,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 7.31/1.51    inference(cnf_transformation,[],[f15])).
% 7.31/1.51  
% 7.31/1.51  fof(f42,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.31/1.51    inference(definition_unfolding,[],[f35,f22,f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f12,axiom,(
% 7.31/1.51    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f32,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 7.31/1.51    inference(cnf_transformation,[],[f12])).
% 7.31/1.51  
% 7.31/1.51  fof(f40,plain,(
% 7.31/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 7.31/1.51    inference(definition_unfolding,[],[f32,f30])).
% 7.31/1.51  
% 7.31/1.51  fof(f13,axiom,(
% 7.31/1.51    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.31/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.51  
% 7.31/1.51  fof(f33,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 7.31/1.51    inference(cnf_transformation,[],[f13])).
% 7.31/1.51  
% 7.31/1.51  fof(f41,plain,(
% 7.31/1.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.31/1.51    inference(definition_unfolding,[],[f33,f30])).
% 7.31/1.51  
% 7.31/1.51  cnf(c_0,plain,
% 7.31/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(cnf_transformation,[],[f21]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_5,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.31/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_4,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.31/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_91,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_95,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_91,c_4]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_7,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.31/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_54,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_8,plain,
% 7.31/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.31/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_6,plain,
% 7.31/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.31/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_39,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_8,c_6]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_66,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_39,c_39]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 7.31/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_37,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_2,c_7]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_3,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.31/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_38,plain,
% 7.31/1.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_37,c_3]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_67,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_66,c_38]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.31/1.51      inference(cnf_transformation,[],[f23]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_45,plain,
% 7.31/1.51      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_68,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_67,c_45]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_253,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_54,c_68]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_311,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_253,c_37]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_748,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_311,c_6]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_5174,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_95,c_748]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_5302,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_5174,c_748]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_13,negated_conjecture,
% 7.31/1.51      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 7.31/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_40,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_13,c_6]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_11,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.31/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_41,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k2_xboole_0(sK0,sK1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_40,c_11]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_44,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_0,c_41]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_22206,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_5302,c_44]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_86,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_12,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 7.31/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_560,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X1,X0))),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_86,c_12]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_77,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_84,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_77,c_1]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_88,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_578,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_560,c_1,c_4,c_7,c_84,c_88]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1298,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_54,c_578]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_196,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_0,c_84]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1342,plain,
% 7.31/1.51      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_1298,c_196]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2509,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_4,c_1342]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2579,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_2509,c_1342]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_5235,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_748,c_2579]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_9,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 7.31/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_377,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_9,c_4]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_259,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_4,c_68]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_305,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_259,c_68]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_382,plain,
% 7.31/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_377,c_39,c_305]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_383,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_382,c_37,c_54]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_803,plain,
% 7.31/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_383,c_7]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_884,plain,
% 7.31/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_803,c_6]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_57,plain,
% 7.31/1.51      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_45,c_7]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_898,plain,
% 7.31/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_884,c_6,c_57]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1807,plain,
% 7.31/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_0,c_898]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2515,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_578,c_1342]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2576,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_2515,c_1342]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2695,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_2576,c_5]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2729,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_2695,c_311]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2881,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)),k1_xboole_0) = k2_xboole_0(X2,X0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_1807,c_2729]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2682,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X2,X0),k1_xboole_0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_1807,c_2576]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1825,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_898,c_4]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1828,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_898,c_578]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1865,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_1828,c_1342]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_1867,plain,
% 7.31/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_1825,c_1865]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2739,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_2682,c_1867]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_2930,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_2881,c_2739]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_3020,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_2930,c_6]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_3032,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_3020,c_45]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_14818,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_3032,c_4]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_22207,plain,
% 7.31/1.51      ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_22206,c_5235,c_14818]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_10,plain,
% 7.31/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 7.31/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_750,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_311,c_9]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_767,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1))) = X0 ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_750,c_37,c_38]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_5350,plain,
% 7.31/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_10,c_767]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_5495,plain,
% 7.31/1.51      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
% 7.31/1.51      inference(light_normalisation,[status(thm)],[c_5350,c_2729]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_22208,plain,
% 7.31/1.51      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 7.31/1.51      inference(demodulation,[status(thm)],[c_22207,c_5495]) ).
% 7.31/1.51  
% 7.31/1.51  cnf(c_22517,plain,
% 7.31/1.51      ( $false ),
% 7.31/1.51      inference(superposition,[status(thm)],[c_0,c_22208]) ).
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.31/1.51  
% 7.31/1.51  ------                               Statistics
% 7.31/1.51  
% 7.31/1.51  ------ General
% 7.31/1.51  
% 7.31/1.51  abstr_ref_over_cycles:                  0
% 7.31/1.51  abstr_ref_under_cycles:                 0
% 7.31/1.51  gc_basic_clause_elim:                   0
% 7.31/1.51  forced_gc_time:                         0
% 7.31/1.51  parsing_time:                           0.006
% 7.31/1.51  unif_index_cands_time:                  0.
% 7.31/1.51  unif_index_add_time:                    0.
% 7.31/1.51  orderings_time:                         0.
% 7.31/1.51  out_proof_time:                         0.006
% 7.31/1.51  total_time:                             0.641
% 7.31/1.51  num_of_symbols:                         38
% 7.31/1.51  num_of_terms:                           36400
% 7.31/1.51  
% 7.31/1.51  ------ Preprocessing
% 7.31/1.51  
% 7.31/1.51  num_of_splits:                          0
% 7.31/1.51  num_of_split_atoms:                     2
% 7.31/1.51  num_of_reused_defs:                     0
% 7.31/1.51  num_eq_ax_congr_red:                    0
% 7.31/1.51  num_of_sem_filtered_clauses:            0
% 7.31/1.51  num_of_subtypes:                        0
% 7.31/1.51  monotx_restored_types:                  0
% 7.31/1.51  sat_num_of_epr_types:                   0
% 7.31/1.51  sat_num_of_non_cyclic_types:            0
% 7.31/1.51  sat_guarded_non_collapsed_types:        0
% 7.31/1.51  num_pure_diseq_elim:                    0
% 7.31/1.51  simp_replaced_by:                       0
% 7.31/1.51  res_preprocessed:                       32
% 7.31/1.51  prep_upred:                             0
% 7.31/1.51  prep_unflattend:                        0
% 7.31/1.51  smt_new_axioms:                         0
% 7.31/1.51  pred_elim_cands:                        0
% 7.31/1.51  pred_elim:                              0
% 7.31/1.51  pred_elim_cl:                           0
% 7.31/1.51  pred_elim_cycles:                       0
% 7.31/1.51  merged_defs:                            0
% 7.31/1.51  merged_defs_ncl:                        0
% 7.31/1.51  bin_hyper_res:                          0
% 7.31/1.51  prep_cycles:                            2
% 7.31/1.51  pred_elim_time:                         0.
% 7.31/1.51  splitting_time:                         0.
% 7.31/1.51  sem_filter_time:                        0.
% 7.31/1.51  monotx_time:                            0.
% 7.31/1.51  subtype_inf_time:                       0.
% 7.31/1.51  
% 7.31/1.51  ------ Problem properties
% 7.31/1.51  
% 7.31/1.51  clauses:                                14
% 7.31/1.51  conjectures:                            1
% 7.31/1.51  epr:                                    0
% 7.31/1.51  horn:                                   14
% 7.31/1.51  ground:                                 1
% 7.31/1.51  unary:                                  14
% 7.31/1.51  binary:                                 0
% 7.31/1.51  lits:                                   14
% 7.31/1.51  lits_eq:                                14
% 7.31/1.51  fd_pure:                                0
% 7.31/1.51  fd_pseudo:                              0
% 7.31/1.51  fd_cond:                                0
% 7.31/1.51  fd_pseudo_cond:                         0
% 7.31/1.51  ac_symbols:                             0
% 7.31/1.51  
% 7.31/1.51  ------ Propositional Solver
% 7.31/1.51  
% 7.31/1.51  prop_solver_calls:                      13
% 7.31/1.51  prop_fast_solver_calls:                 76
% 7.31/1.51  smt_solver_calls:                       0
% 7.31/1.51  smt_fast_solver_calls:                  0
% 7.31/1.51  prop_num_of_clauses:                    230
% 7.31/1.51  prop_preprocess_simplified:             492
% 7.31/1.51  prop_fo_subsumed:                       0
% 7.31/1.51  prop_solver_time:                       0.
% 7.31/1.51  smt_solver_time:                        0.
% 7.31/1.51  smt_fast_solver_time:                   0.
% 7.31/1.51  prop_fast_solver_time:                  0.
% 7.31/1.51  prop_unsat_core_time:                   0.
% 7.31/1.51  
% 7.31/1.51  ------ QBF
% 7.31/1.51  
% 7.31/1.51  qbf_q_res:                              0
% 7.31/1.51  qbf_num_tautologies:                    0
% 7.31/1.51  qbf_prep_cycles:                        0
% 7.31/1.51  
% 7.31/1.51  ------ BMC1
% 7.31/1.51  
% 7.31/1.51  bmc1_current_bound:                     -1
% 7.31/1.51  bmc1_last_solved_bound:                 -1
% 7.31/1.51  bmc1_unsat_core_size:                   -1
% 7.31/1.51  bmc1_unsat_core_parents_size:           -1
% 7.31/1.51  bmc1_merge_next_fun:                    0
% 7.31/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.31/1.51  
% 7.31/1.51  ------ Instantiation
% 7.31/1.51  
% 7.31/1.51  inst_num_of_clauses:                    0
% 7.31/1.51  inst_num_in_passive:                    0
% 7.31/1.51  inst_num_in_active:                     0
% 7.31/1.51  inst_num_in_unprocessed:                0
% 7.31/1.51  inst_num_of_loops:                      0
% 7.31/1.51  inst_num_of_learning_restarts:          0
% 7.31/1.51  inst_num_moves_active_passive:          0
% 7.31/1.51  inst_lit_activity:                      0
% 7.31/1.51  inst_lit_activity_moves:                0
% 7.31/1.51  inst_num_tautologies:                   0
% 7.31/1.51  inst_num_prop_implied:                  0
% 7.31/1.51  inst_num_existing_simplified:           0
% 7.31/1.51  inst_num_eq_res_simplified:             0
% 7.31/1.51  inst_num_child_elim:                    0
% 7.31/1.51  inst_num_of_dismatching_blockings:      0
% 7.31/1.51  inst_num_of_non_proper_insts:           0
% 7.31/1.51  inst_num_of_duplicates:                 0
% 7.31/1.51  inst_inst_num_from_inst_to_res:         0
% 7.31/1.51  inst_dismatching_checking_time:         0.
% 7.31/1.51  
% 7.31/1.51  ------ Resolution
% 7.31/1.51  
% 7.31/1.51  res_num_of_clauses:                     0
% 7.31/1.51  res_num_in_passive:                     0
% 7.31/1.51  res_num_in_active:                      0
% 7.31/1.51  res_num_of_loops:                       34
% 7.31/1.51  res_forward_subset_subsumed:            0
% 7.31/1.51  res_backward_subset_subsumed:           0
% 7.31/1.51  res_forward_subsumed:                   0
% 7.31/1.51  res_backward_subsumed:                  0
% 7.31/1.51  res_forward_subsumption_resolution:     0
% 7.31/1.51  res_backward_subsumption_resolution:    0
% 7.31/1.51  res_clause_to_clause_subsumption:       55836
% 7.31/1.51  res_orphan_elimination:                 0
% 7.31/1.51  res_tautology_del:                      0
% 7.31/1.51  res_num_eq_res_simplified:              0
% 7.31/1.51  res_num_sel_changes:                    0
% 7.31/1.51  res_moves_from_active_to_pass:          0
% 7.31/1.51  
% 7.31/1.51  ------ Superposition
% 7.31/1.51  
% 7.31/1.51  sup_time_total:                         0.
% 7.31/1.51  sup_time_generating:                    0.
% 7.31/1.51  sup_time_sim_full:                      0.
% 7.31/1.51  sup_time_sim_immed:                     0.
% 7.31/1.51  
% 7.31/1.51  sup_num_of_clauses:                     2520
% 7.31/1.51  sup_num_in_active:                      122
% 7.31/1.51  sup_num_in_passive:                     2398
% 7.31/1.51  sup_num_of_loops:                       131
% 7.31/1.51  sup_fw_superposition:                   8322
% 7.31/1.51  sup_bw_superposition:                   6428
% 7.31/1.51  sup_immediate_simplified:               7515
% 7.31/1.51  sup_given_eliminated:                   1
% 7.31/1.51  comparisons_done:                       0
% 7.31/1.51  comparisons_avoided:                    0
% 7.31/1.51  
% 7.31/1.51  ------ Simplifications
% 7.31/1.51  
% 7.31/1.51  
% 7.31/1.51  sim_fw_subset_subsumed:                 0
% 7.31/1.51  sim_bw_subset_subsumed:                 0
% 7.31/1.51  sim_fw_subsumed:                        1323
% 7.31/1.51  sim_bw_subsumed:                        24
% 7.31/1.51  sim_fw_subsumption_res:                 0
% 7.31/1.51  sim_bw_subsumption_res:                 0
% 7.31/1.51  sim_tautology_del:                      0
% 7.31/1.51  sim_eq_tautology_del:                   2188
% 7.31/1.51  sim_eq_res_simp:                        0
% 7.31/1.51  sim_fw_demodulated:                     4667
% 7.31/1.51  sim_bw_demodulated:                     50
% 7.31/1.51  sim_light_normalised:                   2934
% 7.31/1.51  sim_joinable_taut:                      0
% 7.31/1.51  sim_joinable_simp:                      0
% 7.31/1.51  sim_ac_normalised:                      0
% 7.31/1.51  sim_smt_subsumption:                    0
% 7.31/1.51  
%------------------------------------------------------------------------------
