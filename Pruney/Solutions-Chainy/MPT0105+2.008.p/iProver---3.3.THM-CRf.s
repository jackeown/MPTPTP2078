%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:13 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  157 (219194 expanded)
%              Number of clauses        :  122 (79533 expanded)
%              Number of leaves         :   13 (63081 expanded)
%              Depth                    :   36
%              Number of atoms          :  158 (219195 expanded)
%              Number of equality atoms :  157 (219194 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f20])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f29,f20,f20,f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f19,f20,f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f25,f25])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f30,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
    inference(definition_unfolding,[],[f30,f20])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_32,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_3])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_39,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32,c_5])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_35,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_0,c_4])).

cnf(c_504,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X0))),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)))) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_39,c_35])).

cnf(c_508,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0),k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_504,c_3,c_39])).

cnf(c_87,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_91,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_39,c_4])).

cnf(c_108,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_91,c_5])).

cnf(c_2,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_155,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_175,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_155,c_3,c_32,c_108])).

cnf(c_509,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_508,c_87,c_108,c_175])).

cnf(c_510,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_509,c_3,c_87,c_175])).

cnf(c_159,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_172,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_159,c_3,c_108])).

cnf(c_176,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_175,c_172])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_33,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_7,c_4])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_39,c_33])).

cnf(c_75,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_66,c_3,c_39])).

cnf(c_391,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_75])).

cnf(c_1813,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_176,c_391])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_113,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_820,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_113])).

cnf(c_905,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_820,c_113])).

cnf(c_906,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_905,c_4])).

cnf(c_1884,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1813,c_4,c_176,c_906])).

cnf(c_1959,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1884,c_391])).

cnf(c_1971,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1959,c_175])).

cnf(c_2049,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0),k2_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1971,c_391])).

cnf(c_2073,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2049,c_4,c_175])).

cnf(c_3108,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_510,c_2073])).

cnf(c_5129,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3108,c_1])).

cnf(c_5156,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_5129,c_3,c_1884])).

cnf(c_64,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5,c_33])).

cnf(c_76,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_64,c_3,c_39])).

cnf(c_5109,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3108,c_76])).

cnf(c_5282,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5109,c_5156])).

cnf(c_92,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_4,c_4])).

cnf(c_107,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_92,c_4])).

cnf(c_5283,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5282,c_87,c_107,c_175])).

cnf(c_8381,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5156,c_5283])).

cnf(c_8574,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8381,c_1])).

cnf(c_8612,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8574,c_8381])).

cnf(c_8613,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_8612,c_3])).

cnf(c_67,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_33,c_1])).

cnf(c_74,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_67,c_4])).

cnf(c_8944,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8381,c_74])).

cnf(c_9205,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8944,c_5,c_87])).

cnf(c_9502,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9205,c_4])).

cnf(c_97,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_9528,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9502,c_97,c_176])).

cnf(c_10179,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8613,c_9528])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_39])).

cnf(c_10492,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10179,c_102])).

cnf(c_572,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_102])).

cnf(c_10186,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9528,c_572])).

cnf(c_10272,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10186,c_3,c_1884])).

cnf(c_11110,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10272,c_74])).

cnf(c_11136,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_11110,c_1884])).

cnf(c_10214,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9528,c_1])).

cnf(c_10251,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_10214,c_3,c_1884])).

cnf(c_11137,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_11136,c_3,c_4,c_87,c_10251])).

cnf(c_11331,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11137,c_11137])).

cnf(c_14052,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_11331,c_10251])).

cnf(c_38797,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10492,c_14052])).

cnf(c_8568,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0)))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8381,c_35])).

cnf(c_8621,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_8568,c_8381])).

cnf(c_8622,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_8621,c_3,c_87,c_108,c_175])).

cnf(c_8623,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8622,c_3,c_87])).

cnf(c_10579,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8623,c_10251])).

cnf(c_10726,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_10579,c_8381])).

cnf(c_11106,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10272,c_113])).

cnf(c_11141,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_11106,c_10726])).

cnf(c_1963,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1884,c_33])).

cnf(c_1969,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1963,c_3,c_39])).

cnf(c_2656,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_102,c_1969])).

cnf(c_2753,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2656,c_87,c_175])).

cnf(c_4035,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1971,c_2753])).

cnf(c_4172,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4035,c_176])).

cnf(c_10208,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9528,c_4])).

cnf(c_10261,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_10208,c_4])).

cnf(c_11142,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11141,c_4172,c_10261])).

cnf(c_10502,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10179,c_1])).

cnf(c_10539,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10502,c_3,c_5])).

cnf(c_23378,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11142,c_10539])).

cnf(c_11076,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_10272,c_10251])).

cnf(c_10474,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10179,c_572])).

cnf(c_10560,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10474,c_3,c_5])).

cnf(c_10588,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1971,c_10251])).

cnf(c_11653,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_10588,c_3])).

cnf(c_11691,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_11653])).

cnf(c_13521,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_10560,c_11691])).

cnf(c_13636,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(light_normalisation,[status(thm)],[c_13521,c_10726])).

cnf(c_23464,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_23378,c_11076,c_13636])).

cnf(c_8806,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8613,c_5156])).

cnf(c_10091,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_8806,c_8806])).

cnf(c_10167,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_10091,c_5156])).

cnf(c_11701,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_10179,c_11653])).

cnf(c_27029,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_10167,c_11701])).

cnf(c_10292,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10167,c_10167])).

cnf(c_9396,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8623,c_8613])).

cnf(c_10372,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_10292,c_9396])).

cnf(c_10748,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10372,c_8806])).

cnf(c_10828,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_10748,c_10372])).

cnf(c_27235,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_27029,c_5,c_10828])).

cnf(c_39020,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_38797,c_10726,c_23464,c_27235])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_34,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10,c_4])).

cnf(c_553,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_510,c_34])).

cnf(c_8668,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8613,c_553])).

cnf(c_11236,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11137,c_8668])).

cnf(c_11545,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_8613,c_11236])).

cnf(c_39070,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_39020,c_11545])).

cnf(c_39468,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8613,c_39070])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:26:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 11.53/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/1.98  
% 11.53/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/1.98  
% 11.53/1.98  ------  iProver source info
% 11.53/1.98  
% 11.53/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.53/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/1.98  git: non_committed_changes: false
% 11.53/1.98  git: last_make_outside_of_git: false
% 11.53/1.98  
% 11.53/1.98  ------ 
% 11.53/1.98  
% 11.53/1.98  ------ Input Options
% 11.53/1.98  
% 11.53/1.98  --out_options                           all
% 11.53/1.98  --tptp_safe_out                         true
% 11.53/1.98  --problem_path                          ""
% 11.53/1.98  --include_path                          ""
% 11.53/1.98  --clausifier                            res/vclausify_rel
% 11.53/1.98  --clausifier_options                    ""
% 11.53/1.98  --stdin                                 false
% 11.53/1.98  --stats_out                             all
% 11.53/1.98  
% 11.53/1.98  ------ General Options
% 11.53/1.98  
% 11.53/1.98  --fof                                   false
% 11.53/1.98  --time_out_real                         305.
% 11.53/1.98  --time_out_virtual                      -1.
% 11.53/1.98  --symbol_type_check                     false
% 11.53/1.98  --clausify_out                          false
% 11.53/1.98  --sig_cnt_out                           false
% 11.53/1.98  --trig_cnt_out                          false
% 11.53/1.98  --trig_cnt_out_tolerance                1.
% 11.53/1.98  --trig_cnt_out_sk_spl                   false
% 11.53/1.98  --abstr_cl_out                          false
% 11.53/1.98  
% 11.53/1.98  ------ Global Options
% 11.53/1.98  
% 11.53/1.98  --schedule                              default
% 11.53/1.98  --add_important_lit                     false
% 11.53/1.98  --prop_solver_per_cl                    1000
% 11.53/1.98  --min_unsat_core                        false
% 11.53/1.98  --soft_assumptions                      false
% 11.53/1.98  --soft_lemma_size                       3
% 11.53/1.98  --prop_impl_unit_size                   0
% 11.53/1.98  --prop_impl_unit                        []
% 11.53/1.98  --share_sel_clauses                     true
% 11.53/1.98  --reset_solvers                         false
% 11.53/1.98  --bc_imp_inh                            [conj_cone]
% 11.53/1.98  --conj_cone_tolerance                   3.
% 11.53/1.98  --extra_neg_conj                        none
% 11.53/1.98  --large_theory_mode                     true
% 11.53/1.98  --prolific_symb_bound                   200
% 11.53/1.98  --lt_threshold                          2000
% 11.53/1.98  --clause_weak_htbl                      true
% 11.53/1.98  --gc_record_bc_elim                     false
% 11.53/1.98  
% 11.53/1.98  ------ Preprocessing Options
% 11.53/1.98  
% 11.53/1.98  --preprocessing_flag                    true
% 11.53/1.98  --time_out_prep_mult                    0.1
% 11.53/1.98  --splitting_mode                        input
% 11.53/1.98  --splitting_grd                         true
% 11.53/1.98  --splitting_cvd                         false
% 11.53/1.98  --splitting_cvd_svl                     false
% 11.53/1.98  --splitting_nvd                         32
% 11.53/1.98  --sub_typing                            true
% 11.53/1.98  --prep_gs_sim                           true
% 11.53/1.98  --prep_unflatten                        true
% 11.53/1.98  --prep_res_sim                          true
% 11.53/1.98  --prep_upred                            true
% 11.53/1.98  --prep_sem_filter                       exhaustive
% 11.53/1.98  --prep_sem_filter_out                   false
% 11.53/1.98  --pred_elim                             true
% 11.53/1.98  --res_sim_input                         true
% 11.53/1.98  --eq_ax_congr_red                       true
% 11.53/1.98  --pure_diseq_elim                       true
% 11.53/1.98  --brand_transform                       false
% 11.53/1.98  --non_eq_to_eq                          false
% 11.53/1.98  --prep_def_merge                        true
% 11.53/1.98  --prep_def_merge_prop_impl              false
% 11.53/1.98  --prep_def_merge_mbd                    true
% 11.53/1.98  --prep_def_merge_tr_red                 false
% 11.53/1.98  --prep_def_merge_tr_cl                  false
% 11.53/1.98  --smt_preprocessing                     true
% 11.53/1.98  --smt_ac_axioms                         fast
% 11.53/1.98  --preprocessed_out                      false
% 11.53/1.98  --preprocessed_stats                    false
% 11.53/1.98  
% 11.53/1.98  ------ Abstraction refinement Options
% 11.53/1.98  
% 11.53/1.98  --abstr_ref                             []
% 11.53/1.98  --abstr_ref_prep                        false
% 11.53/1.98  --abstr_ref_until_sat                   false
% 11.53/1.98  --abstr_ref_sig_restrict                funpre
% 11.53/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.98  --abstr_ref_under                       []
% 11.53/1.98  
% 11.53/1.98  ------ SAT Options
% 11.53/1.98  
% 11.53/1.98  --sat_mode                              false
% 11.53/1.98  --sat_fm_restart_options                ""
% 11.53/1.98  --sat_gr_def                            false
% 11.53/1.98  --sat_epr_types                         true
% 11.53/1.98  --sat_non_cyclic_types                  false
% 11.53/1.98  --sat_finite_models                     false
% 11.53/1.98  --sat_fm_lemmas                         false
% 11.53/1.98  --sat_fm_prep                           false
% 11.53/1.98  --sat_fm_uc_incr                        true
% 11.53/1.98  --sat_out_model                         small
% 11.53/1.98  --sat_out_clauses                       false
% 11.53/1.98  
% 11.53/1.98  ------ QBF Options
% 11.53/1.98  
% 11.53/1.98  --qbf_mode                              false
% 11.53/1.98  --qbf_elim_univ                         false
% 11.53/1.98  --qbf_dom_inst                          none
% 11.53/1.98  --qbf_dom_pre_inst                      false
% 11.53/1.98  --qbf_sk_in                             false
% 11.53/1.98  --qbf_pred_elim                         true
% 11.53/1.98  --qbf_split                             512
% 11.53/1.98  
% 11.53/1.98  ------ BMC1 Options
% 11.53/1.98  
% 11.53/1.98  --bmc1_incremental                      false
% 11.53/1.98  --bmc1_axioms                           reachable_all
% 11.53/1.98  --bmc1_min_bound                        0
% 11.53/1.98  --bmc1_max_bound                        -1
% 11.53/1.98  --bmc1_max_bound_default                -1
% 11.53/1.98  --bmc1_symbol_reachability              true
% 11.53/1.98  --bmc1_property_lemmas                  false
% 11.53/1.98  --bmc1_k_induction                      false
% 11.53/1.98  --bmc1_non_equiv_states                 false
% 11.53/1.98  --bmc1_deadlock                         false
% 11.53/1.98  --bmc1_ucm                              false
% 11.53/1.98  --bmc1_add_unsat_core                   none
% 11.53/1.98  --bmc1_unsat_core_children              false
% 11.53/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.98  --bmc1_out_stat                         full
% 11.53/1.98  --bmc1_ground_init                      false
% 11.53/1.98  --bmc1_pre_inst_next_state              false
% 11.53/1.98  --bmc1_pre_inst_state                   false
% 11.53/1.98  --bmc1_pre_inst_reach_state             false
% 11.53/1.98  --bmc1_out_unsat_core                   false
% 11.53/1.98  --bmc1_aig_witness_out                  false
% 11.53/1.98  --bmc1_verbose                          false
% 11.53/1.98  --bmc1_dump_clauses_tptp                false
% 11.53/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.98  --bmc1_dump_file                        -
% 11.53/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.98  --bmc1_ucm_extend_mode                  1
% 11.53/1.98  --bmc1_ucm_init_mode                    2
% 11.53/1.98  --bmc1_ucm_cone_mode                    none
% 11.53/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.98  --bmc1_ucm_relax_model                  4
% 11.53/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.98  --bmc1_ucm_layered_model                none
% 11.53/1.98  --bmc1_ucm_max_lemma_size               10
% 11.53/1.98  
% 11.53/1.98  ------ AIG Options
% 11.53/1.98  
% 11.53/1.98  --aig_mode                              false
% 11.53/1.98  
% 11.53/1.98  ------ Instantiation Options
% 11.53/1.98  
% 11.53/1.98  --instantiation_flag                    true
% 11.53/1.98  --inst_sos_flag                         true
% 11.53/1.98  --inst_sos_phase                        true
% 11.53/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.98  --inst_lit_sel_side                     num_symb
% 11.53/1.98  --inst_solver_per_active                1400
% 11.53/1.98  --inst_solver_calls_frac                1.
% 11.53/1.98  --inst_passive_queue_type               priority_queues
% 11.53/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.98  --inst_passive_queues_freq              [25;2]
% 11.53/1.98  --inst_dismatching                      true
% 11.53/1.98  --inst_eager_unprocessed_to_passive     true
% 11.53/1.98  --inst_prop_sim_given                   true
% 11.53/1.98  --inst_prop_sim_new                     false
% 11.53/1.98  --inst_subs_new                         false
% 11.53/1.98  --inst_eq_res_simp                      false
% 11.53/1.98  --inst_subs_given                       false
% 11.53/1.98  --inst_orphan_elimination               true
% 11.53/1.98  --inst_learning_loop_flag               true
% 11.53/1.98  --inst_learning_start                   3000
% 11.53/1.98  --inst_learning_factor                  2
% 11.53/1.98  --inst_start_prop_sim_after_learn       3
% 11.53/1.98  --inst_sel_renew                        solver
% 11.53/1.98  --inst_lit_activity_flag                true
% 11.53/1.98  --inst_restr_to_given                   false
% 11.53/1.98  --inst_activity_threshold               500
% 11.53/1.98  --inst_out_proof                        true
% 11.53/1.98  
% 11.53/1.98  ------ Resolution Options
% 11.53/1.98  
% 11.53/1.98  --resolution_flag                       true
% 11.53/1.98  --res_lit_sel                           adaptive
% 11.53/1.98  --res_lit_sel_side                      none
% 11.53/1.98  --res_ordering                          kbo
% 11.53/1.98  --res_to_prop_solver                    active
% 11.53/1.98  --res_prop_simpl_new                    false
% 11.53/1.98  --res_prop_simpl_given                  true
% 11.53/1.98  --res_passive_queue_type                priority_queues
% 11.53/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.98  --res_passive_queues_freq               [15;5]
% 11.53/1.98  --res_forward_subs                      full
% 11.53/1.98  --res_backward_subs                     full
% 11.53/1.98  --res_forward_subs_resolution           true
% 11.53/1.98  --res_backward_subs_resolution          true
% 11.53/1.98  --res_orphan_elimination                true
% 11.53/1.98  --res_time_limit                        2.
% 11.53/1.98  --res_out_proof                         true
% 11.53/1.98  
% 11.53/1.98  ------ Superposition Options
% 11.53/1.98  
% 11.53/1.98  --superposition_flag                    true
% 11.53/1.98  --sup_passive_queue_type                priority_queues
% 11.53/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.98  --demod_completeness_check              fast
% 11.53/1.98  --demod_use_ground                      true
% 11.53/1.98  --sup_to_prop_solver                    passive
% 11.53/1.98  --sup_prop_simpl_new                    true
% 11.53/1.98  --sup_prop_simpl_given                  true
% 11.53/1.98  --sup_fun_splitting                     true
% 11.53/1.98  --sup_smt_interval                      50000
% 11.53/1.98  
% 11.53/1.98  ------ Superposition Simplification Setup
% 11.53/1.98  
% 11.53/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/1.98  --sup_immed_triv                        [TrivRules]
% 11.53/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_immed_bw_main                     []
% 11.53/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_input_bw                          []
% 11.53/1.98  
% 11.53/1.98  ------ Combination Options
% 11.53/1.98  
% 11.53/1.98  --comb_res_mult                         3
% 11.53/1.98  --comb_sup_mult                         2
% 11.53/1.98  --comb_inst_mult                        10
% 11.53/1.98  
% 11.53/1.98  ------ Debug Options
% 11.53/1.98  
% 11.53/1.98  --dbg_backtrace                         false
% 11.53/1.98  --dbg_dump_prop_clauses                 false
% 11.53/1.98  --dbg_dump_prop_clauses_file            -
% 11.53/1.98  --dbg_out_stat                          false
% 11.53/1.98  ------ Parsing...
% 11.53/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/1.98  
% 11.53/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.53/1.98  
% 11.53/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/1.98  
% 11.53/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.53/1.98  ------ Proving...
% 11.53/1.98  ------ Problem Properties 
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  clauses                                 11
% 11.53/1.98  conjectures                             1
% 11.53/1.98  EPR                                     0
% 11.53/1.98  Horn                                    11
% 11.53/1.98  unary                                   11
% 11.53/1.98  binary                                  0
% 11.53/1.98  lits                                    11
% 11.53/1.98  lits eq                                 11
% 11.53/1.98  fd_pure                                 0
% 11.53/1.98  fd_pseudo                               0
% 11.53/1.98  fd_cond                                 0
% 11.53/1.98  fd_pseudo_cond                          0
% 11.53/1.98  AC symbols                              0
% 11.53/1.98  
% 11.53/1.98  ------ Schedule UEQ
% 11.53/1.98  
% 11.53/1.98  ------ pure equality problem: resolution off 
% 11.53/1.98  
% 11.53/1.98  ------ Option_UEQ Time Limit: Unbounded
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  ------ 
% 11.53/1.98  Current options:
% 11.53/1.98  ------ 
% 11.53/1.98  
% 11.53/1.98  ------ Input Options
% 11.53/1.98  
% 11.53/1.98  --out_options                           all
% 11.53/1.98  --tptp_safe_out                         true
% 11.53/1.98  --problem_path                          ""
% 11.53/1.98  --include_path                          ""
% 11.53/1.98  --clausifier                            res/vclausify_rel
% 11.53/1.98  --clausifier_options                    ""
% 11.53/1.98  --stdin                                 false
% 11.53/1.98  --stats_out                             all
% 11.53/1.98  
% 11.53/1.98  ------ General Options
% 11.53/1.98  
% 11.53/1.98  --fof                                   false
% 11.53/1.98  --time_out_real                         305.
% 11.53/1.98  --time_out_virtual                      -1.
% 11.53/1.98  --symbol_type_check                     false
% 11.53/1.98  --clausify_out                          false
% 11.53/1.98  --sig_cnt_out                           false
% 11.53/1.98  --trig_cnt_out                          false
% 11.53/1.98  --trig_cnt_out_tolerance                1.
% 11.53/1.98  --trig_cnt_out_sk_spl                   false
% 11.53/1.98  --abstr_cl_out                          false
% 11.53/1.98  
% 11.53/1.98  ------ Global Options
% 11.53/1.98  
% 11.53/1.98  --schedule                              default
% 11.53/1.98  --add_important_lit                     false
% 11.53/1.98  --prop_solver_per_cl                    1000
% 11.53/1.98  --min_unsat_core                        false
% 11.53/1.98  --soft_assumptions                      false
% 11.53/1.98  --soft_lemma_size                       3
% 11.53/1.98  --prop_impl_unit_size                   0
% 11.53/1.98  --prop_impl_unit                        []
% 11.53/1.98  --share_sel_clauses                     true
% 11.53/1.98  --reset_solvers                         false
% 11.53/1.98  --bc_imp_inh                            [conj_cone]
% 11.53/1.98  --conj_cone_tolerance                   3.
% 11.53/1.98  --extra_neg_conj                        none
% 11.53/1.98  --large_theory_mode                     true
% 11.53/1.98  --prolific_symb_bound                   200
% 11.53/1.98  --lt_threshold                          2000
% 11.53/1.98  --clause_weak_htbl                      true
% 11.53/1.98  --gc_record_bc_elim                     false
% 11.53/1.98  
% 11.53/1.98  ------ Preprocessing Options
% 11.53/1.98  
% 11.53/1.98  --preprocessing_flag                    true
% 11.53/1.98  --time_out_prep_mult                    0.1
% 11.53/1.98  --splitting_mode                        input
% 11.53/1.98  --splitting_grd                         true
% 11.53/1.98  --splitting_cvd                         false
% 11.53/1.98  --splitting_cvd_svl                     false
% 11.53/1.98  --splitting_nvd                         32
% 11.53/1.98  --sub_typing                            true
% 11.53/1.98  --prep_gs_sim                           true
% 11.53/1.98  --prep_unflatten                        true
% 11.53/1.98  --prep_res_sim                          true
% 11.53/1.98  --prep_upred                            true
% 11.53/1.98  --prep_sem_filter                       exhaustive
% 11.53/1.98  --prep_sem_filter_out                   false
% 11.53/1.98  --pred_elim                             true
% 11.53/1.98  --res_sim_input                         true
% 11.53/1.98  --eq_ax_congr_red                       true
% 11.53/1.98  --pure_diseq_elim                       true
% 11.53/1.98  --brand_transform                       false
% 11.53/1.98  --non_eq_to_eq                          false
% 11.53/1.98  --prep_def_merge                        true
% 11.53/1.98  --prep_def_merge_prop_impl              false
% 11.53/1.98  --prep_def_merge_mbd                    true
% 11.53/1.98  --prep_def_merge_tr_red                 false
% 11.53/1.98  --prep_def_merge_tr_cl                  false
% 11.53/1.98  --smt_preprocessing                     true
% 11.53/1.98  --smt_ac_axioms                         fast
% 11.53/1.98  --preprocessed_out                      false
% 11.53/1.98  --preprocessed_stats                    false
% 11.53/1.98  
% 11.53/1.98  ------ Abstraction refinement Options
% 11.53/1.98  
% 11.53/1.98  --abstr_ref                             []
% 11.53/1.98  --abstr_ref_prep                        false
% 11.53/1.98  --abstr_ref_until_sat                   false
% 11.53/1.98  --abstr_ref_sig_restrict                funpre
% 11.53/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.98  --abstr_ref_under                       []
% 11.53/1.98  
% 11.53/1.98  ------ SAT Options
% 11.53/1.98  
% 11.53/1.98  --sat_mode                              false
% 11.53/1.98  --sat_fm_restart_options                ""
% 11.53/1.98  --sat_gr_def                            false
% 11.53/1.98  --sat_epr_types                         true
% 11.53/1.98  --sat_non_cyclic_types                  false
% 11.53/1.98  --sat_finite_models                     false
% 11.53/1.98  --sat_fm_lemmas                         false
% 11.53/1.98  --sat_fm_prep                           false
% 11.53/1.98  --sat_fm_uc_incr                        true
% 11.53/1.98  --sat_out_model                         small
% 11.53/1.98  --sat_out_clauses                       false
% 11.53/1.98  
% 11.53/1.98  ------ QBF Options
% 11.53/1.98  
% 11.53/1.98  --qbf_mode                              false
% 11.53/1.98  --qbf_elim_univ                         false
% 11.53/1.98  --qbf_dom_inst                          none
% 11.53/1.98  --qbf_dom_pre_inst                      false
% 11.53/1.98  --qbf_sk_in                             false
% 11.53/1.98  --qbf_pred_elim                         true
% 11.53/1.98  --qbf_split                             512
% 11.53/1.98  
% 11.53/1.98  ------ BMC1 Options
% 11.53/1.98  
% 11.53/1.98  --bmc1_incremental                      false
% 11.53/1.98  --bmc1_axioms                           reachable_all
% 11.53/1.98  --bmc1_min_bound                        0
% 11.53/1.98  --bmc1_max_bound                        -1
% 11.53/1.98  --bmc1_max_bound_default                -1
% 11.53/1.98  --bmc1_symbol_reachability              true
% 11.53/1.98  --bmc1_property_lemmas                  false
% 11.53/1.98  --bmc1_k_induction                      false
% 11.53/1.98  --bmc1_non_equiv_states                 false
% 11.53/1.98  --bmc1_deadlock                         false
% 11.53/1.98  --bmc1_ucm                              false
% 11.53/1.98  --bmc1_add_unsat_core                   none
% 11.53/1.98  --bmc1_unsat_core_children              false
% 11.53/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.98  --bmc1_out_stat                         full
% 11.53/1.98  --bmc1_ground_init                      false
% 11.53/1.98  --bmc1_pre_inst_next_state              false
% 11.53/1.98  --bmc1_pre_inst_state                   false
% 11.53/1.98  --bmc1_pre_inst_reach_state             false
% 11.53/1.98  --bmc1_out_unsat_core                   false
% 11.53/1.98  --bmc1_aig_witness_out                  false
% 11.53/1.98  --bmc1_verbose                          false
% 11.53/1.98  --bmc1_dump_clauses_tptp                false
% 11.53/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.98  --bmc1_dump_file                        -
% 11.53/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.98  --bmc1_ucm_extend_mode                  1
% 11.53/1.98  --bmc1_ucm_init_mode                    2
% 11.53/1.98  --bmc1_ucm_cone_mode                    none
% 11.53/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.98  --bmc1_ucm_relax_model                  4
% 11.53/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.98  --bmc1_ucm_layered_model                none
% 11.53/1.98  --bmc1_ucm_max_lemma_size               10
% 11.53/1.98  
% 11.53/1.98  ------ AIG Options
% 11.53/1.98  
% 11.53/1.98  --aig_mode                              false
% 11.53/1.98  
% 11.53/1.98  ------ Instantiation Options
% 11.53/1.98  
% 11.53/1.98  --instantiation_flag                    false
% 11.53/1.98  --inst_sos_flag                         true
% 11.53/1.98  --inst_sos_phase                        true
% 11.53/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.98  --inst_lit_sel_side                     num_symb
% 11.53/1.98  --inst_solver_per_active                1400
% 11.53/1.98  --inst_solver_calls_frac                1.
% 11.53/1.98  --inst_passive_queue_type               priority_queues
% 11.53/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.98  --inst_passive_queues_freq              [25;2]
% 11.53/1.98  --inst_dismatching                      true
% 11.53/1.98  --inst_eager_unprocessed_to_passive     true
% 11.53/1.98  --inst_prop_sim_given                   true
% 11.53/1.98  --inst_prop_sim_new                     false
% 11.53/1.98  --inst_subs_new                         false
% 11.53/1.98  --inst_eq_res_simp                      false
% 11.53/1.98  --inst_subs_given                       false
% 11.53/1.98  --inst_orphan_elimination               true
% 11.53/1.98  --inst_learning_loop_flag               true
% 11.53/1.98  --inst_learning_start                   3000
% 11.53/1.98  --inst_learning_factor                  2
% 11.53/1.98  --inst_start_prop_sim_after_learn       3
% 11.53/1.98  --inst_sel_renew                        solver
% 11.53/1.98  --inst_lit_activity_flag                true
% 11.53/1.98  --inst_restr_to_given                   false
% 11.53/1.98  --inst_activity_threshold               500
% 11.53/1.98  --inst_out_proof                        true
% 11.53/1.98  
% 11.53/1.98  ------ Resolution Options
% 11.53/1.98  
% 11.53/1.98  --resolution_flag                       false
% 11.53/1.98  --res_lit_sel                           adaptive
% 11.53/1.98  --res_lit_sel_side                      none
% 11.53/1.98  --res_ordering                          kbo
% 11.53/1.98  --res_to_prop_solver                    active
% 11.53/1.98  --res_prop_simpl_new                    false
% 11.53/1.98  --res_prop_simpl_given                  true
% 11.53/1.98  --res_passive_queue_type                priority_queues
% 11.53/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.98  --res_passive_queues_freq               [15;5]
% 11.53/1.98  --res_forward_subs                      full
% 11.53/1.98  --res_backward_subs                     full
% 11.53/1.98  --res_forward_subs_resolution           true
% 11.53/1.98  --res_backward_subs_resolution          true
% 11.53/1.98  --res_orphan_elimination                true
% 11.53/1.98  --res_time_limit                        2.
% 11.53/1.98  --res_out_proof                         true
% 11.53/1.98  
% 11.53/1.98  ------ Superposition Options
% 11.53/1.98  
% 11.53/1.98  --superposition_flag                    true
% 11.53/1.98  --sup_passive_queue_type                priority_queues
% 11.53/1.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.98  --demod_completeness_check              fast
% 11.53/1.98  --demod_use_ground                      true
% 11.53/1.98  --sup_to_prop_solver                    active
% 11.53/1.98  --sup_prop_simpl_new                    false
% 11.53/1.98  --sup_prop_simpl_given                  false
% 11.53/1.98  --sup_fun_splitting                     true
% 11.53/1.98  --sup_smt_interval                      10000
% 11.53/1.98  
% 11.53/1.98  ------ Superposition Simplification Setup
% 11.53/1.98  
% 11.53/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.98  --sup_full_triv                         [TrivRules]
% 11.53/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/1.98  --sup_immed_triv                        [TrivRules]
% 11.53/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_immed_bw_main                     []
% 11.53/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.53/1.98  
% 11.53/1.98  ------ Combination Options
% 11.53/1.98  
% 11.53/1.98  --comb_res_mult                         1
% 11.53/1.98  --comb_sup_mult                         1
% 11.53/1.98  --comb_inst_mult                        1000000
% 11.53/1.98  
% 11.53/1.98  ------ Debug Options
% 11.53/1.98  
% 11.53/1.98  --dbg_backtrace                         false
% 11.53/1.98  --dbg_dump_prop_clauses                 false
% 11.53/1.98  --dbg_dump_prop_clauses_file            -
% 11.53/1.98  --dbg_out_stat                          false
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  ------ Proving...
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  % SZS status Theorem for theBenchmark.p
% 11.53/1.98  
% 11.53/1.98   Resolution empty clause
% 11.53/1.98  
% 11.53/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/1.98  
% 11.53/1.98  fof(f10,axiom,(
% 11.53/1.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f27,plain,(
% 11.53/1.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.53/1.98    inference(cnf_transformation,[],[f10])).
% 11.53/1.98  
% 11.53/1.98  fof(f3,axiom,(
% 11.53/1.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f20,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f3])).
% 11.53/1.98  
% 11.53/1.98  fof(f36,plain,(
% 11.53/1.98    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 11.53/1.98    inference(definition_unfolding,[],[f27,f20])).
% 11.53/1.98  
% 11.53/1.98  fof(f4,axiom,(
% 11.53/1.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f21,plain,(
% 11.53/1.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.53/1.98    inference(cnf_transformation,[],[f4])).
% 11.53/1.98  
% 11.53/1.98  fof(f6,axiom,(
% 11.53/1.98    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f23,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 11.53/1.98    inference(cnf_transformation,[],[f6])).
% 11.53/1.98  
% 11.53/1.98  fof(f12,axiom,(
% 11.53/1.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f29,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f12])).
% 11.53/1.98  
% 11.53/1.98  fof(f8,axiom,(
% 11.53/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f25,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f8])).
% 11.53/1.98  
% 11.53/1.98  fof(f31,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f29,f20,f20,f25])).
% 11.53/1.98  
% 11.53/1.98  fof(f5,axiom,(
% 11.53/1.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f22,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f5])).
% 11.53/1.98  
% 11.53/1.98  fof(f2,axiom,(
% 11.53/1.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f19,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f2])).
% 11.53/1.98  
% 11.53/1.98  fof(f33,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f19,f20,f20])).
% 11.53/1.98  
% 11.53/1.98  fof(f9,axiom,(
% 11.53/1.98    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f26,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f9])).
% 11.53/1.98  
% 11.53/1.98  fof(f35,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 11.53/1.98    inference(definition_unfolding,[],[f26,f25,f25])).
% 11.53/1.98  
% 11.53/1.98  fof(f1,axiom,(
% 11.53/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f18,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f1])).
% 11.53/1.98  
% 11.53/1.98  fof(f32,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f18,f25,f25])).
% 11.53/1.98  
% 11.53/1.98  fof(f7,axiom,(
% 11.53/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f24,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f7])).
% 11.53/1.98  
% 11.53/1.98  fof(f34,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f24,f25])).
% 11.53/1.98  
% 11.53/1.98  fof(f13,conjecture,(
% 11.53/1.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f14,negated_conjecture,(
% 11.53/1.98    ~! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.53/1.98    inference(negated_conjecture,[],[f13])).
% 11.53/1.98  
% 11.53/1.98  fof(f15,plain,(
% 11.53/1.98    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1)),
% 11.53/1.98    inference(ennf_transformation,[],[f14])).
% 11.53/1.98  
% 11.53/1.98  fof(f16,plain,(
% 11.53/1.98    ? [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_xboole_0(X0,X1) => k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 11.53/1.98    introduced(choice_axiom,[])).
% 11.53/1.98  
% 11.53/1.98  fof(f17,plain,(
% 11.53/1.98    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 11.53/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 11.53/1.98  
% 11.53/1.98  fof(f30,plain,(
% 11.53/1.98    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1)),
% 11.53/1.98    inference(cnf_transformation,[],[f17])).
% 11.53/1.98  
% 11.53/1.98  fof(f38,plain,(
% 11.53/1.98    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))),
% 11.53/1.98    inference(definition_unfolding,[],[f30,f20])).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.53/1.98      inference(cnf_transformation,[],[f36]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_3,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.53/1.98      inference(cnf_transformation,[],[f21]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_32,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_8,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_5,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.53/1.98      inference(cnf_transformation,[],[f23]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_39,plain,
% 11.53/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_32,c_5]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_0,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(cnf_transformation,[],[f31]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_4,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.53/1.98      inference(cnf_transformation,[],[f22]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_35,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_0,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_504,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X0))),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)))) = k2_xboole_0(X0,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_39,c_35]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_508,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0),k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))) = k2_xboole_0(X0,X0) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_504,c_3,c_39]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_87,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_91,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_39,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_108,plain,
% 11.53/1.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_91,c_5]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
% 11.53/1.98      inference(cnf_transformation,[],[f33]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_155,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_175,plain,
% 11.53/1.98      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_155,c_3,c_32,c_108]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_509,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(X0,X0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_508,c_87,c_108,c_175]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_510,plain,
% 11.53/1.98      ( k2_xboole_0(X0,X0) = X0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_509,c_3,c_87,c_175]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_159,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_172,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_159,c_3,c_108]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_176,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_175,c_172]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_7,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.53/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_33,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_7,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_66,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_39,c_33]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_75,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_66,c_3,c_39]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_391,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2)) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_4,c_75]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1813,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_176,c_391]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.53/1.98      inference(cnf_transformation,[],[f32]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_6,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_113,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_820,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1,c_113]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_905,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_820,c_113]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_906,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_905,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1884,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_1813,c_4,c_176,c_906]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1959,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1884,c_391]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1971,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_1959,c_175]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2049,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0),k2_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1971,c_391]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2073,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X1)) = k1_xboole_0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_2049,c_4,c_175]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_3108,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_510,c_2073]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_5129,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),k1_xboole_0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3108,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_5156,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_5129,c_3,c_1884]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_64,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_5,c_33]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_76,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_64,c_3,c_39]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_5109,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3108,c_76]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_5282,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_5109,c_5156]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_92,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_4,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_107,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_92,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_5283,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_5282,c_87,c_107,c_175]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8381,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_5156,c_5283]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8574,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8381,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8612,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_8574,c_8381]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8613,plain,
% 11.53/1.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_8612,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_67,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_33,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_74,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_67,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8944,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X1)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8381,c_74]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_9205,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_8944,c_5,c_87]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_9502,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_9205,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_97,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_9528,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_9502,c_97,c_176]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10179,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8613,c_9528]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_102,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_4,c_39]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10492,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10179,c_102]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_572,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1,c_102]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10186,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_9528,c_572]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10272,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_10186,c_3,c_1884]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11110,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10272,c_74]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11136,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_11110,c_1884]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10214,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_9528,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10251,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_10214,c_3,c_1884]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11137,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_11136,c_3,c_4,c_87,c_10251]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11331,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_11137,c_11137]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_14052,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_11331,c_10251]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_38797,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10492,c_14052]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8568,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0)))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8381,c_35]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8621,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_8568,c_8381]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8622,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_8621,c_3,c_87,c_108,c_175]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8623,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_8622,c_3,c_87]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10579,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8623,c_10251]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10726,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_10579,c_8381]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11106,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10272,c_113]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11141,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1)) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_11106,c_10726]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1963,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1884,c_33]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1969,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = k1_xboole_0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_1963,c_3,c_39]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2656,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2))))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_102,c_1969]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2753,plain,
% 11.53/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2)))) = k1_xboole_0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_2656,c_87,c_175]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_4035,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1971,c_2753]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_4172,plain,
% 11.53/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_4035,c_176]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10208,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_9528,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10261,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_10208,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11142,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_11141,c_4172,c_10261]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10502,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10179,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10539,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_10502,c_3,c_5]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_23378,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_11142,c_10539]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11076,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10272,c_10251]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10474,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10179,c_572]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10560,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k1_xboole_0 ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_10474,c_3,c_5]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10588,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1971,c_10251]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11653,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10588,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11691,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1,c_11653]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_13521,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10560,c_11691]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_13636,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_13521,c_10726]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_23464,plain,
% 11.53/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_23378,c_11076,c_13636]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8806,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8613,c_5156]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10091,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8806,c_8806]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10167,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_10091,c_5156]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11701,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10179,c_11653]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_27029,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10167,c_11701]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10292,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10167,c_10167]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_9396,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8623,c_8613]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10372,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_10292,c_9396]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10748,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_10372,c_8806]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10828,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_10748,c_10372]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_27235,plain,
% 11.53/1.98      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(light_normalisation,[status(thm)],[c_27029,c_5,c_10828]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_39020,plain,
% 11.53/1.98      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_38797,c_10726,c_23464,c_27235]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_10,negated_conjecture,
% 11.53/1.98      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
% 11.53/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_34,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK0))) != k2_xboole_0(sK0,sK1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_10,c_4]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_553,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_510,c_34]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_8668,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_8613,c_553]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11236,plain,
% 11.53/1.98      ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) != k2_xboole_0(sK0,sK1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_11137,c_8668]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_11545,plain,
% 11.53/1.98      ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8613,c_11236]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_39070,plain,
% 11.53/1.98      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_39020,c_11545]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_39468,plain,
% 11.53/1.98      ( $false ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_8613,c_39070]) ).
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/1.98  
% 11.53/1.98  ------                               Statistics
% 11.53/1.98  
% 11.53/1.98  ------ General
% 11.53/1.98  
% 11.53/1.98  abstr_ref_over_cycles:                  0
% 11.53/1.98  abstr_ref_under_cycles:                 0
% 11.53/1.98  gc_basic_clause_elim:                   0
% 11.53/1.98  forced_gc_time:                         0
% 11.53/1.98  parsing_time:                           0.006
% 11.53/1.98  unif_index_cands_time:                  0.
% 11.53/1.99  unif_index_add_time:                    0.
% 11.53/1.99  orderings_time:                         0.
% 11.53/1.99  out_proof_time:                         0.008
% 11.53/1.99  total_time:                             1.511
% 11.53/1.99  num_of_symbols:                         37
% 11.53/1.99  num_of_terms:                           91833
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing
% 11.53/1.99  
% 11.53/1.99  num_of_splits:                          0
% 11.53/1.99  num_of_split_atoms:                     1
% 11.53/1.99  num_of_reused_defs:                     1
% 11.53/1.99  num_eq_ax_congr_red:                    0
% 11.53/1.99  num_of_sem_filtered_clauses:            0
% 11.53/1.99  num_of_subtypes:                        0
% 11.53/1.99  monotx_restored_types:                  0
% 11.53/1.99  sat_num_of_epr_types:                   0
% 11.53/1.99  sat_num_of_non_cyclic_types:            0
% 11.53/1.99  sat_guarded_non_collapsed_types:        0
% 11.53/1.99  num_pure_diseq_elim:                    0
% 11.53/1.99  simp_replaced_by:                       0
% 11.53/1.99  res_preprocessed:                       26
% 11.53/1.99  prep_upred:                             0
% 11.53/1.99  prep_unflattend:                        0
% 11.53/1.99  smt_new_axioms:                         0
% 11.53/1.99  pred_elim_cands:                        0
% 11.53/1.99  pred_elim:                              0
% 11.53/1.99  pred_elim_cl:                           0
% 11.53/1.99  pred_elim_cycles:                       0
% 11.53/1.99  merged_defs:                            0
% 11.53/1.99  merged_defs_ncl:                        0
% 11.53/1.99  bin_hyper_res:                          0
% 11.53/1.99  prep_cycles:                            2
% 11.53/1.99  pred_elim_time:                         0.
% 11.53/1.99  splitting_time:                         0.
% 11.53/1.99  sem_filter_time:                        0.
% 11.53/1.99  monotx_time:                            0.
% 11.53/1.99  subtype_inf_time:                       0.
% 11.53/1.99  
% 11.53/1.99  ------ Problem properties
% 11.53/1.99  
% 11.53/1.99  clauses:                                11
% 11.53/1.99  conjectures:                            1
% 11.53/1.99  epr:                                    0
% 11.53/1.99  horn:                                   11
% 11.53/1.99  ground:                                 1
% 11.53/1.99  unary:                                  11
% 11.53/1.99  binary:                                 0
% 11.53/1.99  lits:                                   11
% 11.53/1.99  lits_eq:                                11
% 11.53/1.99  fd_pure:                                0
% 11.53/1.99  fd_pseudo:                              0
% 11.53/1.99  fd_cond:                                0
% 11.53/1.99  fd_pseudo_cond:                         0
% 11.53/1.99  ac_symbols:                             0
% 11.53/1.99  
% 11.53/1.99  ------ Propositional Solver
% 11.53/1.99  
% 11.53/1.99  prop_solver_calls:                      13
% 11.53/1.99  prop_fast_solver_calls:                 64
% 11.53/1.99  smt_solver_calls:                       0
% 11.53/1.99  smt_fast_solver_calls:                  0
% 11.53/1.99  prop_num_of_clauses:                    307
% 11.53/1.99  prop_preprocess_simplified:             407
% 11.53/1.99  prop_fo_subsumed:                       0
% 11.53/1.99  prop_solver_time:                       0.
% 11.53/1.99  smt_solver_time:                        0.
% 11.53/1.99  smt_fast_solver_time:                   0.
% 11.53/1.99  prop_fast_solver_time:                  0.
% 11.53/1.99  prop_unsat_core_time:                   0.
% 11.53/1.99  
% 11.53/1.99  ------ QBF
% 11.53/1.99  
% 11.53/1.99  qbf_q_res:                              0
% 11.53/1.99  qbf_num_tautologies:                    0
% 11.53/1.99  qbf_prep_cycles:                        0
% 11.53/1.99  
% 11.53/1.99  ------ BMC1
% 11.53/1.99  
% 11.53/1.99  bmc1_current_bound:                     -1
% 11.53/1.99  bmc1_last_solved_bound:                 -1
% 11.53/1.99  bmc1_unsat_core_size:                   -1
% 11.53/1.99  bmc1_unsat_core_parents_size:           -1
% 11.53/1.99  bmc1_merge_next_fun:                    0
% 11.53/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.53/1.99  
% 11.53/1.99  ------ Instantiation
% 11.53/1.99  
% 11.53/1.99  inst_num_of_clauses:                    0
% 11.53/1.99  inst_num_in_passive:                    0
% 11.53/1.99  inst_num_in_active:                     0
% 11.53/1.99  inst_num_in_unprocessed:                0
% 11.53/1.99  inst_num_of_loops:                      0
% 11.53/1.99  inst_num_of_learning_restarts:          0
% 11.53/1.99  inst_num_moves_active_passive:          0
% 11.53/1.99  inst_lit_activity:                      0
% 11.53/1.99  inst_lit_activity_moves:                0
% 11.53/1.99  inst_num_tautologies:                   0
% 11.53/1.99  inst_num_prop_implied:                  0
% 11.53/1.99  inst_num_existing_simplified:           0
% 11.53/1.99  inst_num_eq_res_simplified:             0
% 11.53/1.99  inst_num_child_elim:                    0
% 11.53/1.99  inst_num_of_dismatching_blockings:      0
% 11.53/1.99  inst_num_of_non_proper_insts:           0
% 11.53/1.99  inst_num_of_duplicates:                 0
% 11.53/1.99  inst_inst_num_from_inst_to_res:         0
% 11.53/1.99  inst_dismatching_checking_time:         0.
% 11.53/1.99  
% 11.53/1.99  ------ Resolution
% 11.53/1.99  
% 11.53/1.99  res_num_of_clauses:                     0
% 11.53/1.99  res_num_in_passive:                     0
% 11.53/1.99  res_num_in_active:                      0
% 11.53/1.99  res_num_of_loops:                       28
% 11.53/1.99  res_forward_subset_subsumed:            0
% 11.53/1.99  res_backward_subset_subsumed:           0
% 11.53/1.99  res_forward_subsumed:                   0
% 11.53/1.99  res_backward_subsumed:                  0
% 11.53/1.99  res_forward_subsumption_resolution:     0
% 11.53/1.99  res_backward_subsumption_resolution:    0
% 11.53/1.99  res_clause_to_clause_subsumption:       123482
% 11.53/1.99  res_orphan_elimination:                 0
% 11.53/1.99  res_tautology_del:                      0
% 11.53/1.99  res_num_eq_res_simplified:              0
% 11.53/1.99  res_num_sel_changes:                    0
% 11.53/1.99  res_moves_from_active_to_pass:          0
% 11.53/1.99  
% 11.53/1.99  ------ Superposition
% 11.53/1.99  
% 11.53/1.99  sup_time_total:                         0.
% 11.53/1.99  sup_time_generating:                    0.
% 11.53/1.99  sup_time_sim_full:                      0.
% 11.53/1.99  sup_time_sim_immed:                     0.
% 11.53/1.99  
% 11.53/1.99  sup_num_of_clauses:                     5114
% 11.53/1.99  sup_num_in_active:                      137
% 11.53/1.99  sup_num_in_passive:                     4977
% 11.53/1.99  sup_num_of_loops:                       174
% 11.53/1.99  sup_fw_superposition:                   12773
% 11.53/1.99  sup_bw_superposition:                   11979
% 11.53/1.99  sup_immediate_simplified:               13737
% 11.53/1.99  sup_given_eliminated:                   3
% 11.53/1.99  comparisons_done:                       0
% 11.53/1.99  comparisons_avoided:                    0
% 11.53/1.99  
% 11.53/1.99  ------ Simplifications
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  sim_fw_subset_subsumed:                 0
% 11.53/1.99  sim_bw_subset_subsumed:                 0
% 11.53/1.99  sim_fw_subsumed:                        2174
% 11.53/1.99  sim_bw_subsumed:                        30
% 11.53/1.99  sim_fw_subsumption_res:                 0
% 11.53/1.99  sim_bw_subsumption_res:                 0
% 11.53/1.99  sim_tautology_del:                      0
% 11.53/1.99  sim_eq_tautology_del:                   3870
% 11.53/1.99  sim_eq_res_simp:                        0
% 11.53/1.99  sim_fw_demodulated:                     9801
% 11.53/1.99  sim_bw_demodulated:                     175
% 11.53/1.99  sim_light_normalised:                   4594
% 11.53/1.99  sim_joinable_taut:                      0
% 11.53/1.99  sim_joinable_simp:                      0
% 11.53/1.99  sim_ac_normalised:                      0
% 11.53/1.99  sim_smt_subsumption:                    0
% 11.53/1.99  
%------------------------------------------------------------------------------
