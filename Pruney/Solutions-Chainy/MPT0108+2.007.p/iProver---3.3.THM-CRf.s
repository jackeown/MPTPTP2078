%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:29 EST 2020

% Result     : Theorem 15.24s
% Output     : CNFRefutation 15.24s
% Verified   : 
% Statistics : Number of formulae       :  111 (5867 expanded)
%              Number of clauses        :   80 (1972 expanded)
%              Number of leaves         :   12 (1780 expanded)
%              Depth                    :   30
%              Number of atoms          :  112 (5868 expanded)
%              Number of equality atoms :  111 (5867 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f29,f24,f24])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f24])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f26,f35,f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f30,f24,f24])).

fof(f14,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f14])).

fof(f18,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f15])).

fof(f19,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f34,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f34,f24,f35])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_467,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_475,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_467,c_6,c_9])).

cnf(c_744,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_10])).

cnf(c_741,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_475,c_0])).

cnf(c_746,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_741,c_6,c_9])).

cnf(c_767,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_744,c_746])).

cnf(c_743,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_475,c_10])).

cnf(c_768,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(demodulation,[status(thm)],[c_743,c_746])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_57,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_4,c_2])).

cnf(c_8,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_56,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_4,c_2])).

cnf(c_347,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_2,c_56])).

cnf(c_755,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_746,c_4])).

cnf(c_1045,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_57,c_347,c_755])).

cnf(c_1050,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))) ),
    inference(superposition,[status(thm)],[c_6,c_1045])).

cnf(c_1065,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))) ),
    inference(superposition,[status(thm)],[c_746,c_1045])).

cnf(c_748,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_746,c_475])).

cnf(c_1067,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1065,c_6,c_9,c_748,c_768])).

cnf(c_1068,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1067,c_746])).

cnf(c_1063,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))) ),
    inference(superposition,[status(thm)],[c_6,c_1045])).

cnf(c_1073,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_1063,c_6])).

cnf(c_181,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_1074,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(demodulation,[status(thm)],[c_1073,c_9,c_181])).

cnf(c_1080,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) ),
    inference(demodulation,[status(thm)],[c_1050,c_1068,c_1074])).

cnf(c_1081,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1080,c_6,c_9,c_181])).

cnf(c_1303,plain,
    ( k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_746,c_1081])).

cnf(c_1319,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1303,c_746])).

cnf(c_1638,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_768,c_1319])).

cnf(c_1649,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_767,c_1638])).

cnf(c_1659,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1649,c_9])).

cnf(c_1677,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1659,c_1638])).

cnf(c_1684,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1677])).

cnf(c_1171,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_755])).

cnf(c_1342,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1171,c_56])).

cnf(c_738,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_475])).

cnf(c_761,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_746,c_4])).

cnf(c_771,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_738,c_761])).

cnf(c_1347,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1342,c_771])).

cnf(c_2683,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1347,c_1045])).

cnf(c_2684,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2683,c_9,c_746])).

cnf(c_10079,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_1347,c_2684])).

cnf(c_1680,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1659,c_1659])).

cnf(c_1990,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1680,c_10])).

cnf(c_8590,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X2) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_1990])).

cnf(c_1184,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_755,c_56])).

cnf(c_1189,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1184,c_746])).

cnf(c_8743,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(light_normalisation,[status(thm)],[c_8590,c_1189])).

cnf(c_10200,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X1,k1_xboole_0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_10079,c_8743])).

cnf(c_10201,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_10200,c_9])).

cnf(c_23330,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_1684,c_10201])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_55,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_4,c_2])).

cnf(c_443,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10,c_55])).

cnf(c_46303,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_23330,c_443])).

cnf(c_115,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_2258,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_746,c_115])).

cnf(c_10114,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_2684,c_2258])).

cnf(c_10161,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_10114,c_2684])).

cnf(c_446,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(superposition,[status(thm)],[c_56,c_10])).

cnf(c_38172,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
    inference(superposition,[status(thm)],[c_10161,c_446])).

cnf(c_38208,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_10161,c_4])).

cnf(c_38388,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_38172,c_38208])).

cnf(c_340,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_2,c_56])).

cnf(c_10093,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_2684,c_340])).

cnf(c_116,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_10126,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_2684,c_116])).

cnf(c_10184,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_10093,c_10126])).

cnf(c_38389,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_38388,c_10184])).

cnf(c_46304,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_46303,c_38389])).

cnf(c_1298,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_1081])).

cnf(c_2227,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1298,c_1659])).

cnf(c_46305,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_46304,c_9,c_2227])).

cnf(c_46306,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_46305])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:54:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.24/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.24/2.49  
% 15.24/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.24/2.49  
% 15.24/2.49  ------  iProver source info
% 15.24/2.49  
% 15.24/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.24/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.24/2.49  git: non_committed_changes: false
% 15.24/2.49  git: last_make_outside_of_git: false
% 15.24/2.49  
% 15.24/2.49  ------ 
% 15.24/2.49  
% 15.24/2.49  ------ Input Options
% 15.24/2.49  
% 15.24/2.49  --out_options                           all
% 15.24/2.49  --tptp_safe_out                         true
% 15.24/2.49  --problem_path                          ""
% 15.24/2.49  --include_path                          ""
% 15.24/2.49  --clausifier                            res/vclausify_rel
% 15.24/2.49  --clausifier_options                    ""
% 15.24/2.49  --stdin                                 false
% 15.24/2.49  --stats_out                             all
% 15.24/2.49  
% 15.24/2.49  ------ General Options
% 15.24/2.49  
% 15.24/2.49  --fof                                   false
% 15.24/2.49  --time_out_real                         305.
% 15.24/2.49  --time_out_virtual                      -1.
% 15.24/2.49  --symbol_type_check                     false
% 15.24/2.49  --clausify_out                          false
% 15.24/2.49  --sig_cnt_out                           false
% 15.24/2.49  --trig_cnt_out                          false
% 15.24/2.49  --trig_cnt_out_tolerance                1.
% 15.24/2.49  --trig_cnt_out_sk_spl                   false
% 15.24/2.49  --abstr_cl_out                          false
% 15.24/2.49  
% 15.24/2.49  ------ Global Options
% 15.24/2.49  
% 15.24/2.49  --schedule                              default
% 15.24/2.49  --add_important_lit                     false
% 15.24/2.49  --prop_solver_per_cl                    1000
% 15.24/2.49  --min_unsat_core                        false
% 15.24/2.49  --soft_assumptions                      false
% 15.24/2.49  --soft_lemma_size                       3
% 15.24/2.49  --prop_impl_unit_size                   0
% 15.24/2.49  --prop_impl_unit                        []
% 15.24/2.49  --share_sel_clauses                     true
% 15.24/2.49  --reset_solvers                         false
% 15.24/2.49  --bc_imp_inh                            [conj_cone]
% 15.24/2.49  --conj_cone_tolerance                   3.
% 15.24/2.49  --extra_neg_conj                        none
% 15.24/2.49  --large_theory_mode                     true
% 15.24/2.49  --prolific_symb_bound                   200
% 15.24/2.49  --lt_threshold                          2000
% 15.24/2.49  --clause_weak_htbl                      true
% 15.24/2.49  --gc_record_bc_elim                     false
% 15.24/2.49  
% 15.24/2.49  ------ Preprocessing Options
% 15.24/2.49  
% 15.24/2.49  --preprocessing_flag                    true
% 15.24/2.49  --time_out_prep_mult                    0.1
% 15.24/2.49  --splitting_mode                        input
% 15.24/2.49  --splitting_grd                         true
% 15.24/2.49  --splitting_cvd                         false
% 15.24/2.49  --splitting_cvd_svl                     false
% 15.24/2.49  --splitting_nvd                         32
% 15.24/2.49  --sub_typing                            true
% 15.24/2.49  --prep_gs_sim                           true
% 15.24/2.49  --prep_unflatten                        true
% 15.24/2.49  --prep_res_sim                          true
% 15.24/2.49  --prep_upred                            true
% 15.24/2.49  --prep_sem_filter                       exhaustive
% 15.24/2.49  --prep_sem_filter_out                   false
% 15.24/2.49  --pred_elim                             true
% 15.24/2.49  --res_sim_input                         true
% 15.24/2.49  --eq_ax_congr_red                       true
% 15.24/2.49  --pure_diseq_elim                       true
% 15.24/2.49  --brand_transform                       false
% 15.24/2.49  --non_eq_to_eq                          false
% 15.24/2.49  --prep_def_merge                        true
% 15.24/2.49  --prep_def_merge_prop_impl              false
% 15.24/2.49  --prep_def_merge_mbd                    true
% 15.24/2.49  --prep_def_merge_tr_red                 false
% 15.24/2.49  --prep_def_merge_tr_cl                  false
% 15.24/2.49  --smt_preprocessing                     true
% 15.24/2.49  --smt_ac_axioms                         fast
% 15.24/2.49  --preprocessed_out                      false
% 15.24/2.49  --preprocessed_stats                    false
% 15.24/2.49  
% 15.24/2.49  ------ Abstraction refinement Options
% 15.24/2.49  
% 15.24/2.49  --abstr_ref                             []
% 15.24/2.49  --abstr_ref_prep                        false
% 15.24/2.49  --abstr_ref_until_sat                   false
% 15.24/2.49  --abstr_ref_sig_restrict                funpre
% 15.24/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.24/2.49  --abstr_ref_under                       []
% 15.24/2.49  
% 15.24/2.49  ------ SAT Options
% 15.24/2.49  
% 15.24/2.49  --sat_mode                              false
% 15.24/2.49  --sat_fm_restart_options                ""
% 15.24/2.49  --sat_gr_def                            false
% 15.24/2.49  --sat_epr_types                         true
% 15.24/2.49  --sat_non_cyclic_types                  false
% 15.24/2.49  --sat_finite_models                     false
% 15.24/2.49  --sat_fm_lemmas                         false
% 15.24/2.49  --sat_fm_prep                           false
% 15.24/2.49  --sat_fm_uc_incr                        true
% 15.24/2.49  --sat_out_model                         small
% 15.24/2.49  --sat_out_clauses                       false
% 15.24/2.49  
% 15.24/2.49  ------ QBF Options
% 15.24/2.49  
% 15.24/2.49  --qbf_mode                              false
% 15.24/2.49  --qbf_elim_univ                         false
% 15.24/2.49  --qbf_dom_inst                          none
% 15.24/2.49  --qbf_dom_pre_inst                      false
% 15.24/2.49  --qbf_sk_in                             false
% 15.24/2.49  --qbf_pred_elim                         true
% 15.24/2.49  --qbf_split                             512
% 15.24/2.49  
% 15.24/2.49  ------ BMC1 Options
% 15.24/2.49  
% 15.24/2.49  --bmc1_incremental                      false
% 15.24/2.49  --bmc1_axioms                           reachable_all
% 15.24/2.49  --bmc1_min_bound                        0
% 15.24/2.49  --bmc1_max_bound                        -1
% 15.24/2.49  --bmc1_max_bound_default                -1
% 15.24/2.49  --bmc1_symbol_reachability              true
% 15.24/2.49  --bmc1_property_lemmas                  false
% 15.24/2.49  --bmc1_k_induction                      false
% 15.24/2.49  --bmc1_non_equiv_states                 false
% 15.24/2.49  --bmc1_deadlock                         false
% 15.24/2.49  --bmc1_ucm                              false
% 15.24/2.49  --bmc1_add_unsat_core                   none
% 15.24/2.49  --bmc1_unsat_core_children              false
% 15.24/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.24/2.49  --bmc1_out_stat                         full
% 15.24/2.49  --bmc1_ground_init                      false
% 15.24/2.49  --bmc1_pre_inst_next_state              false
% 15.24/2.49  --bmc1_pre_inst_state                   false
% 15.24/2.49  --bmc1_pre_inst_reach_state             false
% 15.24/2.49  --bmc1_out_unsat_core                   false
% 15.24/2.49  --bmc1_aig_witness_out                  false
% 15.24/2.49  --bmc1_verbose                          false
% 15.24/2.49  --bmc1_dump_clauses_tptp                false
% 15.24/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.24/2.49  --bmc1_dump_file                        -
% 15.24/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.24/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.24/2.49  --bmc1_ucm_extend_mode                  1
% 15.24/2.49  --bmc1_ucm_init_mode                    2
% 15.24/2.49  --bmc1_ucm_cone_mode                    none
% 15.24/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.24/2.49  --bmc1_ucm_relax_model                  4
% 15.24/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.24/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.24/2.49  --bmc1_ucm_layered_model                none
% 15.24/2.49  --bmc1_ucm_max_lemma_size               10
% 15.24/2.49  
% 15.24/2.49  ------ AIG Options
% 15.24/2.49  
% 15.24/2.49  --aig_mode                              false
% 15.24/2.49  
% 15.24/2.49  ------ Instantiation Options
% 15.24/2.49  
% 15.24/2.49  --instantiation_flag                    true
% 15.24/2.49  --inst_sos_flag                         true
% 15.24/2.49  --inst_sos_phase                        true
% 15.24/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.24/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.24/2.49  --inst_lit_sel_side                     num_symb
% 15.24/2.49  --inst_solver_per_active                1400
% 15.24/2.49  --inst_solver_calls_frac                1.
% 15.24/2.49  --inst_passive_queue_type               priority_queues
% 15.24/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.24/2.49  --inst_passive_queues_freq              [25;2]
% 15.24/2.49  --inst_dismatching                      true
% 15.24/2.49  --inst_eager_unprocessed_to_passive     true
% 15.24/2.49  --inst_prop_sim_given                   true
% 15.24/2.49  --inst_prop_sim_new                     false
% 15.24/2.49  --inst_subs_new                         false
% 15.24/2.49  --inst_eq_res_simp                      false
% 15.24/2.49  --inst_subs_given                       false
% 15.24/2.49  --inst_orphan_elimination               true
% 15.24/2.49  --inst_learning_loop_flag               true
% 15.24/2.49  --inst_learning_start                   3000
% 15.24/2.49  --inst_learning_factor                  2
% 15.24/2.49  --inst_start_prop_sim_after_learn       3
% 15.24/2.49  --inst_sel_renew                        solver
% 15.24/2.49  --inst_lit_activity_flag                true
% 15.24/2.49  --inst_restr_to_given                   false
% 15.24/2.49  --inst_activity_threshold               500
% 15.24/2.49  --inst_out_proof                        true
% 15.24/2.49  
% 15.24/2.49  ------ Resolution Options
% 15.24/2.49  
% 15.24/2.49  --resolution_flag                       true
% 15.24/2.49  --res_lit_sel                           adaptive
% 15.24/2.49  --res_lit_sel_side                      none
% 15.24/2.49  --res_ordering                          kbo
% 15.24/2.49  --res_to_prop_solver                    active
% 15.24/2.49  --res_prop_simpl_new                    false
% 15.24/2.49  --res_prop_simpl_given                  true
% 15.24/2.49  --res_passive_queue_type                priority_queues
% 15.24/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.24/2.49  --res_passive_queues_freq               [15;5]
% 15.24/2.49  --res_forward_subs                      full
% 15.24/2.49  --res_backward_subs                     full
% 15.24/2.49  --res_forward_subs_resolution           true
% 15.24/2.49  --res_backward_subs_resolution          true
% 15.24/2.49  --res_orphan_elimination                true
% 15.24/2.49  --res_time_limit                        2.
% 15.24/2.49  --res_out_proof                         true
% 15.24/2.49  
% 15.24/2.49  ------ Superposition Options
% 15.24/2.49  
% 15.24/2.49  --superposition_flag                    true
% 15.24/2.49  --sup_passive_queue_type                priority_queues
% 15.24/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.24/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.24/2.49  --demod_completeness_check              fast
% 15.24/2.49  --demod_use_ground                      true
% 15.24/2.49  --sup_to_prop_solver                    passive
% 15.24/2.49  --sup_prop_simpl_new                    true
% 15.24/2.49  --sup_prop_simpl_given                  true
% 15.24/2.49  --sup_fun_splitting                     true
% 15.24/2.49  --sup_smt_interval                      50000
% 15.24/2.49  
% 15.24/2.49  ------ Superposition Simplification Setup
% 15.24/2.49  
% 15.24/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.24/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.24/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.24/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.24/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.24/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.24/2.49  --sup_immed_triv                        [TrivRules]
% 15.24/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.49  --sup_immed_bw_main                     []
% 15.24/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.24/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.24/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.49  --sup_input_bw                          []
% 15.24/2.49  
% 15.24/2.49  ------ Combination Options
% 15.24/2.49  
% 15.24/2.49  --comb_res_mult                         3
% 15.24/2.49  --comb_sup_mult                         2
% 15.24/2.49  --comb_inst_mult                        10
% 15.24/2.49  
% 15.24/2.49  ------ Debug Options
% 15.24/2.49  
% 15.24/2.49  --dbg_backtrace                         false
% 15.24/2.49  --dbg_dump_prop_clauses                 false
% 15.24/2.49  --dbg_dump_prop_clauses_file            -
% 15.24/2.49  --dbg_out_stat                          false
% 15.24/2.49  ------ Parsing...
% 15.24/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.24/2.49  
% 15.24/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.24/2.49  
% 15.24/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.24/2.49  
% 15.24/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.24/2.49  ------ Proving...
% 15.24/2.49  ------ Problem Properties 
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  clauses                                 12
% 15.24/2.49  conjectures                             1
% 15.24/2.49  EPR                                     0
% 15.24/2.49  Horn                                    12
% 15.24/2.49  unary                                   11
% 15.24/2.49  binary                                  1
% 15.24/2.49  lits                                    13
% 15.24/2.49  lits eq                                 11
% 15.24/2.49  fd_pure                                 0
% 15.24/2.49  fd_pseudo                               0
% 15.24/2.49  fd_cond                                 0
% 15.24/2.49  fd_pseudo_cond                          0
% 15.24/2.49  AC symbols                              1
% 15.24/2.49  
% 15.24/2.49  ------ Schedule dynamic 5 is on 
% 15.24/2.49  
% 15.24/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  ------ 
% 15.24/2.49  Current options:
% 15.24/2.49  ------ 
% 15.24/2.49  
% 15.24/2.49  ------ Input Options
% 15.24/2.49  
% 15.24/2.49  --out_options                           all
% 15.24/2.49  --tptp_safe_out                         true
% 15.24/2.49  --problem_path                          ""
% 15.24/2.49  --include_path                          ""
% 15.24/2.49  --clausifier                            res/vclausify_rel
% 15.24/2.49  --clausifier_options                    ""
% 15.24/2.49  --stdin                                 false
% 15.24/2.49  --stats_out                             all
% 15.24/2.49  
% 15.24/2.49  ------ General Options
% 15.24/2.49  
% 15.24/2.49  --fof                                   false
% 15.24/2.49  --time_out_real                         305.
% 15.24/2.49  --time_out_virtual                      -1.
% 15.24/2.49  --symbol_type_check                     false
% 15.24/2.49  --clausify_out                          false
% 15.24/2.49  --sig_cnt_out                           false
% 15.24/2.49  --trig_cnt_out                          false
% 15.24/2.49  --trig_cnt_out_tolerance                1.
% 15.24/2.49  --trig_cnt_out_sk_spl                   false
% 15.24/2.49  --abstr_cl_out                          false
% 15.24/2.49  
% 15.24/2.49  ------ Global Options
% 15.24/2.49  
% 15.24/2.49  --schedule                              default
% 15.24/2.49  --add_important_lit                     false
% 15.24/2.49  --prop_solver_per_cl                    1000
% 15.24/2.49  --min_unsat_core                        false
% 15.24/2.49  --soft_assumptions                      false
% 15.24/2.49  --soft_lemma_size                       3
% 15.24/2.49  --prop_impl_unit_size                   0
% 15.24/2.49  --prop_impl_unit                        []
% 15.24/2.49  --share_sel_clauses                     true
% 15.24/2.49  --reset_solvers                         false
% 15.24/2.49  --bc_imp_inh                            [conj_cone]
% 15.24/2.49  --conj_cone_tolerance                   3.
% 15.24/2.49  --extra_neg_conj                        none
% 15.24/2.49  --large_theory_mode                     true
% 15.24/2.49  --prolific_symb_bound                   200
% 15.24/2.49  --lt_threshold                          2000
% 15.24/2.49  --clause_weak_htbl                      true
% 15.24/2.49  --gc_record_bc_elim                     false
% 15.24/2.49  
% 15.24/2.49  ------ Preprocessing Options
% 15.24/2.49  
% 15.24/2.49  --preprocessing_flag                    true
% 15.24/2.49  --time_out_prep_mult                    0.1
% 15.24/2.49  --splitting_mode                        input
% 15.24/2.49  --splitting_grd                         true
% 15.24/2.49  --splitting_cvd                         false
% 15.24/2.49  --splitting_cvd_svl                     false
% 15.24/2.49  --splitting_nvd                         32
% 15.24/2.49  --sub_typing                            true
% 15.24/2.49  --prep_gs_sim                           true
% 15.24/2.49  --prep_unflatten                        true
% 15.24/2.49  --prep_res_sim                          true
% 15.24/2.49  --prep_upred                            true
% 15.24/2.49  --prep_sem_filter                       exhaustive
% 15.24/2.49  --prep_sem_filter_out                   false
% 15.24/2.49  --pred_elim                             true
% 15.24/2.49  --res_sim_input                         true
% 15.24/2.49  --eq_ax_congr_red                       true
% 15.24/2.49  --pure_diseq_elim                       true
% 15.24/2.49  --brand_transform                       false
% 15.24/2.49  --non_eq_to_eq                          false
% 15.24/2.49  --prep_def_merge                        true
% 15.24/2.49  --prep_def_merge_prop_impl              false
% 15.24/2.49  --prep_def_merge_mbd                    true
% 15.24/2.49  --prep_def_merge_tr_red                 false
% 15.24/2.49  --prep_def_merge_tr_cl                  false
% 15.24/2.49  --smt_preprocessing                     true
% 15.24/2.49  --smt_ac_axioms                         fast
% 15.24/2.49  --preprocessed_out                      false
% 15.24/2.49  --preprocessed_stats                    false
% 15.24/2.49  
% 15.24/2.49  ------ Abstraction refinement Options
% 15.24/2.49  
% 15.24/2.49  --abstr_ref                             []
% 15.24/2.49  --abstr_ref_prep                        false
% 15.24/2.49  --abstr_ref_until_sat                   false
% 15.24/2.49  --abstr_ref_sig_restrict                funpre
% 15.24/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.24/2.49  --abstr_ref_under                       []
% 15.24/2.49  
% 15.24/2.49  ------ SAT Options
% 15.24/2.49  
% 15.24/2.49  --sat_mode                              false
% 15.24/2.49  --sat_fm_restart_options                ""
% 15.24/2.49  --sat_gr_def                            false
% 15.24/2.49  --sat_epr_types                         true
% 15.24/2.49  --sat_non_cyclic_types                  false
% 15.24/2.49  --sat_finite_models                     false
% 15.24/2.49  --sat_fm_lemmas                         false
% 15.24/2.49  --sat_fm_prep                           false
% 15.24/2.49  --sat_fm_uc_incr                        true
% 15.24/2.49  --sat_out_model                         small
% 15.24/2.49  --sat_out_clauses                       false
% 15.24/2.49  
% 15.24/2.49  ------ QBF Options
% 15.24/2.49  
% 15.24/2.49  --qbf_mode                              false
% 15.24/2.49  --qbf_elim_univ                         false
% 15.24/2.49  --qbf_dom_inst                          none
% 15.24/2.49  --qbf_dom_pre_inst                      false
% 15.24/2.49  --qbf_sk_in                             false
% 15.24/2.49  --qbf_pred_elim                         true
% 15.24/2.49  --qbf_split                             512
% 15.24/2.49  
% 15.24/2.49  ------ BMC1 Options
% 15.24/2.49  
% 15.24/2.49  --bmc1_incremental                      false
% 15.24/2.49  --bmc1_axioms                           reachable_all
% 15.24/2.49  --bmc1_min_bound                        0
% 15.24/2.49  --bmc1_max_bound                        -1
% 15.24/2.49  --bmc1_max_bound_default                -1
% 15.24/2.49  --bmc1_symbol_reachability              true
% 15.24/2.49  --bmc1_property_lemmas                  false
% 15.24/2.49  --bmc1_k_induction                      false
% 15.24/2.49  --bmc1_non_equiv_states                 false
% 15.24/2.49  --bmc1_deadlock                         false
% 15.24/2.49  --bmc1_ucm                              false
% 15.24/2.49  --bmc1_add_unsat_core                   none
% 15.24/2.49  --bmc1_unsat_core_children              false
% 15.24/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.24/2.49  --bmc1_out_stat                         full
% 15.24/2.49  --bmc1_ground_init                      false
% 15.24/2.49  --bmc1_pre_inst_next_state              false
% 15.24/2.49  --bmc1_pre_inst_state                   false
% 15.24/2.49  --bmc1_pre_inst_reach_state             false
% 15.24/2.49  --bmc1_out_unsat_core                   false
% 15.24/2.49  --bmc1_aig_witness_out                  false
% 15.24/2.49  --bmc1_verbose                          false
% 15.24/2.49  --bmc1_dump_clauses_tptp                false
% 15.24/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.24/2.49  --bmc1_dump_file                        -
% 15.24/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.24/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.24/2.49  --bmc1_ucm_extend_mode                  1
% 15.24/2.49  --bmc1_ucm_init_mode                    2
% 15.24/2.49  --bmc1_ucm_cone_mode                    none
% 15.24/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.24/2.49  --bmc1_ucm_relax_model                  4
% 15.24/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.24/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.24/2.49  --bmc1_ucm_layered_model                none
% 15.24/2.49  --bmc1_ucm_max_lemma_size               10
% 15.24/2.49  
% 15.24/2.49  ------ AIG Options
% 15.24/2.49  
% 15.24/2.49  --aig_mode                              false
% 15.24/2.49  
% 15.24/2.49  ------ Instantiation Options
% 15.24/2.49  
% 15.24/2.49  --instantiation_flag                    true
% 15.24/2.49  --inst_sos_flag                         true
% 15.24/2.49  --inst_sos_phase                        true
% 15.24/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.24/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.24/2.49  --inst_lit_sel_side                     none
% 15.24/2.49  --inst_solver_per_active                1400
% 15.24/2.49  --inst_solver_calls_frac                1.
% 15.24/2.49  --inst_passive_queue_type               priority_queues
% 15.24/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.24/2.49  --inst_passive_queues_freq              [25;2]
% 15.24/2.49  --inst_dismatching                      true
% 15.24/2.49  --inst_eager_unprocessed_to_passive     true
% 15.24/2.49  --inst_prop_sim_given                   true
% 15.24/2.49  --inst_prop_sim_new                     false
% 15.24/2.49  --inst_subs_new                         false
% 15.24/2.49  --inst_eq_res_simp                      false
% 15.24/2.49  --inst_subs_given                       false
% 15.24/2.49  --inst_orphan_elimination               true
% 15.24/2.49  --inst_learning_loop_flag               true
% 15.24/2.49  --inst_learning_start                   3000
% 15.24/2.49  --inst_learning_factor                  2
% 15.24/2.49  --inst_start_prop_sim_after_learn       3
% 15.24/2.49  --inst_sel_renew                        solver
% 15.24/2.49  --inst_lit_activity_flag                true
% 15.24/2.49  --inst_restr_to_given                   false
% 15.24/2.49  --inst_activity_threshold               500
% 15.24/2.49  --inst_out_proof                        true
% 15.24/2.49  
% 15.24/2.49  ------ Resolution Options
% 15.24/2.49  
% 15.24/2.49  --resolution_flag                       false
% 15.24/2.49  --res_lit_sel                           adaptive
% 15.24/2.49  --res_lit_sel_side                      none
% 15.24/2.49  --res_ordering                          kbo
% 15.24/2.49  --res_to_prop_solver                    active
% 15.24/2.49  --res_prop_simpl_new                    false
% 15.24/2.49  --res_prop_simpl_given                  true
% 15.24/2.49  --res_passive_queue_type                priority_queues
% 15.24/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.24/2.49  --res_passive_queues_freq               [15;5]
% 15.24/2.49  --res_forward_subs                      full
% 15.24/2.49  --res_backward_subs                     full
% 15.24/2.49  --res_forward_subs_resolution           true
% 15.24/2.49  --res_backward_subs_resolution          true
% 15.24/2.49  --res_orphan_elimination                true
% 15.24/2.49  --res_time_limit                        2.
% 15.24/2.49  --res_out_proof                         true
% 15.24/2.49  
% 15.24/2.49  ------ Superposition Options
% 15.24/2.49  
% 15.24/2.49  --superposition_flag                    true
% 15.24/2.49  --sup_passive_queue_type                priority_queues
% 15.24/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.24/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.24/2.49  --demod_completeness_check              fast
% 15.24/2.49  --demod_use_ground                      true
% 15.24/2.49  --sup_to_prop_solver                    passive
% 15.24/2.49  --sup_prop_simpl_new                    true
% 15.24/2.49  --sup_prop_simpl_given                  true
% 15.24/2.49  --sup_fun_splitting                     true
% 15.24/2.49  --sup_smt_interval                      50000
% 15.24/2.49  
% 15.24/2.49  ------ Superposition Simplification Setup
% 15.24/2.49  
% 15.24/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.24/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.24/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.24/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.24/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.24/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.24/2.49  --sup_immed_triv                        [TrivRules]
% 15.24/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.49  --sup_immed_bw_main                     []
% 15.24/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.24/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.24/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.49  --sup_input_bw                          []
% 15.24/2.49  
% 15.24/2.49  ------ Combination Options
% 15.24/2.49  
% 15.24/2.49  --comb_res_mult                         3
% 15.24/2.49  --comb_sup_mult                         2
% 15.24/2.49  --comb_inst_mult                        10
% 15.24/2.49  
% 15.24/2.49  ------ Debug Options
% 15.24/2.49  
% 15.24/2.49  --dbg_backtrace                         false
% 15.24/2.49  --dbg_dump_prop_clauses                 false
% 15.24/2.49  --dbg_dump_prop_clauses_file            -
% 15.24/2.49  --dbg_out_stat                          false
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  ------ Proving...
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  % SZS status Theorem for theBenchmark.p
% 15.24/2.49  
% 15.24/2.49   Resolution empty clause
% 15.24/2.49  
% 15.24/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.24/2.49  
% 15.24/2.49  fof(f12,axiom,(
% 15.24/2.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f32,plain,(
% 15.24/2.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 15.24/2.49    inference(cnf_transformation,[],[f12])).
% 15.24/2.49  
% 15.24/2.49  fof(f7,axiom,(
% 15.24/2.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f27,plain,(
% 15.24/2.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.24/2.49    inference(cnf_transformation,[],[f7])).
% 15.24/2.49  
% 15.24/2.49  fof(f9,axiom,(
% 15.24/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f29,plain,(
% 15.24/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.24/2.49    inference(cnf_transformation,[],[f9])).
% 15.24/2.49  
% 15.24/2.49  fof(f4,axiom,(
% 15.24/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f24,plain,(
% 15.24/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.24/2.49    inference(cnf_transformation,[],[f4])).
% 15.24/2.49  
% 15.24/2.49  fof(f36,plain,(
% 15.24/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 15.24/2.49    inference(definition_unfolding,[],[f29,f24,f24])).
% 15.24/2.49  
% 15.24/2.49  fof(f11,axiom,(
% 15.24/2.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f31,plain,(
% 15.24/2.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.24/2.49    inference(cnf_transformation,[],[f11])).
% 15.24/2.49  
% 15.24/2.49  fof(f6,axiom,(
% 15.24/2.49    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f26,plain,(
% 15.24/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 15.24/2.49    inference(cnf_transformation,[],[f6])).
% 15.24/2.49  
% 15.24/2.49  fof(f13,axiom,(
% 15.24/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f33,plain,(
% 15.24/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.24/2.49    inference(cnf_transformation,[],[f13])).
% 15.24/2.49  
% 15.24/2.49  fof(f35,plain,(
% 15.24/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 15.24/2.49    inference(definition_unfolding,[],[f33,f24])).
% 15.24/2.49  
% 15.24/2.49  fof(f39,plain,(
% 15.24/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1))))) )),
% 15.24/2.49    inference(definition_unfolding,[],[f26,f35,f35])).
% 15.24/2.49  
% 15.24/2.49  fof(f5,axiom,(
% 15.24/2.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f25,plain,(
% 15.24/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.24/2.49    inference(cnf_transformation,[],[f5])).
% 15.24/2.49  
% 15.24/2.49  fof(f2,axiom,(
% 15.24/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f22,plain,(
% 15.24/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.24/2.49    inference(cnf_transformation,[],[f2])).
% 15.24/2.49  
% 15.24/2.49  fof(f10,axiom,(
% 15.24/2.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f30,plain,(
% 15.24/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.24/2.49    inference(cnf_transformation,[],[f10])).
% 15.24/2.49  
% 15.24/2.49  fof(f41,plain,(
% 15.24/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 15.24/2.49    inference(definition_unfolding,[],[f30,f24,f24])).
% 15.24/2.49  
% 15.24/2.49  fof(f14,conjecture,(
% 15.24/2.49    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 15.24/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.49  
% 15.24/2.49  fof(f15,negated_conjecture,(
% 15.24/2.49    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 15.24/2.49    inference(negated_conjecture,[],[f14])).
% 15.24/2.49  
% 15.24/2.49  fof(f18,plain,(
% 15.24/2.49    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 15.24/2.49    inference(ennf_transformation,[],[f15])).
% 15.24/2.49  
% 15.24/2.49  fof(f19,plain,(
% 15.24/2.49    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 15.24/2.49    introduced(choice_axiom,[])).
% 15.24/2.49  
% 15.24/2.49  fof(f20,plain,(
% 15.24/2.49    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 15.24/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 15.24/2.49  
% 15.24/2.49  fof(f34,plain,(
% 15.24/2.49    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 15.24/2.49    inference(cnf_transformation,[],[f20])).
% 15.24/2.49  
% 15.24/2.49  fof(f42,plain,(
% 15.24/2.49    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 15.24/2.49    inference(definition_unfolding,[],[f34,f24,f35])).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10,plain,
% 15.24/2.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.24/2.49      inference(cnf_transformation,[],[f32]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_6,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.24/2.49      inference(cnf_transformation,[],[f27]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_0,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 15.24/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_467,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_9,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.24/2.49      inference(cnf_transformation,[],[f31]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_475,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_467,c_6,c_9]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_744,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_475,c_10]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_741,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_475,c_0]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_746,plain,
% 15.24/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_741,c_6,c_9]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_767,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_744,c_746]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_743,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_475,c_10]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_768,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_743,c_746]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_5,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 15.24/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_4,plain,
% 15.24/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.24/2.49      inference(cnf_transformation,[],[f25]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_2,plain,
% 15.24/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.24/2.49      inference(cnf_transformation,[],[f22]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_57,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
% 15.24/2.49      inference(theory_normalisation,[status(thm)],[c_5,c_4,c_2]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_8,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.24/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_56,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.24/2.49      inference(theory_normalisation,[status(thm)],[c_8,c_4,c_2]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_347,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_2,c_56]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_755,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_746,c_4]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1045,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_57,c_347,c_755]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1050,plain,
% 15.24/2.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_6,c_1045]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1065,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_746,c_1045]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_748,plain,
% 15.24/2.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_746,c_475]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1067,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))) = k3_xboole_0(X0,X1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_1065,c_6,c_9,c_748,c_768]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1068,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X0,X1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_1067,c_746]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1063,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_6,c_1045]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1073,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_1063,c_6]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_181,plain,
% 15.24/2.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1074,plain,
% 15.24/2.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_1073,c_9,c_181]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1080,plain,
% 15.24/2.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_1050,c_1068,c_1074]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1081,plain,
% 15.24/2.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_1080,c_6,c_9,c_181]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1303,plain,
% 15.24/2.49      ( k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_746,c_1081]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1319,plain,
% 15.24/2.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_1303,c_746]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1638,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_768,c_1319]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1649,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_767,c_1638]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1659,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_1649,c_9]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1677,plain,
% 15.24/2.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1659,c_1638]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1684,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_10,c_1677]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1171,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_2,c_755]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1342,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1171,c_56]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_738,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_4,c_475]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_761,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_746,c_4]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_771,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_738,c_761]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1347,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_1342,c_771]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_2683,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1347,c_1045]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_2684,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_2683,c_9,c_746]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10079,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0))) = X0 ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1347,c_2684]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1680,plain,
% 15.24/2.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1659,c_1659]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1990,plain,
% 15.24/2.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1680,c_10]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_8590,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X2) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X2)) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_0,c_1990]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1184,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_755,c_56]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1189,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_1184,c_746]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_8743,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_8590,c_1189]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10200,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X1,k1_xboole_0)))) = X0 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_10079,c_8743]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10201,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X1))) = X0 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_10200,c_9]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_23330,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1684,c_10201]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_11,negated_conjecture,
% 15.24/2.49      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 15.24/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_55,negated_conjecture,
% 15.24/2.49      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
% 15.24/2.49      inference(theory_normalisation,[status(thm)],[c_11,c_4,c_2]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_443,plain,
% 15.24/2.49      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_10,c_55]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_46303,plain,
% 15.24/2.49      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_23330,c_443]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_115,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_2258,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_746,c_115]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10114,plain,
% 15.24/2.49      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_2684,c_2258]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10161,plain,
% 15.24/2.49      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_10114,c_2684]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_446,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_56,c_10]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_38172,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_10161,c_446]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_38208,plain,
% 15.24/2.49      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_10161,c_4]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_38388,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X2),X3)) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_38172,c_38208]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_340,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_2,c_56]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10093,plain,
% 15.24/2.49      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_2684,c_340]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_116,plain,
% 15.24/2.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10126,plain,
% 15.24/2.49      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_2684,c_116]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_10184,plain,
% 15.24/2.49      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_10093,c_10126]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_38389,plain,
% 15.24/2.49      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 15.24/2.49      inference(light_normalisation,[status(thm)],[c_38388,c_10184]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_46304,plain,
% 15.24/2.49      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_46303,c_38389]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_1298,plain,
% 15.24/2.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_2,c_1081]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_2227,plain,
% 15.24/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.24/2.49      inference(superposition,[status(thm)],[c_1298,c_1659]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_46305,plain,
% 15.24/2.49      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 15.24/2.49      inference(demodulation,[status(thm)],[c_46304,c_9,c_2227]) ).
% 15.24/2.49  
% 15.24/2.49  cnf(c_46306,plain,
% 15.24/2.49      ( $false ),
% 15.24/2.49      inference(equality_resolution_simp,[status(thm)],[c_46305]) ).
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.24/2.49  
% 15.24/2.49  ------                               Statistics
% 15.24/2.49  
% 15.24/2.49  ------ General
% 15.24/2.49  
% 15.24/2.49  abstr_ref_over_cycles:                  0
% 15.24/2.49  abstr_ref_under_cycles:                 0
% 15.24/2.49  gc_basic_clause_elim:                   0
% 15.24/2.49  forced_gc_time:                         0
% 15.24/2.49  parsing_time:                           0.008
% 15.24/2.49  unif_index_cands_time:                  0.
% 15.24/2.49  unif_index_add_time:                    0.
% 15.24/2.49  orderings_time:                         0.
% 15.24/2.49  out_proof_time:                         0.01
% 15.24/2.49  total_time:                             1.779
% 15.24/2.49  num_of_symbols:                         37
% 15.24/2.49  num_of_terms:                           56554
% 15.24/2.49  
% 15.24/2.49  ------ Preprocessing
% 15.24/2.49  
% 15.24/2.49  num_of_splits:                          0
% 15.24/2.49  num_of_split_atoms:                     0
% 15.24/2.49  num_of_reused_defs:                     0
% 15.24/2.49  num_eq_ax_congr_red:                    2
% 15.24/2.49  num_of_sem_filtered_clauses:            1
% 15.24/2.49  num_of_subtypes:                        0
% 15.24/2.49  monotx_restored_types:                  0
% 15.24/2.49  sat_num_of_epr_types:                   0
% 15.24/2.49  sat_num_of_non_cyclic_types:            0
% 15.24/2.49  sat_guarded_non_collapsed_types:        0
% 15.24/2.49  num_pure_diseq_elim:                    0
% 15.24/2.49  simp_replaced_by:                       0
% 15.24/2.49  res_preprocessed:                       47
% 15.24/2.49  prep_upred:                             0
% 15.24/2.49  prep_unflattend:                        2
% 15.24/2.49  smt_new_axioms:                         0
% 15.24/2.49  pred_elim_cands:                        1
% 15.24/2.49  pred_elim:                              0
% 15.24/2.49  pred_elim_cl:                           0
% 15.24/2.49  pred_elim_cycles:                       1
% 15.24/2.49  merged_defs:                            0
% 15.24/2.49  merged_defs_ncl:                        0
% 15.24/2.49  bin_hyper_res:                          0
% 15.24/2.49  prep_cycles:                            3
% 15.24/2.49  pred_elim_time:                         0.
% 15.24/2.49  splitting_time:                         0.
% 15.24/2.49  sem_filter_time:                        0.
% 15.24/2.49  monotx_time:                            0.
% 15.24/2.49  subtype_inf_time:                       0.
% 15.24/2.49  
% 15.24/2.49  ------ Problem properties
% 15.24/2.49  
% 15.24/2.49  clauses:                                12
% 15.24/2.49  conjectures:                            1
% 15.24/2.49  epr:                                    0
% 15.24/2.49  horn:                                   12
% 15.24/2.49  ground:                                 1
% 15.24/2.49  unary:                                  11
% 15.24/2.49  binary:                                 1
% 15.24/2.49  lits:                                   13
% 15.24/2.49  lits_eq:                                11
% 15.24/2.49  fd_pure:                                0
% 15.24/2.49  fd_pseudo:                              0
% 15.24/2.49  fd_cond:                                0
% 15.24/2.49  fd_pseudo_cond:                         0
% 15.24/2.49  ac_symbols:                             2
% 15.24/2.49  
% 15.24/2.49  ------ Propositional Solver
% 15.24/2.49  
% 15.24/2.49  prop_solver_calls:                      28
% 15.24/2.49  prop_fast_solver_calls:                 347
% 15.24/2.49  smt_solver_calls:                       0
% 15.24/2.49  smt_fast_solver_calls:                  0
% 15.24/2.49  prop_num_of_clauses:                    6891
% 15.24/2.49  prop_preprocess_simplified:             10443
% 15.24/2.49  prop_fo_subsumed:                       0
% 15.24/2.49  prop_solver_time:                       0.
% 15.24/2.49  smt_solver_time:                        0.
% 15.24/2.49  smt_fast_solver_time:                   0.
% 15.24/2.49  prop_fast_solver_time:                  0.
% 15.24/2.49  prop_unsat_core_time:                   0.
% 15.24/2.49  
% 15.24/2.49  ------ QBF
% 15.24/2.49  
% 15.24/2.49  qbf_q_res:                              0
% 15.24/2.49  qbf_num_tautologies:                    0
% 15.24/2.49  qbf_prep_cycles:                        0
% 15.24/2.49  
% 15.24/2.49  ------ BMC1
% 15.24/2.49  
% 15.24/2.49  bmc1_current_bound:                     -1
% 15.24/2.49  bmc1_last_solved_bound:                 -1
% 15.24/2.49  bmc1_unsat_core_size:                   -1
% 15.24/2.49  bmc1_unsat_core_parents_size:           -1
% 15.24/2.49  bmc1_merge_next_fun:                    0
% 15.24/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.24/2.49  
% 15.24/2.49  ------ Instantiation
% 15.24/2.49  
% 15.24/2.49  inst_num_of_clauses:                    2213
% 15.24/2.49  inst_num_in_passive:                    765
% 15.24/2.49  inst_num_in_active:                     760
% 15.24/2.49  inst_num_in_unprocessed:                688
% 15.24/2.49  inst_num_of_loops:                      800
% 15.24/2.49  inst_num_of_learning_restarts:          0
% 15.24/2.49  inst_num_moves_active_passive:          34
% 15.24/2.49  inst_lit_activity:                      0
% 15.24/2.49  inst_lit_activity_moves:                0
% 15.24/2.49  inst_num_tautologies:                   0
% 15.24/2.49  inst_num_prop_implied:                  0
% 15.24/2.49  inst_num_existing_simplified:           0
% 15.24/2.49  inst_num_eq_res_simplified:             0
% 15.24/2.49  inst_num_child_elim:                    0
% 15.24/2.49  inst_num_of_dismatching_blockings:      4380
% 15.24/2.49  inst_num_of_non_proper_insts:           4549
% 15.24/2.49  inst_num_of_duplicates:                 0
% 15.24/2.49  inst_inst_num_from_inst_to_res:         0
% 15.24/2.49  inst_dismatching_checking_time:         0.
% 15.24/2.49  
% 15.24/2.49  ------ Resolution
% 15.24/2.49  
% 15.24/2.49  res_num_of_clauses:                     0
% 15.24/2.49  res_num_in_passive:                     0
% 15.24/2.49  res_num_in_active:                      0
% 15.24/2.49  res_num_of_loops:                       50
% 15.24/2.49  res_forward_subset_subsumed:            535
% 15.24/2.49  res_backward_subset_subsumed:           4
% 15.24/2.49  res_forward_subsumed:                   0
% 15.24/2.49  res_backward_subsumed:                  0
% 15.24/2.49  res_forward_subsumption_resolution:     0
% 15.24/2.49  res_backward_subsumption_resolution:    0
% 15.24/2.49  res_clause_to_clause_subsumption:       45863
% 15.24/2.49  res_orphan_elimination:                 0
% 15.24/2.49  res_tautology_del:                      520
% 15.24/2.49  res_num_eq_res_simplified:              0
% 15.24/2.49  res_num_sel_changes:                    0
% 15.24/2.49  res_moves_from_active_to_pass:          0
% 15.24/2.49  
% 15.24/2.49  ------ Superposition
% 15.24/2.49  
% 15.24/2.49  sup_time_total:                         0.
% 15.24/2.49  sup_time_generating:                    0.
% 15.24/2.49  sup_time_sim_full:                      0.
% 15.24/2.49  sup_time_sim_immed:                     0.
% 15.24/2.49  
% 15.24/2.49  sup_num_of_clauses:                     2219
% 15.24/2.49  sup_num_in_active:                      144
% 15.24/2.49  sup_num_in_passive:                     2075
% 15.24/2.49  sup_num_of_loops:                       159
% 15.24/2.49  sup_fw_superposition:                   10965
% 15.24/2.49  sup_bw_superposition:                   8120
% 15.24/2.49  sup_immediate_simplified:               8253
% 15.24/2.49  sup_given_eliminated:                   4
% 15.24/2.49  comparisons_done:                       0
% 15.24/2.49  comparisons_avoided:                    0
% 15.24/2.49  
% 15.24/2.49  ------ Simplifications
% 15.24/2.49  
% 15.24/2.49  
% 15.24/2.49  sim_fw_subset_subsumed:                 0
% 15.24/2.49  sim_bw_subset_subsumed:                 0
% 15.24/2.49  sim_fw_subsumed:                        911
% 15.24/2.49  sim_bw_subsumed:                        13
% 15.24/2.49  sim_fw_subsumption_res:                 0
% 15.24/2.49  sim_bw_subsumption_res:                 0
% 15.24/2.49  sim_tautology_del:                      0
% 15.24/2.49  sim_eq_tautology_del:                   2204
% 15.24/2.49  sim_eq_res_simp:                        0
% 15.24/2.49  sim_fw_demodulated:                     6185
% 15.24/2.49  sim_bw_demodulated:                     102
% 15.24/2.49  sim_light_normalised:                   3549
% 15.24/2.49  sim_joinable_taut:                      206
% 15.24/2.49  sim_joinable_simp:                      0
% 15.24/2.49  sim_ac_normalised:                      0
% 15.24/2.49  sim_smt_subsumption:                    0
% 15.24/2.49  
%------------------------------------------------------------------------------
