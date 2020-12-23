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
% DateTime   : Thu Dec  3 11:25:03 EST 2020

% Result     : Theorem 39.62s
% Output     : CNFRefutation 39.62s
% Verified   : 
% Statistics : Number of formulae       :  156 (5435 expanded)
%              Number of clauses        :  117 (2066 expanded)
%              Number of leaves         :   15 (1491 expanded)
%              Depth                    :   27
%              Number of atoms          :  157 (5436 expanded)
%              Number of equality atoms :  156 (5435 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f29,f29])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f22])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f17,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f33,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f33,f29,f22,f22])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_60,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_40,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_55,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_40])).

cnf(c_75,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_60,c_55])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_175,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_75,c_6])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_28,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_9,c_8,c_0])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_36,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10,c_5])).

cnf(c_59,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28,c_36])).

cnf(c_182,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_175,c_59])).

cnf(c_71,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_28])).

cnf(c_1882,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_182,c_71])).

cnf(c_1940,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1882,c_5])).

cnf(c_5729,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1940])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_132,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_8])).

cnf(c_324,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_132])).

cnf(c_202,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_182])).

cnf(c_879,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_324,c_202])).

cnf(c_179,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_75,c_6])).

cnf(c_329,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_28,c_132])).

cnf(c_344,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_329,c_28])).

cnf(c_427,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_344])).

cnf(c_931,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_179,c_427])).

cnf(c_976,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_931,c_5])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_116,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_37,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_281,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_116,c_37])).

cnf(c_977,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_976,c_281])).

cnf(c_1548,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_977])).

cnf(c_54865,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_879,c_1548])).

cnf(c_55415,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_54865,c_3])).

cnf(c_38,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_754,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_116,c_38])).

cnf(c_55682,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(k4_xboole_0(X0,X2),X0) ),
    inference(superposition,[status(thm)],[c_55415,c_754])).

cnf(c_55790,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_55682,c_344])).

cnf(c_58252,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_5729,c_55790])).

cnf(c_197,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_116,c_8])).

cnf(c_2469,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_197,c_324])).

cnf(c_277,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_37])).

cnf(c_2471,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_197,c_277])).

cnf(c_2475,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_197,c_38])).

cnf(c_2505,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_2471,c_197,c_2475])).

cnf(c_2506,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_2469,c_2505])).

cnf(c_207,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28,c_182])).

cnf(c_241,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_207])).

cnf(c_528,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_241,c_6])).

cnf(c_1014,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_528,c_427])).

cnf(c_1034,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(light_normalisation,[status(thm)],[c_1014,c_5])).

cnf(c_756,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_344,c_38])).

cnf(c_1035,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1034,c_756])).

cnf(c_750,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3,c_38])).

cnf(c_72,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_306,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_182,c_72])).

cnf(c_316,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_306,c_5])).

cnf(c_804,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_316])).

cnf(c_1374,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_750,c_804])).

cnf(c_611,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_277])).

cnf(c_307,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_202,c_72])).

cnf(c_315,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_307,c_5])).

cnf(c_1148,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_611,c_315])).

cnf(c_1183,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1148,c_611])).

cnf(c_1428,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1374,c_1183])).

cnf(c_2167,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1035,c_1428])).

cnf(c_2225,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2167,c_1428])).

cnf(c_5761,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2225,c_1940])).

cnf(c_2174,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_977,c_1428])).

cnf(c_2219,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2174,c_1428])).

cnf(c_5888,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5761,c_2219,c_2225])).

cnf(c_18202,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X2),X0),X0) ),
    inference(superposition,[status(thm)],[c_2506,c_5888])).

cnf(c_694,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_315])).

cnf(c_3170,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_694,c_281])).

cnf(c_3276,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_3170,c_281])).

cnf(c_18407,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_18202,c_3276])).

cnf(c_55550,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_18407,c_55415])).

cnf(c_877,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_324,c_277])).

cnf(c_880,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_324,c_38])).

cnf(c_901,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_877,c_324,c_880])).

cnf(c_6919,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_901,c_324])).

cnf(c_6981,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_6919,c_901])).

cnf(c_19647,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1940,c_6981])).

cnf(c_19807,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_19647,c_6981])).

cnf(c_440,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_344,c_8])).

cnf(c_3059,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_427,c_440])).

cnf(c_3119,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
    inference(light_normalisation,[status(thm)],[c_3059,c_427])).

cnf(c_3120,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_3119,c_6])).

cnf(c_6165,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
    inference(superposition,[status(thm)],[c_277,c_3120])).

cnf(c_55728,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_55415,c_6165])).

cnf(c_57786,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_19807,c_55728])).

cnf(c_80,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_57971,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_55728,c_80])).

cnf(c_58036,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_57971,c_5,c_182])).

cnf(c_58113,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_57786,c_58036])).

cnf(c_55488,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1035,c_55415])).

cnf(c_58114,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_58113,c_55488])).

cnf(c_58619,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(light_normalisation,[status(thm)],[c_58252,c_55550,c_58114])).

cnf(c_55487,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2219,c_55415])).

cnf(c_58620,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_58619,c_55487])).

cnf(c_59459,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X2) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_58620,c_80])).

cnf(c_59620,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_59459,c_5,c_202])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_27,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_8,c_0])).

cnf(c_186426,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_59620,c_27])).

cnf(c_206,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_182])).

cnf(c_2608,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_344,c_206])).

cnf(c_13792,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2219,c_2608])).

cnf(c_186427,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_186426,c_3,c_13792])).

cnf(c_187652,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_186427])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n005.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:03:02 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 39.62/5.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.62/5.47  
% 39.62/5.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.62/5.47  
% 39.62/5.47  ------  iProver source info
% 39.62/5.47  
% 39.62/5.47  git: date: 2020-06-30 10:37:57 +0100
% 39.62/5.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.62/5.47  git: non_committed_changes: false
% 39.62/5.47  git: last_make_outside_of_git: false
% 39.62/5.47  
% 39.62/5.47  ------ 
% 39.62/5.47  
% 39.62/5.47  ------ Input Options
% 39.62/5.47  
% 39.62/5.47  --out_options                           all
% 39.62/5.47  --tptp_safe_out                         true
% 39.62/5.47  --problem_path                          ""
% 39.62/5.47  --include_path                          ""
% 39.62/5.47  --clausifier                            res/vclausify_rel
% 39.62/5.47  --clausifier_options                    --mode clausify
% 39.62/5.47  --stdin                                 false
% 39.62/5.47  --stats_out                             all
% 39.62/5.47  
% 39.62/5.47  ------ General Options
% 39.62/5.47  
% 39.62/5.47  --fof                                   false
% 39.62/5.47  --time_out_real                         305.
% 39.62/5.47  --time_out_virtual                      -1.
% 39.62/5.47  --symbol_type_check                     false
% 39.62/5.47  --clausify_out                          false
% 39.62/5.47  --sig_cnt_out                           false
% 39.62/5.47  --trig_cnt_out                          false
% 39.62/5.47  --trig_cnt_out_tolerance                1.
% 39.62/5.47  --trig_cnt_out_sk_spl                   false
% 39.62/5.47  --abstr_cl_out                          false
% 39.62/5.47  
% 39.62/5.47  ------ Global Options
% 39.62/5.47  
% 39.62/5.47  --schedule                              default
% 39.62/5.47  --add_important_lit                     false
% 39.62/5.47  --prop_solver_per_cl                    1000
% 39.62/5.47  --min_unsat_core                        false
% 39.62/5.47  --soft_assumptions                      false
% 39.62/5.47  --soft_lemma_size                       3
% 39.62/5.47  --prop_impl_unit_size                   0
% 39.62/5.47  --prop_impl_unit                        []
% 39.62/5.47  --share_sel_clauses                     true
% 39.62/5.47  --reset_solvers                         false
% 39.62/5.47  --bc_imp_inh                            [conj_cone]
% 39.62/5.47  --conj_cone_tolerance                   3.
% 39.62/5.47  --extra_neg_conj                        none
% 39.62/5.47  --large_theory_mode                     true
% 39.62/5.47  --prolific_symb_bound                   200
% 39.62/5.47  --lt_threshold                          2000
% 39.62/5.47  --clause_weak_htbl                      true
% 39.62/5.47  --gc_record_bc_elim                     false
% 39.62/5.47  
% 39.62/5.47  ------ Preprocessing Options
% 39.62/5.47  
% 39.62/5.47  --preprocessing_flag                    true
% 39.62/5.47  --time_out_prep_mult                    0.1
% 39.62/5.47  --splitting_mode                        input
% 39.62/5.47  --splitting_grd                         true
% 39.62/5.47  --splitting_cvd                         false
% 39.62/5.47  --splitting_cvd_svl                     false
% 39.62/5.47  --splitting_nvd                         32
% 39.62/5.47  --sub_typing                            true
% 39.62/5.47  --prep_gs_sim                           true
% 39.62/5.47  --prep_unflatten                        true
% 39.62/5.47  --prep_res_sim                          true
% 39.62/5.47  --prep_upred                            true
% 39.62/5.47  --prep_sem_filter                       exhaustive
% 39.62/5.47  --prep_sem_filter_out                   false
% 39.62/5.47  --pred_elim                             true
% 39.62/5.47  --res_sim_input                         true
% 39.62/5.47  --eq_ax_congr_red                       true
% 39.62/5.47  --pure_diseq_elim                       true
% 39.62/5.47  --brand_transform                       false
% 39.62/5.47  --non_eq_to_eq                          false
% 39.62/5.47  --prep_def_merge                        true
% 39.62/5.47  --prep_def_merge_prop_impl              false
% 39.62/5.47  --prep_def_merge_mbd                    true
% 39.62/5.47  --prep_def_merge_tr_red                 false
% 39.62/5.47  --prep_def_merge_tr_cl                  false
% 39.62/5.47  --smt_preprocessing                     true
% 39.62/5.47  --smt_ac_axioms                         fast
% 39.62/5.47  --preprocessed_out                      false
% 39.62/5.47  --preprocessed_stats                    false
% 39.62/5.47  
% 39.62/5.47  ------ Abstraction refinement Options
% 39.62/5.47  
% 39.62/5.47  --abstr_ref                             []
% 39.62/5.47  --abstr_ref_prep                        false
% 39.62/5.47  --abstr_ref_until_sat                   false
% 39.62/5.47  --abstr_ref_sig_restrict                funpre
% 39.62/5.47  --abstr_ref_af_restrict_to_split_sk     false
% 39.62/5.47  --abstr_ref_under                       []
% 39.62/5.47  
% 39.62/5.47  ------ SAT Options
% 39.62/5.47  
% 39.62/5.47  --sat_mode                              false
% 39.62/5.47  --sat_fm_restart_options                ""
% 39.62/5.47  --sat_gr_def                            false
% 39.62/5.47  --sat_epr_types                         true
% 39.62/5.47  --sat_non_cyclic_types                  false
% 39.62/5.47  --sat_finite_models                     false
% 39.62/5.47  --sat_fm_lemmas                         false
% 39.62/5.47  --sat_fm_prep                           false
% 39.62/5.47  --sat_fm_uc_incr                        true
% 39.62/5.47  --sat_out_model                         small
% 39.62/5.47  --sat_out_clauses                       false
% 39.62/5.47  
% 39.62/5.47  ------ QBF Options
% 39.62/5.47  
% 39.62/5.47  --qbf_mode                              false
% 39.62/5.47  --qbf_elim_univ                         false
% 39.62/5.47  --qbf_dom_inst                          none
% 39.62/5.47  --qbf_dom_pre_inst                      false
% 39.62/5.47  --qbf_sk_in                             false
% 39.62/5.47  --qbf_pred_elim                         true
% 39.62/5.47  --qbf_split                             512
% 39.62/5.47  
% 39.62/5.47  ------ BMC1 Options
% 39.62/5.47  
% 39.62/5.47  --bmc1_incremental                      false
% 39.62/5.47  --bmc1_axioms                           reachable_all
% 39.62/5.47  --bmc1_min_bound                        0
% 39.62/5.47  --bmc1_max_bound                        -1
% 39.62/5.47  --bmc1_max_bound_default                -1
% 39.62/5.47  --bmc1_symbol_reachability              true
% 39.62/5.47  --bmc1_property_lemmas                  false
% 39.62/5.47  --bmc1_k_induction                      false
% 39.62/5.47  --bmc1_non_equiv_states                 false
% 39.62/5.47  --bmc1_deadlock                         false
% 39.62/5.47  --bmc1_ucm                              false
% 39.62/5.47  --bmc1_add_unsat_core                   none
% 39.62/5.47  --bmc1_unsat_core_children              false
% 39.62/5.47  --bmc1_unsat_core_extrapolate_axioms    false
% 39.62/5.47  --bmc1_out_stat                         full
% 39.62/5.47  --bmc1_ground_init                      false
% 39.62/5.47  --bmc1_pre_inst_next_state              false
% 39.62/5.47  --bmc1_pre_inst_state                   false
% 39.62/5.47  --bmc1_pre_inst_reach_state             false
% 39.62/5.47  --bmc1_out_unsat_core                   false
% 39.62/5.47  --bmc1_aig_witness_out                  false
% 39.62/5.47  --bmc1_verbose                          false
% 39.62/5.47  --bmc1_dump_clauses_tptp                false
% 39.62/5.47  --bmc1_dump_unsat_core_tptp             false
% 39.62/5.47  --bmc1_dump_file                        -
% 39.62/5.47  --bmc1_ucm_expand_uc_limit              128
% 39.62/5.47  --bmc1_ucm_n_expand_iterations          6
% 39.62/5.47  --bmc1_ucm_extend_mode                  1
% 39.62/5.47  --bmc1_ucm_init_mode                    2
% 39.62/5.47  --bmc1_ucm_cone_mode                    none
% 39.62/5.47  --bmc1_ucm_reduced_relation_type        0
% 39.62/5.47  --bmc1_ucm_relax_model                  4
% 39.62/5.47  --bmc1_ucm_full_tr_after_sat            true
% 39.62/5.47  --bmc1_ucm_expand_neg_assumptions       false
% 39.62/5.47  --bmc1_ucm_layered_model                none
% 39.62/5.47  --bmc1_ucm_max_lemma_size               10
% 39.62/5.47  
% 39.62/5.47  ------ AIG Options
% 39.62/5.47  
% 39.62/5.47  --aig_mode                              false
% 39.62/5.47  
% 39.62/5.47  ------ Instantiation Options
% 39.62/5.47  
% 39.62/5.47  --instantiation_flag                    true
% 39.62/5.47  --inst_sos_flag                         false
% 39.62/5.47  --inst_sos_phase                        true
% 39.62/5.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.62/5.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.62/5.47  --inst_lit_sel_side                     num_symb
% 39.62/5.47  --inst_solver_per_active                1400
% 39.62/5.47  --inst_solver_calls_frac                1.
% 39.62/5.47  --inst_passive_queue_type               priority_queues
% 39.62/5.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.62/5.47  --inst_passive_queues_freq              [25;2]
% 39.62/5.47  --inst_dismatching                      true
% 39.62/5.47  --inst_eager_unprocessed_to_passive     true
% 39.62/5.47  --inst_prop_sim_given                   true
% 39.62/5.47  --inst_prop_sim_new                     false
% 39.62/5.47  --inst_subs_new                         false
% 39.62/5.47  --inst_eq_res_simp                      false
% 39.62/5.47  --inst_subs_given                       false
% 39.62/5.47  --inst_orphan_elimination               true
% 39.62/5.47  --inst_learning_loop_flag               true
% 39.62/5.47  --inst_learning_start                   3000
% 39.62/5.47  --inst_learning_factor                  2
% 39.62/5.47  --inst_start_prop_sim_after_learn       3
% 39.62/5.47  --inst_sel_renew                        solver
% 39.62/5.47  --inst_lit_activity_flag                true
% 39.62/5.47  --inst_restr_to_given                   false
% 39.62/5.47  --inst_activity_threshold               500
% 39.62/5.47  --inst_out_proof                        true
% 39.62/5.47  
% 39.62/5.47  ------ Resolution Options
% 39.62/5.47  
% 39.62/5.47  --resolution_flag                       true
% 39.62/5.47  --res_lit_sel                           adaptive
% 39.62/5.47  --res_lit_sel_side                      none
% 39.62/5.47  --res_ordering                          kbo
% 39.62/5.47  --res_to_prop_solver                    active
% 39.62/5.47  --res_prop_simpl_new                    false
% 39.62/5.47  --res_prop_simpl_given                  true
% 39.62/5.47  --res_passive_queue_type                priority_queues
% 39.62/5.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.62/5.47  --res_passive_queues_freq               [15;5]
% 39.62/5.47  --res_forward_subs                      full
% 39.62/5.47  --res_backward_subs                     full
% 39.62/5.47  --res_forward_subs_resolution           true
% 39.62/5.47  --res_backward_subs_resolution          true
% 39.62/5.47  --res_orphan_elimination                true
% 39.62/5.47  --res_time_limit                        2.
% 39.62/5.47  --res_out_proof                         true
% 39.62/5.47  
% 39.62/5.47  ------ Superposition Options
% 39.62/5.47  
% 39.62/5.47  --superposition_flag                    true
% 39.62/5.47  --sup_passive_queue_type                priority_queues
% 39.62/5.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.62/5.47  --sup_passive_queues_freq               [8;1;4]
% 39.62/5.47  --demod_completeness_check              fast
% 39.62/5.47  --demod_use_ground                      true
% 39.62/5.47  --sup_to_prop_solver                    passive
% 39.62/5.47  --sup_prop_simpl_new                    true
% 39.62/5.47  --sup_prop_simpl_given                  true
% 39.62/5.47  --sup_fun_splitting                     false
% 39.62/5.47  --sup_smt_interval                      50000
% 39.62/5.47  
% 39.62/5.47  ------ Superposition Simplification Setup
% 39.62/5.47  
% 39.62/5.47  --sup_indices_passive                   []
% 39.62/5.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.62/5.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.62/5.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.62/5.47  --sup_full_triv                         [TrivRules;PropSubs]
% 39.62/5.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.62/5.47  --sup_full_bw                           [BwDemod]
% 39.62/5.47  --sup_immed_triv                        [TrivRules]
% 39.62/5.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.62/5.47  --sup_immed_bw_main                     []
% 39.62/5.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.62/5.47  --sup_input_triv                        [Unflattening;TrivRules]
% 39.62/5.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.62/5.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.62/5.47  
% 39.62/5.47  ------ Combination Options
% 39.62/5.47  
% 39.62/5.47  --comb_res_mult                         3
% 39.62/5.47  --comb_sup_mult                         2
% 39.62/5.47  --comb_inst_mult                        10
% 39.62/5.47  
% 39.62/5.47  ------ Debug Options
% 39.62/5.47  
% 39.62/5.47  --dbg_backtrace                         false
% 39.62/5.47  --dbg_dump_prop_clauses                 false
% 39.62/5.47  --dbg_dump_prop_clauses_file            -
% 39.62/5.47  --dbg_out_stat                          false
% 39.62/5.47  ------ Parsing...
% 39.62/5.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.62/5.47  
% 39.62/5.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 39.62/5.47  
% 39.62/5.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.62/5.47  
% 39.62/5.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.62/5.47  ------ Proving...
% 39.62/5.47  ------ Problem Properties 
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  clauses                                 12
% 39.62/5.47  conjectures                             1
% 39.62/5.47  EPR                                     0
% 39.62/5.47  Horn                                    12
% 39.62/5.47  unary                                   12
% 39.62/5.47  binary                                  0
% 39.62/5.47  lits                                    12
% 39.62/5.47  lits eq                                 12
% 39.62/5.47  fd_pure                                 0
% 39.62/5.47  fd_pseudo                               0
% 39.62/5.47  fd_cond                                 0
% 39.62/5.47  fd_pseudo_cond                          0
% 39.62/5.47  AC symbols                              1
% 39.62/5.47  
% 39.62/5.47  ------ Schedule UEQ
% 39.62/5.47  
% 39.62/5.47  ------ pure equality problem: resolution off 
% 39.62/5.47  
% 39.62/5.47  ------ Option_UEQ Time Limit: Unbounded
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  ------ 
% 39.62/5.47  Current options:
% 39.62/5.47  ------ 
% 39.62/5.47  
% 39.62/5.47  ------ Input Options
% 39.62/5.47  
% 39.62/5.47  --out_options                           all
% 39.62/5.47  --tptp_safe_out                         true
% 39.62/5.47  --problem_path                          ""
% 39.62/5.47  --include_path                          ""
% 39.62/5.47  --clausifier                            res/vclausify_rel
% 39.62/5.47  --clausifier_options                    --mode clausify
% 39.62/5.47  --stdin                                 false
% 39.62/5.47  --stats_out                             all
% 39.62/5.47  
% 39.62/5.47  ------ General Options
% 39.62/5.47  
% 39.62/5.47  --fof                                   false
% 39.62/5.47  --time_out_real                         305.
% 39.62/5.47  --time_out_virtual                      -1.
% 39.62/5.47  --symbol_type_check                     false
% 39.62/5.47  --clausify_out                          false
% 39.62/5.47  --sig_cnt_out                           false
% 39.62/5.47  --trig_cnt_out                          false
% 39.62/5.47  --trig_cnt_out_tolerance                1.
% 39.62/5.47  --trig_cnt_out_sk_spl                   false
% 39.62/5.47  --abstr_cl_out                          false
% 39.62/5.47  
% 39.62/5.47  ------ Global Options
% 39.62/5.47  
% 39.62/5.47  --schedule                              default
% 39.62/5.47  --add_important_lit                     false
% 39.62/5.47  --prop_solver_per_cl                    1000
% 39.62/5.47  --min_unsat_core                        false
% 39.62/5.47  --soft_assumptions                      false
% 39.62/5.47  --soft_lemma_size                       3
% 39.62/5.47  --prop_impl_unit_size                   0
% 39.62/5.47  --prop_impl_unit                        []
% 39.62/5.47  --share_sel_clauses                     true
% 39.62/5.47  --reset_solvers                         false
% 39.62/5.47  --bc_imp_inh                            [conj_cone]
% 39.62/5.47  --conj_cone_tolerance                   3.
% 39.62/5.47  --extra_neg_conj                        none
% 39.62/5.47  --large_theory_mode                     true
% 39.62/5.47  --prolific_symb_bound                   200
% 39.62/5.47  --lt_threshold                          2000
% 39.62/5.47  --clause_weak_htbl                      true
% 39.62/5.47  --gc_record_bc_elim                     false
% 39.62/5.47  
% 39.62/5.47  ------ Preprocessing Options
% 39.62/5.47  
% 39.62/5.47  --preprocessing_flag                    true
% 39.62/5.47  --time_out_prep_mult                    0.1
% 39.62/5.47  --splitting_mode                        input
% 39.62/5.47  --splitting_grd                         true
% 39.62/5.47  --splitting_cvd                         false
% 39.62/5.47  --splitting_cvd_svl                     false
% 39.62/5.47  --splitting_nvd                         32
% 39.62/5.47  --sub_typing                            true
% 39.62/5.47  --prep_gs_sim                           true
% 39.62/5.47  --prep_unflatten                        true
% 39.62/5.47  --prep_res_sim                          true
% 39.62/5.47  --prep_upred                            true
% 39.62/5.47  --prep_sem_filter                       exhaustive
% 39.62/5.47  --prep_sem_filter_out                   false
% 39.62/5.47  --pred_elim                             true
% 39.62/5.47  --res_sim_input                         true
% 39.62/5.47  --eq_ax_congr_red                       true
% 39.62/5.47  --pure_diseq_elim                       true
% 39.62/5.47  --brand_transform                       false
% 39.62/5.47  --non_eq_to_eq                          false
% 39.62/5.47  --prep_def_merge                        true
% 39.62/5.47  --prep_def_merge_prop_impl              false
% 39.62/5.47  --prep_def_merge_mbd                    true
% 39.62/5.47  --prep_def_merge_tr_red                 false
% 39.62/5.47  --prep_def_merge_tr_cl                  false
% 39.62/5.47  --smt_preprocessing                     true
% 39.62/5.47  --smt_ac_axioms                         fast
% 39.62/5.47  --preprocessed_out                      false
% 39.62/5.47  --preprocessed_stats                    false
% 39.62/5.47  
% 39.62/5.47  ------ Abstraction refinement Options
% 39.62/5.47  
% 39.62/5.47  --abstr_ref                             []
% 39.62/5.47  --abstr_ref_prep                        false
% 39.62/5.47  --abstr_ref_until_sat                   false
% 39.62/5.47  --abstr_ref_sig_restrict                funpre
% 39.62/5.47  --abstr_ref_af_restrict_to_split_sk     false
% 39.62/5.47  --abstr_ref_under                       []
% 39.62/5.47  
% 39.62/5.47  ------ SAT Options
% 39.62/5.47  
% 39.62/5.47  --sat_mode                              false
% 39.62/5.47  --sat_fm_restart_options                ""
% 39.62/5.47  --sat_gr_def                            false
% 39.62/5.47  --sat_epr_types                         true
% 39.62/5.47  --sat_non_cyclic_types                  false
% 39.62/5.47  --sat_finite_models                     false
% 39.62/5.47  --sat_fm_lemmas                         false
% 39.62/5.47  --sat_fm_prep                           false
% 39.62/5.47  --sat_fm_uc_incr                        true
% 39.62/5.47  --sat_out_model                         small
% 39.62/5.47  --sat_out_clauses                       false
% 39.62/5.47  
% 39.62/5.47  ------ QBF Options
% 39.62/5.47  
% 39.62/5.47  --qbf_mode                              false
% 39.62/5.47  --qbf_elim_univ                         false
% 39.62/5.47  --qbf_dom_inst                          none
% 39.62/5.47  --qbf_dom_pre_inst                      false
% 39.62/5.47  --qbf_sk_in                             false
% 39.62/5.47  --qbf_pred_elim                         true
% 39.62/5.47  --qbf_split                             512
% 39.62/5.47  
% 39.62/5.47  ------ BMC1 Options
% 39.62/5.47  
% 39.62/5.47  --bmc1_incremental                      false
% 39.62/5.47  --bmc1_axioms                           reachable_all
% 39.62/5.47  --bmc1_min_bound                        0
% 39.62/5.47  --bmc1_max_bound                        -1
% 39.62/5.47  --bmc1_max_bound_default                -1
% 39.62/5.47  --bmc1_symbol_reachability              true
% 39.62/5.47  --bmc1_property_lemmas                  false
% 39.62/5.47  --bmc1_k_induction                      false
% 39.62/5.47  --bmc1_non_equiv_states                 false
% 39.62/5.47  --bmc1_deadlock                         false
% 39.62/5.47  --bmc1_ucm                              false
% 39.62/5.47  --bmc1_add_unsat_core                   none
% 39.62/5.47  --bmc1_unsat_core_children              false
% 39.62/5.47  --bmc1_unsat_core_extrapolate_axioms    false
% 39.62/5.47  --bmc1_out_stat                         full
% 39.62/5.47  --bmc1_ground_init                      false
% 39.62/5.47  --bmc1_pre_inst_next_state              false
% 39.62/5.47  --bmc1_pre_inst_state                   false
% 39.62/5.47  --bmc1_pre_inst_reach_state             false
% 39.62/5.47  --bmc1_out_unsat_core                   false
% 39.62/5.47  --bmc1_aig_witness_out                  false
% 39.62/5.47  --bmc1_verbose                          false
% 39.62/5.47  --bmc1_dump_clauses_tptp                false
% 39.62/5.47  --bmc1_dump_unsat_core_tptp             false
% 39.62/5.47  --bmc1_dump_file                        -
% 39.62/5.47  --bmc1_ucm_expand_uc_limit              128
% 39.62/5.47  --bmc1_ucm_n_expand_iterations          6
% 39.62/5.47  --bmc1_ucm_extend_mode                  1
% 39.62/5.47  --bmc1_ucm_init_mode                    2
% 39.62/5.47  --bmc1_ucm_cone_mode                    none
% 39.62/5.47  --bmc1_ucm_reduced_relation_type        0
% 39.62/5.47  --bmc1_ucm_relax_model                  4
% 39.62/5.47  --bmc1_ucm_full_tr_after_sat            true
% 39.62/5.47  --bmc1_ucm_expand_neg_assumptions       false
% 39.62/5.47  --bmc1_ucm_layered_model                none
% 39.62/5.47  --bmc1_ucm_max_lemma_size               10
% 39.62/5.47  
% 39.62/5.47  ------ AIG Options
% 39.62/5.47  
% 39.62/5.47  --aig_mode                              false
% 39.62/5.47  
% 39.62/5.47  ------ Instantiation Options
% 39.62/5.47  
% 39.62/5.47  --instantiation_flag                    false
% 39.62/5.47  --inst_sos_flag                         false
% 39.62/5.47  --inst_sos_phase                        true
% 39.62/5.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.62/5.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.62/5.47  --inst_lit_sel_side                     num_symb
% 39.62/5.47  --inst_solver_per_active                1400
% 39.62/5.47  --inst_solver_calls_frac                1.
% 39.62/5.47  --inst_passive_queue_type               priority_queues
% 39.62/5.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.62/5.47  --inst_passive_queues_freq              [25;2]
% 39.62/5.47  --inst_dismatching                      true
% 39.62/5.47  --inst_eager_unprocessed_to_passive     true
% 39.62/5.47  --inst_prop_sim_given                   true
% 39.62/5.47  --inst_prop_sim_new                     false
% 39.62/5.47  --inst_subs_new                         false
% 39.62/5.47  --inst_eq_res_simp                      false
% 39.62/5.47  --inst_subs_given                       false
% 39.62/5.47  --inst_orphan_elimination               true
% 39.62/5.47  --inst_learning_loop_flag               true
% 39.62/5.47  --inst_learning_start                   3000
% 39.62/5.47  --inst_learning_factor                  2
% 39.62/5.47  --inst_start_prop_sim_after_learn       3
% 39.62/5.47  --inst_sel_renew                        solver
% 39.62/5.47  --inst_lit_activity_flag                true
% 39.62/5.47  --inst_restr_to_given                   false
% 39.62/5.47  --inst_activity_threshold               500
% 39.62/5.47  --inst_out_proof                        true
% 39.62/5.47  
% 39.62/5.47  ------ Resolution Options
% 39.62/5.47  
% 39.62/5.47  --resolution_flag                       false
% 39.62/5.47  --res_lit_sel                           adaptive
% 39.62/5.47  --res_lit_sel_side                      none
% 39.62/5.47  --res_ordering                          kbo
% 39.62/5.47  --res_to_prop_solver                    active
% 39.62/5.47  --res_prop_simpl_new                    false
% 39.62/5.47  --res_prop_simpl_given                  true
% 39.62/5.47  --res_passive_queue_type                priority_queues
% 39.62/5.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.62/5.47  --res_passive_queues_freq               [15;5]
% 39.62/5.47  --res_forward_subs                      full
% 39.62/5.47  --res_backward_subs                     full
% 39.62/5.47  --res_forward_subs_resolution           true
% 39.62/5.47  --res_backward_subs_resolution          true
% 39.62/5.47  --res_orphan_elimination                true
% 39.62/5.47  --res_time_limit                        2.
% 39.62/5.47  --res_out_proof                         true
% 39.62/5.47  
% 39.62/5.47  ------ Superposition Options
% 39.62/5.47  
% 39.62/5.47  --superposition_flag                    true
% 39.62/5.47  --sup_passive_queue_type                priority_queues
% 39.62/5.47  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.62/5.47  --sup_passive_queues_freq               [8;1;4]
% 39.62/5.47  --demod_completeness_check              fast
% 39.62/5.47  --demod_use_ground                      true
% 39.62/5.47  --sup_to_prop_solver                    active
% 39.62/5.47  --sup_prop_simpl_new                    false
% 39.62/5.47  --sup_prop_simpl_given                  false
% 39.62/5.47  --sup_fun_splitting                     true
% 39.62/5.47  --sup_smt_interval                      10000
% 39.62/5.47  
% 39.62/5.47  ------ Superposition Simplification Setup
% 39.62/5.47  
% 39.62/5.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.62/5.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.62/5.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.62/5.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.62/5.47  --sup_full_triv                         [TrivRules]
% 39.62/5.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.62/5.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.62/5.47  --sup_immed_triv                        [TrivRules]
% 39.62/5.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.47  --sup_immed_bw_main                     []
% 39.62/5.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.62/5.47  --sup_input_triv                        [Unflattening;TrivRules]
% 39.62/5.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.62/5.47  --sup_input_bw                          [BwDemod;BwSubsumption]
% 39.62/5.47  
% 39.62/5.47  ------ Combination Options
% 39.62/5.47  
% 39.62/5.47  --comb_res_mult                         1
% 39.62/5.47  --comb_sup_mult                         1
% 39.62/5.47  --comb_inst_mult                        1000000
% 39.62/5.47  
% 39.62/5.47  ------ Debug Options
% 39.62/5.47  
% 39.62/5.47  --dbg_backtrace                         false
% 39.62/5.47  --dbg_dump_prop_clauses                 false
% 39.62/5.47  --dbg_dump_prop_clauses_file            -
% 39.62/5.47  --dbg_out_stat                          false
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  ------ Proving...
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  % SZS status Theorem for theBenchmark.p
% 39.62/5.47  
% 39.62/5.47   Resolution empty clause
% 39.62/5.47  
% 39.62/5.47  % SZS output start CNFRefutation for theBenchmark.p
% 39.62/5.47  
% 39.62/5.47  fof(f2,axiom,(
% 39.62/5.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f21,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.62/5.47    inference(cnf_transformation,[],[f2])).
% 39.62/5.47  
% 39.62/5.47  fof(f10,axiom,(
% 39.62/5.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f29,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.62/5.47    inference(cnf_transformation,[],[f10])).
% 39.62/5.47  
% 39.62/5.47  fof(f34,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 39.62/5.47    inference(definition_unfolding,[],[f21,f29,f29])).
% 39.62/5.47  
% 39.62/5.47  fof(f1,axiom,(
% 39.62/5.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f20,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 39.62/5.47    inference(cnf_transformation,[],[f1])).
% 39.62/5.47  
% 39.62/5.47  fof(f7,axiom,(
% 39.62/5.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f26,plain,(
% 39.62/5.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.62/5.47    inference(cnf_transformation,[],[f7])).
% 39.62/5.47  
% 39.62/5.47  fof(f6,axiom,(
% 39.62/5.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f25,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 39.62/5.47    inference(cnf_transformation,[],[f6])).
% 39.62/5.47  
% 39.62/5.47  fof(f35,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 39.62/5.47    inference(definition_unfolding,[],[f25,f29])).
% 39.62/5.47  
% 39.62/5.47  fof(f5,axiom,(
% 39.62/5.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f24,plain,(
% 39.62/5.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.62/5.47    inference(cnf_transformation,[],[f5])).
% 39.62/5.47  
% 39.62/5.47  fof(f8,axiom,(
% 39.62/5.47    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f27,plain,(
% 39.62/5.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 39.62/5.47    inference(cnf_transformation,[],[f8])).
% 39.62/5.47  
% 39.62/5.47  fof(f12,axiom,(
% 39.62/5.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f31,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 39.62/5.47    inference(cnf_transformation,[],[f12])).
% 39.62/5.47  
% 39.62/5.47  fof(f37,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 39.62/5.47    inference(definition_unfolding,[],[f31,f29])).
% 39.62/5.47  
% 39.62/5.47  fof(f11,axiom,(
% 39.62/5.47    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f30,plain,(
% 39.62/5.47    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 39.62/5.47    inference(cnf_transformation,[],[f11])).
% 39.62/5.47  
% 39.62/5.47  fof(f13,axiom,(
% 39.62/5.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f32,plain,(
% 39.62/5.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.62/5.47    inference(cnf_transformation,[],[f13])).
% 39.62/5.47  
% 39.62/5.47  fof(f3,axiom,(
% 39.62/5.47    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f22,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 39.62/5.47    inference(cnf_transformation,[],[f3])).
% 39.62/5.47  
% 39.62/5.47  fof(f38,plain,(
% 39.62/5.47    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 39.62/5.47    inference(definition_unfolding,[],[f32,f22])).
% 39.62/5.47  
% 39.62/5.47  fof(f4,axiom,(
% 39.62/5.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f16,plain,(
% 39.62/5.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 39.62/5.47    inference(rectify,[],[f4])).
% 39.62/5.47  
% 39.62/5.47  fof(f23,plain,(
% 39.62/5.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 39.62/5.47    inference(cnf_transformation,[],[f16])).
% 39.62/5.47  
% 39.62/5.47  fof(f9,axiom,(
% 39.62/5.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f28,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.62/5.47    inference(cnf_transformation,[],[f9])).
% 39.62/5.47  
% 39.62/5.47  fof(f36,plain,(
% 39.62/5.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 39.62/5.47    inference(definition_unfolding,[],[f28,f29])).
% 39.62/5.47  
% 39.62/5.47  fof(f14,conjecture,(
% 39.62/5.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 39.62/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.62/5.47  
% 39.62/5.47  fof(f15,negated_conjecture,(
% 39.62/5.47    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 39.62/5.47    inference(negated_conjecture,[],[f14])).
% 39.62/5.47  
% 39.62/5.47  fof(f17,plain,(
% 39.62/5.47    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 39.62/5.47    inference(ennf_transformation,[],[f15])).
% 39.62/5.47  
% 39.62/5.47  fof(f18,plain,(
% 39.62/5.47    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 39.62/5.47    introduced(choice_axiom,[])).
% 39.62/5.47  
% 39.62/5.47  fof(f19,plain,(
% 39.62/5.47    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 39.62/5.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 39.62/5.47  
% 39.62/5.47  fof(f33,plain,(
% 39.62/5.47    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 39.62/5.47    inference(cnf_transformation,[],[f19])).
% 39.62/5.47  
% 39.62/5.47  fof(f39,plain,(
% 39.62/5.47    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 39.62/5.47    inference(definition_unfolding,[],[f33,f29,f22,f22])).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 39.62/5.47      inference(cnf_transformation,[],[f34]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_0,plain,
% 39.62/5.47      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(cnf_transformation,[],[f20]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_5,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.62/5.47      inference(cnf_transformation,[],[f26]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_60,plain,
% 39.62/5.47      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_4,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 39.62/5.47      inference(cnf_transformation,[],[f35]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_3,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.62/5.47      inference(cnf_transformation,[],[f24]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_40,plain,
% 39.62/5.47      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55,plain,
% 39.62/5.47      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_4,c_40]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_75,plain,
% 39.62/5.47      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_60,c_55]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_6,plain,
% 39.62/5.47      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 39.62/5.47      inference(cnf_transformation,[],[f27]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_175,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_75,c_6]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_9,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 39.62/5.47      inference(cnf_transformation,[],[f37]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_8,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 39.62/5.47      inference(cnf_transformation,[],[f30]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_28,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 39.62/5.47      inference(theory_normalisation,[status(thm)],[c_9,c_8,c_0]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_10,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 39.62/5.47      inference(cnf_transformation,[],[f38]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_36,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_10,c_5]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_59,plain,
% 39.62/5.47      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_28,c_36]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_182,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_175,c_59]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_71,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1,c_28]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1882,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_182,c_71]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1940,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_1882,c_5]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_5729,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_0,c_1940]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2,plain,
% 39.62/5.47      ( k2_xboole_0(X0,X0) = X0 ),
% 39.62/5.47      inference(cnf_transformation,[],[f23]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_132,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_2,c_8]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_324,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_0,c_132]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_202,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_0,c_182]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_879,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_324,c_202]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_179,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_75,c_6]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_329,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_28,c_132]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_344,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_329,c_28]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_427,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1,c_344]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_931,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_179,c_427]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_976,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_931,c_5]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_7,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 39.62/5.47      inference(cnf_transformation,[],[f36]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_116,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_37,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_281,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_116,c_37]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_977,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_976,c_281]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1548,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_6,c_977]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_54865,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_879,c_1548]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55415,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_54865,c_3]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_38,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_754,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_116,c_38]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55682,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(k4_xboole_0(X0,X2),X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_55415,c_754]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55790,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_55682,c_344]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_58252,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_5729,c_55790]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_197,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_116,c_8]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2469,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_197,c_324]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_277,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_2,c_37]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2471,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_197,c_277]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2475,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_197,c_38]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2505,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_2471,c_197,c_2475]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2506,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,X2) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_2469,c_2505]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_207,plain,
% 39.62/5.47      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_28,c_182]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_241,plain,
% 39.62/5.47      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1,c_207]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_528,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_241,c_6]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1014,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_528,c_427]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1034,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_1014,c_5]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_756,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_344,c_38]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1035,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_1034,c_756]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_750,plain,
% 39.62/5.47      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_3,c_38]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_72,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_306,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_182,c_72]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_316,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_306,c_5]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_804,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_0,c_316]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1374,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_750,c_804]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_611,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_0,c_277]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_307,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_202,c_72]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_315,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_307,c_5]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1148,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_611,c_315]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1183,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_1148,c_611]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_1428,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_1374,c_1183]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2167,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1035,c_1428]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2225,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_2167,c_1428]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_5761,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_2225,c_1940]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2174,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_977,c_1428]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2219,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_2174,c_1428]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_5888,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X0,X1) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_5761,c_2219,c_2225]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_18202,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X2),X0),X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_2506,c_5888]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_694,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_0,c_315]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_3170,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_694,c_281]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_3276,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X2,X0) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_3170,c_281]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_18407,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_18202,c_3276]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55550,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_18407,c_55415]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_877,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_324,c_277]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_880,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_324,c_38]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_901,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_877,c_324,c_880]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_6919,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_901,c_324]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_6981,plain,
% 39.62/5.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_6919,c_901]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_19647,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1940,c_6981]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_19807,plain,
% 39.62/5.47      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) = k2_xboole_0(X1,X0) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_19647,c_6981]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_440,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_344,c_8]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_3059,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_427,c_440]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_3119,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_3059,c_427]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_3120,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_3119,c_6]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_6165,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_277,c_3120]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55728,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_55415,c_6165]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_57786,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_19807,c_55728]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_80,plain,
% 39.62/5.47      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_57971,plain,
% 39.62/5.47      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_55728,c_80]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_58036,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_57971,c_5,c_182]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_58113,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_57786,c_58036]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55488,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k4_xboole_0(X0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1035,c_55415]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_58114,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_58113,c_55488]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_58619,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_58252,c_55550,c_58114]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_55487,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,X1) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_2219,c_55415]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_58620,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_58619,c_55487]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_59459,plain,
% 39.62/5.47      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X2) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_58620,c_80]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_59620,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 39.62/5.47      inference(light_normalisation,[status(thm)],[c_59459,c_5,c_202]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_11,negated_conjecture,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 39.62/5.47      inference(cnf_transformation,[],[f39]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_27,negated_conjecture,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 39.62/5.47      inference(theory_normalisation,[status(thm)],[c_11,c_8,c_0]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_186426,plain,
% 39.62/5.47      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_59620,c_27]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_206,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_8,c_182]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_2608,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_344,c_206]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_13792,plain,
% 39.62/5.47      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_2219,c_2608]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_186427,plain,
% 39.62/5.47      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 39.62/5.47      inference(demodulation,[status(thm)],[c_186426,c_3,c_13792]) ).
% 39.62/5.47  
% 39.62/5.47  cnf(c_187652,plain,
% 39.62/5.47      ( $false ),
% 39.62/5.47      inference(superposition,[status(thm)],[c_1,c_186427]) ).
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  % SZS output end CNFRefutation for theBenchmark.p
% 39.62/5.47  
% 39.62/5.47  ------                               Statistics
% 39.62/5.47  
% 39.62/5.47  ------ General
% 39.62/5.47  
% 39.62/5.47  abstr_ref_over_cycles:                  0
% 39.62/5.47  abstr_ref_under_cycles:                 0
% 39.62/5.47  gc_basic_clause_elim:                   0
% 39.62/5.47  forced_gc_time:                         0
% 39.62/5.47  parsing_time:                           0.007
% 39.62/5.47  unif_index_cands_time:                  0.
% 39.62/5.47  unif_index_add_time:                    0.
% 39.62/5.47  orderings_time:                         0.
% 39.62/5.47  out_proof_time:                         0.008
% 39.62/5.47  total_time:                             4.873
% 39.62/5.47  num_of_symbols:                         41
% 39.62/5.47  num_of_terms:                           249247
% 39.62/5.47  
% 39.62/5.47  ------ Preprocessing
% 39.62/5.47  
% 39.62/5.47  num_of_splits:                          0
% 39.62/5.47  num_of_split_atoms:                     5
% 39.62/5.47  num_of_reused_defs:                     2
% 39.62/5.47  num_eq_ax_congr_red:                    0
% 39.62/5.47  num_of_sem_filtered_clauses:            0
% 39.62/5.47  num_of_subtypes:                        0
% 39.62/5.47  monotx_restored_types:                  0
% 39.62/5.47  sat_num_of_epr_types:                   0
% 39.62/5.47  sat_num_of_non_cyclic_types:            0
% 39.62/5.47  sat_guarded_non_collapsed_types:        0
% 39.62/5.47  num_pure_diseq_elim:                    0
% 39.62/5.47  simp_replaced_by:                       0
% 39.62/5.47  res_preprocessed:                       28
% 39.62/5.47  prep_upred:                             0
% 39.62/5.47  prep_unflattend:                        0
% 39.62/5.47  smt_new_axioms:                         0
% 39.62/5.47  pred_elim_cands:                        0
% 39.62/5.47  pred_elim:                              0
% 39.62/5.47  pred_elim_cl:                           0
% 39.62/5.47  pred_elim_cycles:                       0
% 39.62/5.47  merged_defs:                            0
% 39.62/5.47  merged_defs_ncl:                        0
% 39.62/5.47  bin_hyper_res:                          0
% 39.62/5.47  prep_cycles:                            2
% 39.62/5.47  pred_elim_time:                         0.
% 39.62/5.47  splitting_time:                         0.
% 39.62/5.47  sem_filter_time:                        0.
% 39.62/5.47  monotx_time:                            0.
% 39.62/5.47  subtype_inf_time:                       0.
% 39.62/5.47  
% 39.62/5.47  ------ Problem properties
% 39.62/5.47  
% 39.62/5.47  clauses:                                12
% 39.62/5.47  conjectures:                            1
% 39.62/5.47  epr:                                    0
% 39.62/5.47  horn:                                   12
% 39.62/5.47  ground:                                 1
% 39.62/5.47  unary:                                  12
% 39.62/5.47  binary:                                 0
% 39.62/5.47  lits:                                   12
% 39.62/5.47  lits_eq:                                12
% 39.62/5.47  fd_pure:                                0
% 39.62/5.47  fd_pseudo:                              0
% 39.62/5.47  fd_cond:                                0
% 39.62/5.47  fd_pseudo_cond:                         0
% 39.62/5.47  ac_symbols:                             1
% 39.62/5.47  
% 39.62/5.47  ------ Propositional Solver
% 39.62/5.47  
% 39.62/5.47  prop_solver_calls:                      13
% 39.62/5.47  prop_fast_solver_calls:                 68
% 39.62/5.47  smt_solver_calls:                       0
% 39.62/5.47  smt_fast_solver_calls:                  0
% 39.62/5.47  prop_num_of_clauses:                    521
% 39.62/5.47  prop_preprocess_simplified:             556
% 39.62/5.47  prop_fo_subsumed:                       0
% 39.62/5.47  prop_solver_time:                       0.
% 39.62/5.47  smt_solver_time:                        0.
% 39.62/5.47  smt_fast_solver_time:                   0.
% 39.62/5.47  prop_fast_solver_time:                  0.
% 39.62/5.47  prop_unsat_core_time:                   0.
% 39.62/5.47  
% 39.62/5.47  ------ QBF
% 39.62/5.47  
% 39.62/5.47  qbf_q_res:                              0
% 39.62/5.47  qbf_num_tautologies:                    0
% 39.62/5.47  qbf_prep_cycles:                        0
% 39.62/5.47  
% 39.62/5.47  ------ BMC1
% 39.62/5.47  
% 39.62/5.47  bmc1_current_bound:                     -1
% 39.62/5.47  bmc1_last_solved_bound:                 -1
% 39.62/5.47  bmc1_unsat_core_size:                   -1
% 39.62/5.47  bmc1_unsat_core_parents_size:           -1
% 39.62/5.47  bmc1_merge_next_fun:                    0
% 39.62/5.47  bmc1_unsat_core_clauses_time:           0.
% 39.62/5.47  
% 39.62/5.47  ------ Instantiation
% 39.62/5.47  
% 39.62/5.47  inst_num_of_clauses:                    0
% 39.62/5.47  inst_num_in_passive:                    0
% 39.62/5.47  inst_num_in_active:                     0
% 39.62/5.47  inst_num_in_unprocessed:                0
% 39.62/5.47  inst_num_of_loops:                      0
% 39.62/5.47  inst_num_of_learning_restarts:          0
% 39.62/5.47  inst_num_moves_active_passive:          0
% 39.62/5.47  inst_lit_activity:                      0
% 39.62/5.47  inst_lit_activity_moves:                0
% 39.62/5.47  inst_num_tautologies:                   0
% 39.62/5.47  inst_num_prop_implied:                  0
% 39.62/5.47  inst_num_existing_simplified:           0
% 39.62/5.47  inst_num_eq_res_simplified:             0
% 39.62/5.47  inst_num_child_elim:                    0
% 39.62/5.47  inst_num_of_dismatching_blockings:      0
% 39.62/5.47  inst_num_of_non_proper_insts:           0
% 39.62/5.47  inst_num_of_duplicates:                 0
% 39.62/5.47  inst_inst_num_from_inst_to_res:         0
% 39.62/5.47  inst_dismatching_checking_time:         0.
% 39.62/5.47  
% 39.62/5.47  ------ Resolution
% 39.62/5.47  
% 39.62/5.47  res_num_of_clauses:                     0
% 39.62/5.47  res_num_in_passive:                     0
% 39.62/5.47  res_num_in_active:                      0
% 39.62/5.47  res_num_of_loops:                       30
% 39.62/5.47  res_forward_subset_subsumed:            0
% 39.62/5.47  res_backward_subset_subsumed:           0
% 39.62/5.47  res_forward_subsumed:                   0
% 39.62/5.47  res_backward_subsumed:                  0
% 39.62/5.47  res_forward_subsumption_resolution:     0
% 39.62/5.47  res_backward_subsumption_resolution:    0
% 39.62/5.47  res_clause_to_clause_subsumption:       624103
% 39.62/5.47  res_orphan_elimination:                 0
% 39.62/5.47  res_tautology_del:                      0
% 39.62/5.47  res_num_eq_res_simplified:              0
% 39.62/5.47  res_num_sel_changes:                    0
% 39.62/5.47  res_moves_from_active_to_pass:          0
% 39.62/5.47  
% 39.62/5.47  ------ Superposition
% 39.62/5.47  
% 39.62/5.47  sup_time_total:                         0.
% 39.62/5.47  sup_time_generating:                    0.
% 39.62/5.47  sup_time_sim_full:                      0.
% 39.62/5.47  sup_time_sim_immed:                     0.
% 39.62/5.47  
% 39.62/5.47  sup_num_of_clauses:                     11048
% 39.62/5.47  sup_num_in_active:                      302
% 39.62/5.47  sup_num_in_passive:                     10746
% 39.62/5.47  sup_num_of_loops:                       338
% 39.62/5.47  sup_fw_superposition:                   66716
% 39.62/5.47  sup_bw_superposition:                   50895
% 39.62/5.47  sup_immediate_simplified:               60893
% 39.62/5.47  sup_given_eliminated:                   9
% 39.62/5.47  comparisons_done:                       0
% 39.62/5.47  comparisons_avoided:                    0
% 39.62/5.47  
% 39.62/5.47  ------ Simplifications
% 39.62/5.47  
% 39.62/5.47  
% 39.62/5.47  sim_fw_subset_subsumed:                 0
% 39.62/5.47  sim_bw_subset_subsumed:                 0
% 39.62/5.47  sim_fw_subsumed:                        5064
% 39.62/5.47  sim_bw_subsumed:                        108
% 39.62/5.47  sim_fw_subsumption_res:                 0
% 39.62/5.47  sim_bw_subsumption_res:                 0
% 39.62/5.47  sim_tautology_del:                      0
% 39.62/5.47  sim_eq_tautology_del:                   16195
% 39.62/5.47  sim_eq_res_simp:                        0
% 39.62/5.47  sim_fw_demodulated:                     47661
% 39.62/5.47  sim_bw_demodulated:                     277
% 39.62/5.47  sim_light_normalised:                   21233
% 39.62/5.47  sim_joinable_taut:                      1636
% 39.62/5.47  sim_joinable_simp:                      0
% 39.62/5.47  sim_ac_normalised:                      0
% 39.62/5.47  sim_smt_subsumption:                    0
% 39.62/5.47  
%------------------------------------------------------------------------------
