%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:58 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  131 (59882 expanded)
%              Number of clauses        :  106 (23858 expanded)
%              Number of leaves         :   10 (16421 expanded)
%              Depth                    :   31
%              Number of atoms          :  132 (59883 expanded)
%              Number of equality atoms :  131 (59882 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f15,f20,f20])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f22,f16,f16,f20])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_5,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_28,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_29,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_28,c_2])).

cnf(c_128,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_5,c_29])).

cnf(c_129,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_130,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_128,c_129])).

cnf(c_190,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_130,c_0])).

cnf(c_187,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_130,c_3])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_281,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_187,c_4])).

cnf(c_25,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_32,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_2,c_25])).

cnf(c_35,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_32,c_25])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_108,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_33,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_25,c_2])).

cnf(c_34,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_33,c_2])).

cnf(c_155,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_108,c_34])).

cnf(c_161,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_155,c_108])).

cnf(c_246,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_35,c_161])).

cnf(c_253,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_246,c_4])).

cnf(c_254,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_253,c_2])).

cnf(c_351,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(light_normalisation,[status(thm)],[c_254,c_254,c_281])).

cnf(c_365,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X1,X1),X0) ),
    inference(superposition,[status(thm)],[c_351,c_2])).

cnf(c_371,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_365,c_351])).

cnf(c_195,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_190])).

cnf(c_369,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_351,c_195])).

cnf(c_372,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_371,c_369])).

cnf(c_373,plain,
    ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_372])).

cnf(c_378,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_281,c_281,c_373])).

cnf(c_395,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(sP0_iProver_split,X0) ),
    inference(superposition,[status(thm)],[c_378,c_187])).

cnf(c_415,plain,
    ( k4_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_395,c_373])).

cnf(c_403,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(sP0_iProver_split,X2) ),
    inference(superposition,[status(thm)],[c_378,c_4])).

cnf(c_416,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_415,c_403])).

cnf(c_1165,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_0,c_416])).

cnf(c_1397,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_190,c_1165])).

cnf(c_2652,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1397,c_161])).

cnf(c_383,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_2,c_378])).

cnf(c_472,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_383,c_1])).

cnf(c_27,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_39,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2,c_29])).

cnf(c_184,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_25,c_130])).

cnf(c_318,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_39,c_184])).

cnf(c_333,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_318,c_27])).

cnf(c_343,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_333,c_4,c_190])).

cnf(c_480,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_472,c_27,c_343])).

cnf(c_2683,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2652,c_480])).

cnf(c_405,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)),sP0_iProver_split) = X1 ),
    inference(superposition,[status(thm)],[c_378,c_108])).

cnf(c_54,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_27])).

cnf(c_410,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),sP0_iProver_split) = X0 ),
    inference(light_normalisation,[status(thm)],[c_405,c_3,c_54])).

cnf(c_522,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_410,c_27])).

cnf(c_376,plain,
    ( k2_xboole_0(sP0_iProver_split,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_373,c_351])).

cnf(c_422,plain,
    ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_365,c_373,c_376])).

cnf(c_536,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_522,c_4,c_415,c_422,c_480])).

cnf(c_779,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_536,c_27])).

cnf(c_2173,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),sP0_iProver_split) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_383,c_779])).

cnf(c_197,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_190])).

cnf(c_2014,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_197])).

cnf(c_2227,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2173,c_2014])).

cnf(c_468,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(sP0_iProver_split,X2) ),
    inference(superposition,[status(thm)],[c_383,c_4])).

cnf(c_483,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_468,c_4,c_415])).

cnf(c_3252,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(sP0_iProver_split,k2_xboole_0(X1,X0)),X2)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_2227,c_483])).

cnf(c_93,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_4,c_4])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_93,c_4])).

cnf(c_385,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_29,c_378])).

cnf(c_400,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sP0_iProver_split),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_378,c_108])).

cnf(c_411,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sP0_iProver_split),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_400,c_3])).

cnf(c_425,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_422,c_411])).

cnf(c_1271,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_385,c_425])).

cnf(c_1007,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_385,c_2])).

cnf(c_43,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_29,c_29])).

cnf(c_474,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_383,c_2])).

cnf(c_199,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_25,c_190])).

cnf(c_477,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_474,c_199])).

cnf(c_1009,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1007,c_43,c_477])).

cnf(c_1315,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1271,c_1009])).

cnf(c_2469,plain,
    ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1315,c_0])).

cnf(c_3382,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_3252,c_102,c_2469])).

cnf(c_12043,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_2683,c_3382])).

cnf(c_19960,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),sP0_iProver_split),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_12043,c_161])).

cnf(c_91,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_25,c_4])).

cnf(c_104,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_91,c_4])).

cnf(c_15301,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_104,c_2])).

cnf(c_15347,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_15301,c_425])).

cnf(c_20036,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_19960,c_2227,c_15347])).

cnf(c_805,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_536,c_4])).

cnf(c_4165,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_29,c_805])).

cnf(c_4277,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4165,c_805])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_23,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6,c_4])).

cnf(c_24,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_23])).

cnf(c_45,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_34,c_24])).

cnf(c_14425,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4277,c_45])).

cnf(c_2424,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_2,c_1315])).

cnf(c_2501,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2424,c_1315])).

cnf(c_4209,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_805,c_2501])).

cnf(c_2738,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sP0_iProver_split,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_2227,c_4])).

cnf(c_2757,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_2738,c_376])).

cnf(c_11905,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2757,c_2])).

cnf(c_14426,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14425,c_4209,c_11905])).

cnf(c_30746,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_20036,c_14426])).

cnf(c_30747,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_30746,c_2501])).

cnf(c_31101,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_0,c_30747])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.44/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.44/1.49  
% 7.44/1.49  ------  iProver source info
% 7.44/1.49  
% 7.44/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.44/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.44/1.49  git: non_committed_changes: false
% 7.44/1.49  git: last_make_outside_of_git: false
% 7.44/1.49  
% 7.44/1.49  ------ 
% 7.44/1.49  
% 7.44/1.49  ------ Input Options
% 7.44/1.49  
% 7.44/1.49  --out_options                           all
% 7.44/1.49  --tptp_safe_out                         true
% 7.44/1.49  --problem_path                          ""
% 7.44/1.49  --include_path                          ""
% 7.44/1.49  --clausifier                            res/vclausify_rel
% 7.44/1.49  --clausifier_options                    --mode clausify
% 7.44/1.49  --stdin                                 false
% 7.44/1.49  --stats_out                             all
% 7.44/1.49  
% 7.44/1.49  ------ General Options
% 7.44/1.49  
% 7.44/1.49  --fof                                   false
% 7.44/1.49  --time_out_real                         305.
% 7.44/1.49  --time_out_virtual                      -1.
% 7.44/1.49  --symbol_type_check                     false
% 7.44/1.49  --clausify_out                          false
% 7.44/1.49  --sig_cnt_out                           false
% 7.44/1.49  --trig_cnt_out                          false
% 7.44/1.49  --trig_cnt_out_tolerance                1.
% 7.44/1.49  --trig_cnt_out_sk_spl                   false
% 7.44/1.49  --abstr_cl_out                          false
% 7.44/1.49  
% 7.44/1.49  ------ Global Options
% 7.44/1.49  
% 7.44/1.49  --schedule                              default
% 7.44/1.49  --add_important_lit                     false
% 7.44/1.49  --prop_solver_per_cl                    1000
% 7.44/1.49  --min_unsat_core                        false
% 7.44/1.49  --soft_assumptions                      false
% 7.44/1.49  --soft_lemma_size                       3
% 7.44/1.49  --prop_impl_unit_size                   0
% 7.44/1.49  --prop_impl_unit                        []
% 7.44/1.49  --share_sel_clauses                     true
% 7.44/1.49  --reset_solvers                         false
% 7.44/1.49  --bc_imp_inh                            [conj_cone]
% 7.44/1.49  --conj_cone_tolerance                   3.
% 7.44/1.49  --extra_neg_conj                        none
% 7.44/1.49  --large_theory_mode                     true
% 7.44/1.49  --prolific_symb_bound                   200
% 7.44/1.49  --lt_threshold                          2000
% 7.44/1.49  --clause_weak_htbl                      true
% 7.44/1.49  --gc_record_bc_elim                     false
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing Options
% 7.44/1.49  
% 7.44/1.49  --preprocessing_flag                    true
% 7.44/1.49  --time_out_prep_mult                    0.1
% 7.44/1.49  --splitting_mode                        input
% 7.44/1.49  --splitting_grd                         true
% 7.44/1.49  --splitting_cvd                         false
% 7.44/1.49  --splitting_cvd_svl                     false
% 7.44/1.49  --splitting_nvd                         32
% 7.44/1.49  --sub_typing                            true
% 7.44/1.49  --prep_gs_sim                           true
% 7.44/1.49  --prep_unflatten                        true
% 7.44/1.49  --prep_res_sim                          true
% 7.44/1.49  --prep_upred                            true
% 7.44/1.49  --prep_sem_filter                       exhaustive
% 7.44/1.49  --prep_sem_filter_out                   false
% 7.44/1.49  --pred_elim                             true
% 7.44/1.49  --res_sim_input                         true
% 7.44/1.49  --eq_ax_congr_red                       true
% 7.44/1.49  --pure_diseq_elim                       true
% 7.44/1.49  --brand_transform                       false
% 7.44/1.49  --non_eq_to_eq                          false
% 7.44/1.49  --prep_def_merge                        true
% 7.44/1.49  --prep_def_merge_prop_impl              false
% 7.44/1.49  --prep_def_merge_mbd                    true
% 7.44/1.49  --prep_def_merge_tr_red                 false
% 7.44/1.49  --prep_def_merge_tr_cl                  false
% 7.44/1.49  --smt_preprocessing                     true
% 7.44/1.49  --smt_ac_axioms                         fast
% 7.44/1.49  --preprocessed_out                      false
% 7.44/1.49  --preprocessed_stats                    false
% 7.44/1.49  
% 7.44/1.49  ------ Abstraction refinement Options
% 7.44/1.49  
% 7.44/1.49  --abstr_ref                             []
% 7.44/1.49  --abstr_ref_prep                        false
% 7.44/1.49  --abstr_ref_until_sat                   false
% 7.44/1.49  --abstr_ref_sig_restrict                funpre
% 7.44/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.49  --abstr_ref_under                       []
% 7.44/1.49  
% 7.44/1.49  ------ SAT Options
% 7.44/1.49  
% 7.44/1.49  --sat_mode                              false
% 7.44/1.49  --sat_fm_restart_options                ""
% 7.44/1.49  --sat_gr_def                            false
% 7.44/1.49  --sat_epr_types                         true
% 7.44/1.49  --sat_non_cyclic_types                  false
% 7.44/1.49  --sat_finite_models                     false
% 7.44/1.49  --sat_fm_lemmas                         false
% 7.44/1.49  --sat_fm_prep                           false
% 7.44/1.49  --sat_fm_uc_incr                        true
% 7.44/1.49  --sat_out_model                         small
% 7.44/1.49  --sat_out_clauses                       false
% 7.44/1.49  
% 7.44/1.49  ------ QBF Options
% 7.44/1.49  
% 7.44/1.49  --qbf_mode                              false
% 7.44/1.49  --qbf_elim_univ                         false
% 7.44/1.49  --qbf_dom_inst                          none
% 7.44/1.49  --qbf_dom_pre_inst                      false
% 7.44/1.49  --qbf_sk_in                             false
% 7.44/1.49  --qbf_pred_elim                         true
% 7.44/1.49  --qbf_split                             512
% 7.44/1.49  
% 7.44/1.49  ------ BMC1 Options
% 7.44/1.49  
% 7.44/1.49  --bmc1_incremental                      false
% 7.44/1.49  --bmc1_axioms                           reachable_all
% 7.44/1.49  --bmc1_min_bound                        0
% 7.44/1.49  --bmc1_max_bound                        -1
% 7.44/1.49  --bmc1_max_bound_default                -1
% 7.44/1.49  --bmc1_symbol_reachability              true
% 7.44/1.49  --bmc1_property_lemmas                  false
% 7.44/1.49  --bmc1_k_induction                      false
% 7.44/1.49  --bmc1_non_equiv_states                 false
% 7.44/1.49  --bmc1_deadlock                         false
% 7.44/1.49  --bmc1_ucm                              false
% 7.44/1.49  --bmc1_add_unsat_core                   none
% 7.44/1.49  --bmc1_unsat_core_children              false
% 7.44/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.49  --bmc1_out_stat                         full
% 7.44/1.49  --bmc1_ground_init                      false
% 7.44/1.49  --bmc1_pre_inst_next_state              false
% 7.44/1.49  --bmc1_pre_inst_state                   false
% 7.44/1.49  --bmc1_pre_inst_reach_state             false
% 7.44/1.49  --bmc1_out_unsat_core                   false
% 7.44/1.49  --bmc1_aig_witness_out                  false
% 7.44/1.49  --bmc1_verbose                          false
% 7.44/1.49  --bmc1_dump_clauses_tptp                false
% 7.44/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.49  --bmc1_dump_file                        -
% 7.44/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.49  --bmc1_ucm_extend_mode                  1
% 7.44/1.49  --bmc1_ucm_init_mode                    2
% 7.44/1.49  --bmc1_ucm_cone_mode                    none
% 7.44/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.49  --bmc1_ucm_relax_model                  4
% 7.44/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.49  --bmc1_ucm_layered_model                none
% 7.44/1.49  --bmc1_ucm_max_lemma_size               10
% 7.44/1.49  
% 7.44/1.49  ------ AIG Options
% 7.44/1.49  
% 7.44/1.49  --aig_mode                              false
% 7.44/1.49  
% 7.44/1.49  ------ Instantiation Options
% 7.44/1.49  
% 7.44/1.49  --instantiation_flag                    true
% 7.44/1.49  --inst_sos_flag                         false
% 7.44/1.49  --inst_sos_phase                        true
% 7.44/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel_side                     num_symb
% 7.44/1.49  --inst_solver_per_active                1400
% 7.44/1.49  --inst_solver_calls_frac                1.
% 7.44/1.49  --inst_passive_queue_type               priority_queues
% 7.44/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.49  --inst_passive_queues_freq              [25;2]
% 7.44/1.49  --inst_dismatching                      true
% 7.44/1.49  --inst_eager_unprocessed_to_passive     true
% 7.44/1.49  --inst_prop_sim_given                   true
% 7.44/1.49  --inst_prop_sim_new                     false
% 7.44/1.49  --inst_subs_new                         false
% 7.44/1.49  --inst_eq_res_simp                      false
% 7.44/1.49  --inst_subs_given                       false
% 7.44/1.49  --inst_orphan_elimination               true
% 7.44/1.49  --inst_learning_loop_flag               true
% 7.44/1.49  --inst_learning_start                   3000
% 7.44/1.49  --inst_learning_factor                  2
% 7.44/1.49  --inst_start_prop_sim_after_learn       3
% 7.44/1.49  --inst_sel_renew                        solver
% 7.44/1.49  --inst_lit_activity_flag                true
% 7.44/1.49  --inst_restr_to_given                   false
% 7.44/1.49  --inst_activity_threshold               500
% 7.44/1.49  --inst_out_proof                        true
% 7.44/1.49  
% 7.44/1.49  ------ Resolution Options
% 7.44/1.49  
% 7.44/1.49  --resolution_flag                       true
% 7.44/1.49  --res_lit_sel                           adaptive
% 7.44/1.49  --res_lit_sel_side                      none
% 7.44/1.49  --res_ordering                          kbo
% 7.44/1.49  --res_to_prop_solver                    active
% 7.44/1.49  --res_prop_simpl_new                    false
% 7.44/1.49  --res_prop_simpl_given                  true
% 7.44/1.49  --res_passive_queue_type                priority_queues
% 7.44/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.49  --res_passive_queues_freq               [15;5]
% 7.44/1.49  --res_forward_subs                      full
% 7.44/1.49  --res_backward_subs                     full
% 7.44/1.49  --res_forward_subs_resolution           true
% 7.44/1.49  --res_backward_subs_resolution          true
% 7.44/1.49  --res_orphan_elimination                true
% 7.44/1.49  --res_time_limit                        2.
% 7.44/1.49  --res_out_proof                         true
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Options
% 7.44/1.49  
% 7.44/1.49  --superposition_flag                    true
% 7.44/1.49  --sup_passive_queue_type                priority_queues
% 7.44/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.49  --demod_completeness_check              fast
% 7.44/1.49  --demod_use_ground                      true
% 7.44/1.49  --sup_to_prop_solver                    passive
% 7.44/1.49  --sup_prop_simpl_new                    true
% 7.44/1.49  --sup_prop_simpl_given                  true
% 7.44/1.49  --sup_fun_splitting                     false
% 7.44/1.49  --sup_smt_interval                      50000
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Simplification Setup
% 7.44/1.49  
% 7.44/1.49  --sup_indices_passive                   []
% 7.44/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.49  --sup_full_bw                           [BwDemod]
% 7.44/1.49  --sup_immed_triv                        [TrivRules]
% 7.44/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.49  --sup_immed_bw_main                     []
% 7.44/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.49  
% 7.44/1.49  ------ Combination Options
% 7.44/1.49  
% 7.44/1.49  --comb_res_mult                         3
% 7.44/1.49  --comb_sup_mult                         2
% 7.44/1.49  --comb_inst_mult                        10
% 7.44/1.49  
% 7.44/1.49  ------ Debug Options
% 7.44/1.49  
% 7.44/1.49  --dbg_backtrace                         false
% 7.44/1.49  --dbg_dump_prop_clauses                 false
% 7.44/1.49  --dbg_dump_prop_clauses_file            -
% 7.44/1.49  --dbg_out_stat                          false
% 7.44/1.49  ------ Parsing...
% 7.44/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.44/1.49  ------ Proving...
% 7.44/1.49  ------ Problem Properties 
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  clauses                                 7
% 7.44/1.49  conjectures                             1
% 7.44/1.49  EPR                                     0
% 7.44/1.49  Horn                                    7
% 7.44/1.49  unary                                   7
% 7.44/1.49  binary                                  0
% 7.44/1.49  lits                                    7
% 7.44/1.49  lits eq                                 7
% 7.44/1.49  fd_pure                                 0
% 7.44/1.49  fd_pseudo                               0
% 7.44/1.49  fd_cond                                 0
% 7.44/1.49  fd_pseudo_cond                          0
% 7.44/1.49  AC symbols                              0
% 7.44/1.49  
% 7.44/1.49  ------ Schedule UEQ
% 7.44/1.49  
% 7.44/1.49  ------ pure equality problem: resolution off 
% 7.44/1.49  
% 7.44/1.49  ------ Option_UEQ Time Limit: Unbounded
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  ------ 
% 7.44/1.49  Current options:
% 7.44/1.49  ------ 
% 7.44/1.49  
% 7.44/1.49  ------ Input Options
% 7.44/1.49  
% 7.44/1.49  --out_options                           all
% 7.44/1.49  --tptp_safe_out                         true
% 7.44/1.49  --problem_path                          ""
% 7.44/1.49  --include_path                          ""
% 7.44/1.49  --clausifier                            res/vclausify_rel
% 7.44/1.49  --clausifier_options                    --mode clausify
% 7.44/1.49  --stdin                                 false
% 7.44/1.49  --stats_out                             all
% 7.44/1.49  
% 7.44/1.49  ------ General Options
% 7.44/1.49  
% 7.44/1.49  --fof                                   false
% 7.44/1.49  --time_out_real                         305.
% 7.44/1.49  --time_out_virtual                      -1.
% 7.44/1.49  --symbol_type_check                     false
% 7.44/1.49  --clausify_out                          false
% 7.44/1.49  --sig_cnt_out                           false
% 7.44/1.49  --trig_cnt_out                          false
% 7.44/1.49  --trig_cnt_out_tolerance                1.
% 7.44/1.49  --trig_cnt_out_sk_spl                   false
% 7.44/1.49  --abstr_cl_out                          false
% 7.44/1.49  
% 7.44/1.49  ------ Global Options
% 7.44/1.49  
% 7.44/1.49  --schedule                              default
% 7.44/1.49  --add_important_lit                     false
% 7.44/1.49  --prop_solver_per_cl                    1000
% 7.44/1.49  --min_unsat_core                        false
% 7.44/1.49  --soft_assumptions                      false
% 7.44/1.49  --soft_lemma_size                       3
% 7.44/1.49  --prop_impl_unit_size                   0
% 7.44/1.49  --prop_impl_unit                        []
% 7.44/1.49  --share_sel_clauses                     true
% 7.44/1.49  --reset_solvers                         false
% 7.44/1.49  --bc_imp_inh                            [conj_cone]
% 7.44/1.49  --conj_cone_tolerance                   3.
% 7.44/1.49  --extra_neg_conj                        none
% 7.44/1.49  --large_theory_mode                     true
% 7.44/1.49  --prolific_symb_bound                   200
% 7.44/1.49  --lt_threshold                          2000
% 7.44/1.49  --clause_weak_htbl                      true
% 7.44/1.49  --gc_record_bc_elim                     false
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing Options
% 7.44/1.49  
% 7.44/1.49  --preprocessing_flag                    true
% 7.44/1.49  --time_out_prep_mult                    0.1
% 7.44/1.49  --splitting_mode                        input
% 7.44/1.49  --splitting_grd                         true
% 7.44/1.49  --splitting_cvd                         false
% 7.44/1.49  --splitting_cvd_svl                     false
% 7.44/1.49  --splitting_nvd                         32
% 7.44/1.49  --sub_typing                            true
% 7.44/1.49  --prep_gs_sim                           true
% 7.44/1.49  --prep_unflatten                        true
% 7.44/1.49  --prep_res_sim                          true
% 7.44/1.49  --prep_upred                            true
% 7.44/1.49  --prep_sem_filter                       exhaustive
% 7.44/1.49  --prep_sem_filter_out                   false
% 7.44/1.49  --pred_elim                             true
% 7.44/1.49  --res_sim_input                         true
% 7.44/1.49  --eq_ax_congr_red                       true
% 7.44/1.49  --pure_diseq_elim                       true
% 7.44/1.49  --brand_transform                       false
% 7.44/1.49  --non_eq_to_eq                          false
% 7.44/1.49  --prep_def_merge                        true
% 7.44/1.49  --prep_def_merge_prop_impl              false
% 7.44/1.49  --prep_def_merge_mbd                    true
% 7.44/1.49  --prep_def_merge_tr_red                 false
% 7.44/1.49  --prep_def_merge_tr_cl                  false
% 7.44/1.49  --smt_preprocessing                     true
% 7.44/1.49  --smt_ac_axioms                         fast
% 7.44/1.49  --preprocessed_out                      false
% 7.44/1.49  --preprocessed_stats                    false
% 7.44/1.49  
% 7.44/1.49  ------ Abstraction refinement Options
% 7.44/1.49  
% 7.44/1.49  --abstr_ref                             []
% 7.44/1.49  --abstr_ref_prep                        false
% 7.44/1.49  --abstr_ref_until_sat                   false
% 7.44/1.49  --abstr_ref_sig_restrict                funpre
% 7.44/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.49  --abstr_ref_under                       []
% 7.44/1.49  
% 7.44/1.49  ------ SAT Options
% 7.44/1.49  
% 7.44/1.49  --sat_mode                              false
% 7.44/1.49  --sat_fm_restart_options                ""
% 7.44/1.49  --sat_gr_def                            false
% 7.44/1.49  --sat_epr_types                         true
% 7.44/1.49  --sat_non_cyclic_types                  false
% 7.44/1.49  --sat_finite_models                     false
% 7.44/1.49  --sat_fm_lemmas                         false
% 7.44/1.49  --sat_fm_prep                           false
% 7.44/1.49  --sat_fm_uc_incr                        true
% 7.44/1.49  --sat_out_model                         small
% 7.44/1.49  --sat_out_clauses                       false
% 7.44/1.49  
% 7.44/1.49  ------ QBF Options
% 7.44/1.49  
% 7.44/1.49  --qbf_mode                              false
% 7.44/1.49  --qbf_elim_univ                         false
% 7.44/1.49  --qbf_dom_inst                          none
% 7.44/1.49  --qbf_dom_pre_inst                      false
% 7.44/1.49  --qbf_sk_in                             false
% 7.44/1.49  --qbf_pred_elim                         true
% 7.44/1.49  --qbf_split                             512
% 7.44/1.49  
% 7.44/1.49  ------ BMC1 Options
% 7.44/1.49  
% 7.44/1.49  --bmc1_incremental                      false
% 7.44/1.49  --bmc1_axioms                           reachable_all
% 7.44/1.49  --bmc1_min_bound                        0
% 7.44/1.49  --bmc1_max_bound                        -1
% 7.44/1.49  --bmc1_max_bound_default                -1
% 7.44/1.49  --bmc1_symbol_reachability              true
% 7.44/1.49  --bmc1_property_lemmas                  false
% 7.44/1.49  --bmc1_k_induction                      false
% 7.44/1.49  --bmc1_non_equiv_states                 false
% 7.44/1.49  --bmc1_deadlock                         false
% 7.44/1.49  --bmc1_ucm                              false
% 7.44/1.49  --bmc1_add_unsat_core                   none
% 7.44/1.49  --bmc1_unsat_core_children              false
% 7.44/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.49  --bmc1_out_stat                         full
% 7.44/1.49  --bmc1_ground_init                      false
% 7.44/1.49  --bmc1_pre_inst_next_state              false
% 7.44/1.49  --bmc1_pre_inst_state                   false
% 7.44/1.49  --bmc1_pre_inst_reach_state             false
% 7.44/1.49  --bmc1_out_unsat_core                   false
% 7.44/1.49  --bmc1_aig_witness_out                  false
% 7.44/1.49  --bmc1_verbose                          false
% 7.44/1.49  --bmc1_dump_clauses_tptp                false
% 7.44/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.49  --bmc1_dump_file                        -
% 7.44/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.49  --bmc1_ucm_extend_mode                  1
% 7.44/1.49  --bmc1_ucm_init_mode                    2
% 7.44/1.49  --bmc1_ucm_cone_mode                    none
% 7.44/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.49  --bmc1_ucm_relax_model                  4
% 7.44/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.49  --bmc1_ucm_layered_model                none
% 7.44/1.49  --bmc1_ucm_max_lemma_size               10
% 7.44/1.49  
% 7.44/1.49  ------ AIG Options
% 7.44/1.49  
% 7.44/1.49  --aig_mode                              false
% 7.44/1.49  
% 7.44/1.49  ------ Instantiation Options
% 7.44/1.49  
% 7.44/1.49  --instantiation_flag                    false
% 7.44/1.49  --inst_sos_flag                         false
% 7.44/1.49  --inst_sos_phase                        true
% 7.44/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.49  --inst_lit_sel_side                     num_symb
% 7.44/1.49  --inst_solver_per_active                1400
% 7.44/1.49  --inst_solver_calls_frac                1.
% 7.44/1.49  --inst_passive_queue_type               priority_queues
% 7.44/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.49  --inst_passive_queues_freq              [25;2]
% 7.44/1.49  --inst_dismatching                      true
% 7.44/1.49  --inst_eager_unprocessed_to_passive     true
% 7.44/1.49  --inst_prop_sim_given                   true
% 7.44/1.49  --inst_prop_sim_new                     false
% 7.44/1.49  --inst_subs_new                         false
% 7.44/1.49  --inst_eq_res_simp                      false
% 7.44/1.49  --inst_subs_given                       false
% 7.44/1.49  --inst_orphan_elimination               true
% 7.44/1.49  --inst_learning_loop_flag               true
% 7.44/1.49  --inst_learning_start                   3000
% 7.44/1.49  --inst_learning_factor                  2
% 7.44/1.49  --inst_start_prop_sim_after_learn       3
% 7.44/1.49  --inst_sel_renew                        solver
% 7.44/1.49  --inst_lit_activity_flag                true
% 7.44/1.49  --inst_restr_to_given                   false
% 7.44/1.49  --inst_activity_threshold               500
% 7.44/1.49  --inst_out_proof                        true
% 7.44/1.49  
% 7.44/1.49  ------ Resolution Options
% 7.44/1.49  
% 7.44/1.49  --resolution_flag                       false
% 7.44/1.49  --res_lit_sel                           adaptive
% 7.44/1.49  --res_lit_sel_side                      none
% 7.44/1.49  --res_ordering                          kbo
% 7.44/1.49  --res_to_prop_solver                    active
% 7.44/1.49  --res_prop_simpl_new                    false
% 7.44/1.49  --res_prop_simpl_given                  true
% 7.44/1.49  --res_passive_queue_type                priority_queues
% 7.44/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.49  --res_passive_queues_freq               [15;5]
% 7.44/1.49  --res_forward_subs                      full
% 7.44/1.49  --res_backward_subs                     full
% 7.44/1.49  --res_forward_subs_resolution           true
% 7.44/1.49  --res_backward_subs_resolution          true
% 7.44/1.49  --res_orphan_elimination                true
% 7.44/1.49  --res_time_limit                        2.
% 7.44/1.49  --res_out_proof                         true
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Options
% 7.44/1.49  
% 7.44/1.49  --superposition_flag                    true
% 7.44/1.49  --sup_passive_queue_type                priority_queues
% 7.44/1.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.49  --demod_completeness_check              fast
% 7.44/1.49  --demod_use_ground                      true
% 7.44/1.49  --sup_to_prop_solver                    active
% 7.44/1.49  --sup_prop_simpl_new                    false
% 7.44/1.49  --sup_prop_simpl_given                  false
% 7.44/1.49  --sup_fun_splitting                     true
% 7.44/1.49  --sup_smt_interval                      10000
% 7.44/1.49  
% 7.44/1.49  ------ Superposition Simplification Setup
% 7.44/1.49  
% 7.44/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.44/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.49  --sup_full_triv                         [TrivRules]
% 7.44/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.44/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.44/1.49  --sup_immed_triv                        [TrivRules]
% 7.44/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_immed_bw_main                     []
% 7.44/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.44/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.44/1.49  
% 7.44/1.49  ------ Combination Options
% 7.44/1.49  
% 7.44/1.49  --comb_res_mult                         1
% 7.44/1.49  --comb_sup_mult                         1
% 7.44/1.49  --comb_inst_mult                        1000000
% 7.44/1.49  
% 7.44/1.49  ------ Debug Options
% 7.44/1.49  
% 7.44/1.49  --dbg_backtrace                         false
% 7.44/1.49  --dbg_dump_prop_clauses                 false
% 7.44/1.49  --dbg_dump_prop_clauses_file            -
% 7.44/1.49  --dbg_out_stat                          false
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  ------ Proving...
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  % SZS status Theorem for theBenchmark.p
% 7.44/1.49  
% 7.44/1.49   Resolution empty clause
% 7.44/1.49  
% 7.44/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  fof(f1,axiom,(
% 7.44/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f14,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f1])).
% 7.44/1.49  
% 7.44/1.49  fof(f8,axiom,(
% 7.44/1.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f21,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.44/1.49    inference(cnf_transformation,[],[f8])).
% 7.44/1.49  
% 7.44/1.49  fof(f7,axiom,(
% 7.44/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f20,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.44/1.49    inference(cnf_transformation,[],[f7])).
% 7.44/1.49  
% 7.44/1.49  fof(f24,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.44/1.49    inference(definition_unfolding,[],[f21,f20])).
% 7.44/1.49  
% 7.44/1.49  fof(f5,axiom,(
% 7.44/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f18,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f5])).
% 7.44/1.49  
% 7.44/1.49  fof(f4,axiom,(
% 7.44/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f17,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.44/1.49    inference(cnf_transformation,[],[f4])).
% 7.44/1.49  
% 7.44/1.49  fof(f6,axiom,(
% 7.44/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f19,plain,(
% 7.44/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f6])).
% 7.44/1.49  
% 7.44/1.49  fof(f2,axiom,(
% 7.44/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f15,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f2])).
% 7.44/1.49  
% 7.44/1.49  fof(f23,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.44/1.49    inference(definition_unfolding,[],[f15,f20,f20])).
% 7.44/1.49  
% 7.44/1.49  fof(f9,conjecture,(
% 7.44/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f10,negated_conjecture,(
% 7.44/1.49    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.44/1.49    inference(negated_conjecture,[],[f9])).
% 7.44/1.49  
% 7.44/1.49  fof(f11,plain,(
% 7.44/1.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.44/1.49    inference(ennf_transformation,[],[f10])).
% 7.44/1.49  
% 7.44/1.49  fof(f12,plain,(
% 7.44/1.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.44/1.49    introduced(choice_axiom,[])).
% 7.44/1.49  
% 7.44/1.49  fof(f13,plain,(
% 7.44/1.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.44/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 7.44/1.49  
% 7.44/1.49  fof(f22,plain,(
% 7.44/1.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.44/1.49    inference(cnf_transformation,[],[f13])).
% 7.44/1.49  
% 7.44/1.49  fof(f3,axiom,(
% 7.44/1.49    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.44/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.49  
% 7.44/1.49  fof(f16,plain,(
% 7.44/1.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.44/1.49    inference(cnf_transformation,[],[f3])).
% 7.44/1.49  
% 7.44/1.49  fof(f25,plain,(
% 7.44/1.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 7.44/1.49    inference(definition_unfolding,[],[f22,f16,f16,f20])).
% 7.44/1.49  
% 7.44/1.49  cnf(c_0,plain,
% 7.44/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(cnf_transformation,[],[f14]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_5,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.44/1.49      inference(cnf_transformation,[],[f24]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f18]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(cnf_transformation,[],[f17]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_28,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_29,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_28,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_128,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5,c_29]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_129,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_130,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_128,c_129]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_190,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_130,c_0]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_187,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_130,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.44/1.49      inference(cnf_transformation,[],[f19]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_281,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_187,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_25,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_32,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2,c_25]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_35,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_32,c_25]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.44/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_108,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_33,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_25,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_34,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_33,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_155,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_108,c_34]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_161,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_155,c_108]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_246,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1) = X1 ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_35,c_161]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_253,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),X1) = X1 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_246,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_254,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),X1) = X1 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_253,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_351,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_254,c_254,c_281]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_365,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X1,X1),X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_351,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_371,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_365,c_351]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_195,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1,c_190]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_369,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_351,c_195]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_372,plain,
% 7.44/1.49      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_371,c_369]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_373,plain,
% 7.44/1.49      ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
% 7.44/1.49      inference(splitting,
% 7.44/1.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.44/1.49                [c_372]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_378,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = sP0_iProver_split ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_281,c_281,c_373]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_395,plain,
% 7.44/1.49      ( k4_xboole_0(X0,X0) = k4_xboole_0(sP0_iProver_split,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_378,c_187]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_415,plain,
% 7.44/1.49      ( k4_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_395,c_373]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_403,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(sP0_iProver_split,X2) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_378,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_416,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = sP0_iProver_split ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_415,c_403]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1165,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = sP0_iProver_split ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_0,c_416]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1397,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = sP0_iProver_split ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_190,c_1165]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2652,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1397,c_161]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_383,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2,c_378]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_472,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),sP0_iProver_split) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_383,c_1]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_27,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_39,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2,c_29]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_184,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_25,c_130]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_318,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_39,c_184]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_333,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_318,c_27]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_343,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_333,c_4,c_190]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_480,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) = k4_xboole_0(X0,X1) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_472,c_27,c_343]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2683,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_2652,c_480]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_405,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)),sP0_iProver_split) = X1 ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_378,c_108]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_54,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_0,c_27]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_410,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),sP0_iProver_split) = X0 ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_405,c_3,c_54]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_522,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(sP0_iProver_split,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_410,c_27]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_376,plain,
% 7.44/1.49      ( k2_xboole_0(sP0_iProver_split,X0) = X0 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_373,c_351]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_422,plain,
% 7.44/1.49      ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_365,c_373,c_376]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_536,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_522,c_4,c_415,c_422,c_480]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_779,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_536,c_27]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2173,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),sP0_iProver_split) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_383,c_779]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_197,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_3,c_190]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2014,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_0,c_197]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2227,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_2173,c_2014]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_468,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(sP0_iProver_split,X2) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_383,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_483,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = sP0_iProver_split ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_468,c_4,c_415]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3252,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(sP0_iProver_split,k2_xboole_0(X1,X0)),X2)) = sP0_iProver_split ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2227,c_483]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_93,plain,
% 7.44/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_4,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_102,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_93,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_385,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_29,c_378]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_400,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,sP0_iProver_split),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_378,c_108]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_411,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,sP0_iProver_split),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_400,c_3]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_425,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_422,c_411]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1271,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_385,c_425]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1007,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_385,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_43,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_29,c_29]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_474,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_383,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_199,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_25,c_190]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_477,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_474,c_199]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1009,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_1007,c_43,c_477]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_1315,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(light_normalisation,[status(thm)],[c_1271,c_1009]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2469,plain,
% 7.44/1.49      ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_1315,c_0]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_3382,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = sP0_iProver_split ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_3252,c_102,c_2469]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_12043,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = sP0_iProver_split ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2683,c_3382]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_19960,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),sP0_iProver_split),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_12043,c_161]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_91,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_25,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_104,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_91,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15301,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_104,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_15347,plain,
% 7.44/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_15301,c_425]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_20036,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_19960,c_2227,c_15347]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_805,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_536,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4165,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_29,c_805]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4277,plain,
% 7.44/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_4165,c_805]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_6,negated_conjecture,
% 7.44/1.49      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 7.44/1.49      inference(cnf_transformation,[],[f25]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_23,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_6,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_24,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_0,c_23]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_45,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_34,c_24]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_14425,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_4277,c_45]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2424,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2,c_1315]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2501,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_2424,c_1315]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_4209,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_805,c_2501]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2738,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sP0_iProver_split,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2227,c_4]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_2757,plain,
% 7.44/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_2738,c_376]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_11905,plain,
% 7.44/1.49      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_2757,c_2]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_14426,plain,
% 7.44/1.49      ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_14425,c_4209,c_11905]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_30746,plain,
% 7.44/1.49      ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) != k2_xboole_0(sK0,sK1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_20036,c_14426]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_30747,plain,
% 7.44/1.49      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 7.44/1.49      inference(demodulation,[status(thm)],[c_30746,c_2501]) ).
% 7.44/1.49  
% 7.44/1.49  cnf(c_31101,plain,
% 7.44/1.49      ( $false ),
% 7.44/1.49      inference(superposition,[status(thm)],[c_0,c_30747]) ).
% 7.44/1.49  
% 7.44/1.49  
% 7.44/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.44/1.49  
% 7.44/1.49  ------                               Statistics
% 7.44/1.49  
% 7.44/1.49  ------ General
% 7.44/1.49  
% 7.44/1.49  abstr_ref_over_cycles:                  0
% 7.44/1.49  abstr_ref_under_cycles:                 0
% 7.44/1.49  gc_basic_clause_elim:                   0
% 7.44/1.49  forced_gc_time:                         0
% 7.44/1.49  parsing_time:                           0.008
% 7.44/1.49  unif_index_cands_time:                  0.
% 7.44/1.49  unif_index_add_time:                    0.
% 7.44/1.49  orderings_time:                         0.
% 7.44/1.49  out_proof_time:                         0.008
% 7.44/1.49  total_time:                             0.857
% 7.44/1.49  num_of_symbols:                         36
% 7.44/1.49  num_of_terms:                           40539
% 7.44/1.49  
% 7.44/1.49  ------ Preprocessing
% 7.44/1.49  
% 7.44/1.49  num_of_splits:                          0
% 7.44/1.49  num_of_split_atoms:                     1
% 7.44/1.49  num_of_reused_defs:                     0
% 7.44/1.49  num_eq_ax_congr_red:                    0
% 7.44/1.49  num_of_sem_filtered_clauses:            0
% 7.44/1.49  num_of_subtypes:                        0
% 7.44/1.49  monotx_restored_types:                  0
% 7.44/1.49  sat_num_of_epr_types:                   0
% 7.44/1.49  sat_num_of_non_cyclic_types:            0
% 7.44/1.49  sat_guarded_non_collapsed_types:        0
% 7.44/1.49  num_pure_diseq_elim:                    0
% 7.44/1.49  simp_replaced_by:                       0
% 7.44/1.49  res_preprocessed:                       18
% 7.44/1.49  prep_upred:                             0
% 7.44/1.49  prep_unflattend:                        0
% 7.44/1.49  smt_new_axioms:                         0
% 7.44/1.49  pred_elim_cands:                        0
% 7.44/1.49  pred_elim:                              0
% 7.44/1.49  pred_elim_cl:                           0
% 7.44/1.49  pred_elim_cycles:                       0
% 7.44/1.49  merged_defs:                            0
% 7.44/1.49  merged_defs_ncl:                        0
% 7.44/1.49  bin_hyper_res:                          0
% 7.44/1.49  prep_cycles:                            2
% 7.44/1.49  pred_elim_time:                         0.
% 7.44/1.49  splitting_time:                         0.
% 7.44/1.49  sem_filter_time:                        0.
% 7.44/1.49  monotx_time:                            0.
% 7.44/1.49  subtype_inf_time:                       0.
% 7.44/1.49  
% 7.44/1.49  ------ Problem properties
% 7.44/1.49  
% 7.44/1.49  clauses:                                7
% 7.44/1.49  conjectures:                            1
% 7.44/1.49  epr:                                    0
% 7.44/1.49  horn:                                   7
% 7.44/1.49  ground:                                 1
% 7.44/1.49  unary:                                  7
% 7.44/1.49  binary:                                 0
% 7.44/1.49  lits:                                   7
% 7.44/1.49  lits_eq:                                7
% 7.44/1.49  fd_pure:                                0
% 7.44/1.49  fd_pseudo:                              0
% 7.44/1.49  fd_cond:                                0
% 7.44/1.49  fd_pseudo_cond:                         0
% 7.44/1.49  ac_symbols:                             0
% 7.44/1.49  
% 7.44/1.49  ------ Propositional Solver
% 7.44/1.49  
% 7.44/1.49  prop_solver_calls:                      13
% 7.44/1.49  prop_fast_solver_calls:                 48
% 7.44/1.49  smt_solver_calls:                       0
% 7.44/1.49  smt_fast_solver_calls:                  0
% 7.44/1.49  prop_num_of_clauses:                    269
% 7.44/1.49  prop_preprocess_simplified:             306
% 7.44/1.49  prop_fo_subsumed:                       0
% 7.44/1.49  prop_solver_time:                       0.
% 7.44/1.49  smt_solver_time:                        0.
% 7.44/1.49  smt_fast_solver_time:                   0.
% 7.44/1.49  prop_fast_solver_time:                  0.
% 7.44/1.49  prop_unsat_core_time:                   0.
% 7.44/1.49  
% 7.44/1.49  ------ QBF
% 7.44/1.49  
% 7.44/1.49  qbf_q_res:                              0
% 7.44/1.49  qbf_num_tautologies:                    0
% 7.44/1.49  qbf_prep_cycles:                        0
% 7.44/1.49  
% 7.44/1.49  ------ BMC1
% 7.44/1.49  
% 7.44/1.49  bmc1_current_bound:                     -1
% 7.44/1.49  bmc1_last_solved_bound:                 -1
% 7.44/1.49  bmc1_unsat_core_size:                   -1
% 7.44/1.49  bmc1_unsat_core_parents_size:           -1
% 7.44/1.49  bmc1_merge_next_fun:                    0
% 7.44/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.44/1.49  
% 7.44/1.49  ------ Instantiation
% 7.44/1.49  
% 7.44/1.49  inst_num_of_clauses:                    0
% 7.44/1.49  inst_num_in_passive:                    0
% 7.44/1.49  inst_num_in_active:                     0
% 7.44/1.49  inst_num_in_unprocessed:                0
% 7.44/1.49  inst_num_of_loops:                      0
% 7.44/1.49  inst_num_of_learning_restarts:          0
% 7.44/1.49  inst_num_moves_active_passive:          0
% 7.44/1.49  inst_lit_activity:                      0
% 7.44/1.49  inst_lit_activity_moves:                0
% 7.44/1.49  inst_num_tautologies:                   0
% 7.44/1.49  inst_num_prop_implied:                  0
% 7.44/1.49  inst_num_existing_simplified:           0
% 7.44/1.49  inst_num_eq_res_simplified:             0
% 7.44/1.49  inst_num_child_elim:                    0
% 7.44/1.49  inst_num_of_dismatching_blockings:      0
% 7.44/1.49  inst_num_of_non_proper_insts:           0
% 7.44/1.49  inst_num_of_duplicates:                 0
% 7.44/1.49  inst_inst_num_from_inst_to_res:         0
% 7.44/1.49  inst_dismatching_checking_time:         0.
% 7.44/1.49  
% 7.44/1.49  ------ Resolution
% 7.44/1.49  
% 7.44/1.49  res_num_of_clauses:                     0
% 7.44/1.49  res_num_in_passive:                     0
% 7.44/1.49  res_num_in_active:                      0
% 7.44/1.49  res_num_of_loops:                       20
% 7.44/1.49  res_forward_subset_subsumed:            0
% 7.44/1.49  res_backward_subset_subsumed:           0
% 7.44/1.49  res_forward_subsumed:                   0
% 7.44/1.49  res_backward_subsumed:                  0
% 7.44/1.49  res_forward_subsumption_resolution:     0
% 7.44/1.50  res_backward_subsumption_resolution:    0
% 7.44/1.50  res_clause_to_clause_subsumption:       69835
% 7.44/1.50  res_orphan_elimination:                 0
% 7.44/1.50  res_tautology_del:                      0
% 7.44/1.50  res_num_eq_res_simplified:              0
% 7.44/1.50  res_num_sel_changes:                    0
% 7.44/1.50  res_moves_from_active_to_pass:          0
% 7.44/1.50  
% 7.44/1.50  ------ Superposition
% 7.44/1.50  
% 7.44/1.50  sup_time_total:                         0.
% 7.44/1.50  sup_time_generating:                    0.
% 7.44/1.50  sup_time_sim_full:                      0.
% 7.44/1.50  sup_time_sim_immed:                     0.
% 7.44/1.50  
% 7.44/1.50  sup_num_of_clauses:                     2545
% 7.44/1.50  sup_num_in_active:                      143
% 7.44/1.50  sup_num_in_passive:                     2402
% 7.44/1.50  sup_num_of_loops:                       164
% 7.44/1.50  sup_fw_superposition:                   12499
% 7.44/1.50  sup_bw_superposition:                   9279
% 7.44/1.50  sup_immediate_simplified:               9737
% 7.44/1.50  sup_given_eliminated:                   3
% 7.44/1.50  comparisons_done:                       0
% 7.44/1.50  comparisons_avoided:                    0
% 7.44/1.50  
% 7.44/1.50  ------ Simplifications
% 7.44/1.50  
% 7.44/1.50  
% 7.44/1.50  sim_fw_subset_subsumed:                 0
% 7.44/1.50  sim_bw_subset_subsumed:                 0
% 7.44/1.50  sim_fw_subsumed:                        1681
% 7.44/1.50  sim_bw_subsumed:                        34
% 7.44/1.50  sim_fw_subsumption_res:                 0
% 7.44/1.50  sim_bw_subsumption_res:                 0
% 7.44/1.50  sim_tautology_del:                      0
% 7.44/1.50  sim_eq_tautology_del:                   2823
% 7.44/1.50  sim_eq_res_simp:                        0
% 7.44/1.50  sim_fw_demodulated:                     5356
% 7.44/1.50  sim_bw_demodulated:                     55
% 7.44/1.50  sim_light_normalised:                   3796
% 7.44/1.50  sim_joinable_taut:                      0
% 7.44/1.50  sim_joinable_simp:                      0
% 7.44/1.50  sim_ac_normalised:                      0
% 7.44/1.50  sim_smt_subsumption:                    0
% 7.44/1.50  
%------------------------------------------------------------------------------
