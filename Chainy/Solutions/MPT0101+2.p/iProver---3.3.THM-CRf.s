%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0101+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:21 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 561 expanded)
%              Number of clauses        :   71 ( 196 expanded)
%              Number of leaves         :   22 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 562 expanded)
%              Number of equality atoms :  128 ( 561 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f432,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f93])).

fof(f88,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f427,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

fof(f549,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f432,f427])).

fof(f91,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f430,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f91])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f304,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f86,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f425,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f309,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f544,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f425,f309])).

fof(f94,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f433,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

fof(f550,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f433,f427])).

fof(f81,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f420,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f81])).

fof(f54,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f390,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f54])).

fof(f522,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f390,f309])).

fof(f77,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f416,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

fof(f144,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f145,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f144])).

fof(f244,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f145])).

fof(f300,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK15,sK16) != k5_xboole_0(k5_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK16)) ),
    introduced(choice_axiom,[])).

fof(f301,plain,(
    k2_xboole_0(sK15,sK16) != k5_xboole_0(k5_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f244,f300])).

fof(f487,plain,(
    k2_xboole_0(sK15,sK16) != k5_xboole_0(k5_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f301])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f331,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f572,plain,(
    k2_xboole_0(sK15,sK16) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)))) ),
    inference(definition_unfolding,[],[f487,f331,f331,f427])).

fof(f115,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f455,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f115])).

fof(f97,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f436,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f97])).

fof(f553,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f436,f427])).

fof(f143,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f486,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f143])).

fof(f571,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f486,f331,f427])).

fof(f80,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f419,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f80])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f305,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f489,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f305,f427,f427])).

fof(f78,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f417,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f78])).

fof(f542,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f417,f309])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f398,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f529,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f398,f427,f427])).

fof(f90,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f429,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f90])).

fof(f547,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f429,f309,f309])).

fof(f82,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f421,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_127,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f549])).

cnf(c_125,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f430])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f304])).

cnf(c_2886,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_127,c_125,c_2])).

cnf(c_121,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f544])).

cnf(c_10984,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2886,c_121])).

cnf(c_128,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f550])).

cnf(c_13793,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),o_0_0_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10984,c_128])).

cnf(c_116,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f420])).

cnf(c_13828,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,X1),o_0_0_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_13793,c_116])).

cnf(c_13829,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,o_0_0_xboole_0))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(demodulation,[status(thm)],[c_13828,c_116])).

cnf(c_86,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f522])).

cnf(c_112,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f416])).

cnf(c_10985,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_2886,c_112])).

cnf(c_12246,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_116,c_10985])).

cnf(c_13830,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13829,c_86,c_12246])).

cnf(c_182,negated_conjecture,
    ( k2_xboole_0(sK15,sK16) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)))) ),
    inference(cnf_transformation,[],[f572])).

cnf(c_2877,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) != k2_xboole_0(sK15,sK16) ),
    inference(theory_normalisation,[status(thm)],[c_182,c_125,c_2])).

cnf(c_5439,plain,
    ( k2_xboole_0(k4_xboole_0(sK15,k2_xboole_0(k4_xboole_0(sK15,sK16),k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) != k2_xboole_0(sK15,sK16) ),
    inference(demodulation,[status(thm)],[c_2877,c_116])).

cnf(c_150,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f455])).

cnf(c_5440,plain,
    ( k2_xboole_0(k4_xboole_0(sK15,k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) != k2_xboole_0(sK15,sK16) ),
    inference(demodulation,[status(thm)],[c_5439,c_150])).

cnf(c_40357,plain,
    ( k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) != k2_xboole_0(sK15,sK16) ),
    inference(demodulation,[status(thm)],[c_13830,c_5440])).

cnf(c_131,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f553])).

cnf(c_2885,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_131,c_125,c_2])).

cnf(c_181,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f571])).

cnf(c_2878,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(X1,X0) ),
    inference(theory_normalisation,[status(thm)],[c_181,c_125,c_2])).

cnf(c_5433,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2878,c_2886])).

cnf(c_115,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f419])).

cnf(c_8844,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_115,c_112])).

cnf(c_8865,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8844,c_112])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f489])).

cnf(c_9048,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_115,c_3])).

cnf(c_113,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f542])).

cnf(c_7559,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_121])).

cnf(c_9094,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_9048,c_113,c_7559])).

cnf(c_15302,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8865,c_9094])).

cnf(c_15403,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),o_0_0_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_15302,c_7559])).

cnf(c_21994,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_5433,c_15403])).

cnf(c_22121,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_21994,c_15403])).

cnf(c_26218,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2885,c_22121])).

cnf(c_8759,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2885,c_112])).

cnf(c_7608,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_121,c_112])).

cnf(c_7610,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7608,c_86])).

cnf(c_94,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f529])).

cnf(c_8838,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_115])).

cnf(c_12808,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_8838,c_116])).

cnf(c_12838,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_12808,c_116])).

cnf(c_16346,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_94,c_94,c_12838])).

cnf(c_16366,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_7610,c_16346])).

cnf(c_16514,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2)))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(light_normalisation,[status(thm)],[c_16366,c_125])).

cnf(c_16515,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_16514,c_121,c_15403])).

cnf(c_26332,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_26218,c_8759,c_16515])).

cnf(c_11014,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(o_0_0_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_7559,c_116])).

cnf(c_124,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f547])).

cnf(c_11062,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11014,c_124])).

cnf(c_12599,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_3,c_5433])).

cnf(c_12638,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_12599,c_10985])).

cnf(c_33806,plain,
    ( k2_xboole_0(k4_xboole_0(X0,o_0_0_xboole_0),k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_11062,c_12638])).

cnf(c_117,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f421])).

cnf(c_13656,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_8838,c_117])).

cnf(c_13685,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_117,c_2])).

cnf(c_13718,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X0) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_13656,c_13685])).

cnf(c_13719,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_13718,c_125])).

cnf(c_12240,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_3,c_10985])).

cnf(c_19474,plain,
    ( k2_xboole_0(k4_xboole_0(X0,o_0_0_xboole_0),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_11062,c_12240])).

cnf(c_14906,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8865,c_125])).

cnf(c_14922,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_14906,c_125])).

cnf(c_19528,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_19474,c_113,c_14922])).

cnf(c_34017,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_33806,c_113,c_13719,c_19528])).

cnf(c_40358,plain,
    ( k2_xboole_0(sK16,sK15) != k2_xboole_0(sK15,sK16) ),
    inference(demodulation,[status(thm)],[c_40357,c_26332,c_34017])).

cnf(c_40641,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_40358])).

%------------------------------------------------------------------------------
