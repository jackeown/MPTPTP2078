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
% DateTime   : Thu Dec  3 11:24:55 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  139 (16170 expanded)
%              Number of clauses        :  108 (6880 expanded)
%              Number of leaves         :   12 (4279 expanded)
%              Depth                    :   28
%              Number of atoms          :  140 (16171 expanded)
%              Number of equality atoms :  139 (16170 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f23,f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f18,f23])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_31,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_32,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_31,c_3])).

cnf(c_34,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_32])).

cnf(c_41,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_34,c_4])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_100,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_179,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_41,c_100])).

cnf(c_198,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_179,c_6])).

cnf(c_201,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_198,c_41])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_238,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_201,c_5])).

cnf(c_244,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_238,c_198])).

cnf(c_372,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_244])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_222,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_198,c_2])).

cnf(c_226,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_222,c_3])).

cnf(c_250,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_226])).

cnf(c_489,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_372,c_250])).

cnf(c_499,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_489,c_3])).

cnf(c_763,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_499,c_0])).

cnf(c_29,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_259,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_226,c_29])).

cnf(c_261,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_259,c_201])).

cnf(c_419,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_261,c_5])).

cnf(c_435,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_419,c_5,c_198])).

cnf(c_719,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_435,c_5])).

cnf(c_737,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_719,c_5,c_198])).

cnf(c_6774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_763,c_737])).

cnf(c_56,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_458,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_372,c_7])).

cnf(c_464,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_458,c_3])).

cnf(c_619,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_56,c_3,c_372,c_464])).

cnf(c_653,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_619,c_6])).

cnf(c_663,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_653,c_4])).

cnf(c_487,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_244,c_250])).

cnf(c_501,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_487,c_3])).

cnf(c_773,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_501])).

cnf(c_1513,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_663,c_773])).

cnf(c_1550,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1513,c_773])).

cnf(c_21074,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6774,c_1550])).

cnf(c_386,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_244,c_5])).

cnf(c_72,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_81,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_72,c_5])).

cnf(c_395,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_386,c_81,c_198])).

cnf(c_514,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_395])).

cnf(c_482,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_250])).

cnf(c_505,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_482,c_5])).

cnf(c_414,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_261,c_7])).

cnf(c_439,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_414,c_5])).

cnf(c_440,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_439,c_5,c_34])).

cnf(c_506,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_505,c_440])).

cnf(c_5598,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X3,k1_xboole_0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_514,c_506])).

cnf(c_5671,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_5598,c_32])).

cnf(c_751,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_499])).

cnf(c_1431,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_751,c_395])).

cnf(c_721,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_435,c_250])).

cnf(c_735,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_721,c_5])).

cnf(c_736,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_735,c_32])).

cnf(c_7392,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_736])).

cnf(c_20077,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_1431,c_7392])).

cnf(c_1150,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_663,c_0])).

cnf(c_1751,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_372,c_1150])).

cnf(c_1423,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_499,c_751])).

cnf(c_1425,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_501,c_751])).

cnf(c_1438,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_751,c_0])).

cnf(c_1454,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1425,c_1438])).

cnf(c_1455,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1423,c_1454])).

cnf(c_1795,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1751,c_1455])).

cnf(c_69,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_29,c_5])).

cnf(c_82,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_69,c_5])).

cnf(c_256,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_29,c_226])).

cnf(c_4172,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_256])).

cnf(c_17404,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_82,c_4172])).

cnf(c_9955,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_82,c_1150])).

cnf(c_9999,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_9955,c_1550])).

cnf(c_17620,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_17404,c_9999])).

cnf(c_254,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_226])).

cnf(c_3838,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_254])).

cnf(c_17621,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_17620,c_3838,c_9999])).

cnf(c_20236,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_20077,c_1795,c_17621])).

cnf(c_21138,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_21074,c_5671,c_20236])).

cnf(c_8,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_27,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_27270,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_21138,c_27])).

cnf(c_1144,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_663,c_29])).

cnf(c_1163,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1144,c_619])).

cnf(c_1220,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1163,c_7])).

cnf(c_1228,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1220,c_201])).

cnf(c_1229,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1228,c_32])).

cnf(c_11166,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_1229,c_663])).

cnf(c_27271,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_27270,c_7,c_11166])).

cnf(c_699,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_435])).

cnf(c_1366,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_699,c_663])).

cnf(c_1405,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1366,c_34])).

cnf(c_17375,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1405,c_4172])).

cnf(c_17665,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_17375,c_17621])).

cnf(c_9952,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_82,c_1550])).

cnf(c_10003,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_9952,c_9999])).

cnf(c_17666,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_17665,c_699,c_1795,c_10003])).

cnf(c_25642,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_663,c_17666])).

cnf(c_25896,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_25642,c_17666])).

cnf(c_27272,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_27271,c_25896])).

cnf(c_28670,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_27272])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.67/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.50  
% 7.67/1.50  ------  iProver source info
% 7.67/1.50  
% 7.67/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.50  git: non_committed_changes: false
% 7.67/1.50  git: last_make_outside_of_git: false
% 7.67/1.50  
% 7.67/1.50  ------ 
% 7.67/1.50  
% 7.67/1.50  ------ Input Options
% 7.67/1.50  
% 7.67/1.50  --out_options                           all
% 7.67/1.50  --tptp_safe_out                         true
% 7.67/1.50  --problem_path                          ""
% 7.67/1.50  --include_path                          ""
% 7.67/1.50  --clausifier                            res/vclausify_rel
% 7.67/1.50  --clausifier_options                    --mode clausify
% 7.67/1.50  --stdin                                 false
% 7.67/1.50  --stats_out                             all
% 7.67/1.50  
% 7.67/1.50  ------ General Options
% 7.67/1.50  
% 7.67/1.50  --fof                                   false
% 7.67/1.50  --time_out_real                         305.
% 7.67/1.50  --time_out_virtual                      -1.
% 7.67/1.50  --symbol_type_check                     false
% 7.67/1.50  --clausify_out                          false
% 7.67/1.50  --sig_cnt_out                           false
% 7.67/1.50  --trig_cnt_out                          false
% 7.67/1.50  --trig_cnt_out_tolerance                1.
% 7.67/1.50  --trig_cnt_out_sk_spl                   false
% 7.67/1.50  --abstr_cl_out                          false
% 7.67/1.50  
% 7.67/1.50  ------ Global Options
% 7.67/1.50  
% 7.67/1.50  --schedule                              default
% 7.67/1.50  --add_important_lit                     false
% 7.67/1.50  --prop_solver_per_cl                    1000
% 7.67/1.50  --min_unsat_core                        false
% 7.67/1.50  --soft_assumptions                      false
% 7.67/1.50  --soft_lemma_size                       3
% 7.67/1.50  --prop_impl_unit_size                   0
% 7.67/1.50  --prop_impl_unit                        []
% 7.67/1.50  --share_sel_clauses                     true
% 7.67/1.50  --reset_solvers                         false
% 7.67/1.50  --bc_imp_inh                            [conj_cone]
% 7.67/1.50  --conj_cone_tolerance                   3.
% 7.67/1.50  --extra_neg_conj                        none
% 7.67/1.50  --large_theory_mode                     true
% 7.67/1.50  --prolific_symb_bound                   200
% 7.67/1.50  --lt_threshold                          2000
% 7.67/1.50  --clause_weak_htbl                      true
% 7.67/1.50  --gc_record_bc_elim                     false
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing Options
% 7.67/1.50  
% 7.67/1.50  --preprocessing_flag                    true
% 7.67/1.50  --time_out_prep_mult                    0.1
% 7.67/1.50  --splitting_mode                        input
% 7.67/1.50  --splitting_grd                         true
% 7.67/1.50  --splitting_cvd                         false
% 7.67/1.50  --splitting_cvd_svl                     false
% 7.67/1.50  --splitting_nvd                         32
% 7.67/1.50  --sub_typing                            true
% 7.67/1.50  --prep_gs_sim                           true
% 7.67/1.50  --prep_unflatten                        true
% 7.67/1.50  --prep_res_sim                          true
% 7.67/1.50  --prep_upred                            true
% 7.67/1.50  --prep_sem_filter                       exhaustive
% 7.67/1.50  --prep_sem_filter_out                   false
% 7.67/1.50  --pred_elim                             true
% 7.67/1.50  --res_sim_input                         true
% 7.67/1.50  --eq_ax_congr_red                       true
% 7.67/1.50  --pure_diseq_elim                       true
% 7.67/1.50  --brand_transform                       false
% 7.67/1.50  --non_eq_to_eq                          false
% 7.67/1.50  --prep_def_merge                        true
% 7.67/1.50  --prep_def_merge_prop_impl              false
% 7.67/1.50  --prep_def_merge_mbd                    true
% 7.67/1.50  --prep_def_merge_tr_red                 false
% 7.67/1.50  --prep_def_merge_tr_cl                  false
% 7.67/1.50  --smt_preprocessing                     true
% 7.67/1.50  --smt_ac_axioms                         fast
% 7.67/1.50  --preprocessed_out                      false
% 7.67/1.50  --preprocessed_stats                    false
% 7.67/1.50  
% 7.67/1.50  ------ Abstraction refinement Options
% 7.67/1.50  
% 7.67/1.50  --abstr_ref                             []
% 7.67/1.50  --abstr_ref_prep                        false
% 7.67/1.50  --abstr_ref_until_sat                   false
% 7.67/1.50  --abstr_ref_sig_restrict                funpre
% 7.67/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.50  --abstr_ref_under                       []
% 7.67/1.50  
% 7.67/1.50  ------ SAT Options
% 7.67/1.50  
% 7.67/1.50  --sat_mode                              false
% 7.67/1.50  --sat_fm_restart_options                ""
% 7.67/1.50  --sat_gr_def                            false
% 7.67/1.50  --sat_epr_types                         true
% 7.67/1.50  --sat_non_cyclic_types                  false
% 7.67/1.50  --sat_finite_models                     false
% 7.67/1.50  --sat_fm_lemmas                         false
% 7.67/1.50  --sat_fm_prep                           false
% 7.67/1.50  --sat_fm_uc_incr                        true
% 7.67/1.50  --sat_out_model                         small
% 7.67/1.50  --sat_out_clauses                       false
% 7.67/1.50  
% 7.67/1.50  ------ QBF Options
% 7.67/1.50  
% 7.67/1.50  --qbf_mode                              false
% 7.67/1.50  --qbf_elim_univ                         false
% 7.67/1.50  --qbf_dom_inst                          none
% 7.67/1.50  --qbf_dom_pre_inst                      false
% 7.67/1.50  --qbf_sk_in                             false
% 7.67/1.50  --qbf_pred_elim                         true
% 7.67/1.50  --qbf_split                             512
% 7.67/1.50  
% 7.67/1.50  ------ BMC1 Options
% 7.67/1.50  
% 7.67/1.50  --bmc1_incremental                      false
% 7.67/1.50  --bmc1_axioms                           reachable_all
% 7.67/1.50  --bmc1_min_bound                        0
% 7.67/1.50  --bmc1_max_bound                        -1
% 7.67/1.50  --bmc1_max_bound_default                -1
% 7.67/1.50  --bmc1_symbol_reachability              true
% 7.67/1.50  --bmc1_property_lemmas                  false
% 7.67/1.50  --bmc1_k_induction                      false
% 7.67/1.50  --bmc1_non_equiv_states                 false
% 7.67/1.50  --bmc1_deadlock                         false
% 7.67/1.50  --bmc1_ucm                              false
% 7.67/1.50  --bmc1_add_unsat_core                   none
% 7.67/1.50  --bmc1_unsat_core_children              false
% 7.67/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.50  --bmc1_out_stat                         full
% 7.67/1.50  --bmc1_ground_init                      false
% 7.67/1.50  --bmc1_pre_inst_next_state              false
% 7.67/1.50  --bmc1_pre_inst_state                   false
% 7.67/1.50  --bmc1_pre_inst_reach_state             false
% 7.67/1.50  --bmc1_out_unsat_core                   false
% 7.67/1.50  --bmc1_aig_witness_out                  false
% 7.67/1.50  --bmc1_verbose                          false
% 7.67/1.50  --bmc1_dump_clauses_tptp                false
% 7.67/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.50  --bmc1_dump_file                        -
% 7.67/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.50  --bmc1_ucm_extend_mode                  1
% 7.67/1.50  --bmc1_ucm_init_mode                    2
% 7.67/1.50  --bmc1_ucm_cone_mode                    none
% 7.67/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.50  --bmc1_ucm_relax_model                  4
% 7.67/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.50  --bmc1_ucm_layered_model                none
% 7.67/1.50  --bmc1_ucm_max_lemma_size               10
% 7.67/1.50  
% 7.67/1.50  ------ AIG Options
% 7.67/1.50  
% 7.67/1.50  --aig_mode                              false
% 7.67/1.50  
% 7.67/1.50  ------ Instantiation Options
% 7.67/1.50  
% 7.67/1.50  --instantiation_flag                    true
% 7.67/1.50  --inst_sos_flag                         false
% 7.67/1.50  --inst_sos_phase                        true
% 7.67/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel_side                     num_symb
% 7.67/1.50  --inst_solver_per_active                1400
% 7.67/1.50  --inst_solver_calls_frac                1.
% 7.67/1.50  --inst_passive_queue_type               priority_queues
% 7.67/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.50  --inst_passive_queues_freq              [25;2]
% 7.67/1.50  --inst_dismatching                      true
% 7.67/1.50  --inst_eager_unprocessed_to_passive     true
% 7.67/1.50  --inst_prop_sim_given                   true
% 7.67/1.50  --inst_prop_sim_new                     false
% 7.67/1.50  --inst_subs_new                         false
% 7.67/1.50  --inst_eq_res_simp                      false
% 7.67/1.50  --inst_subs_given                       false
% 7.67/1.50  --inst_orphan_elimination               true
% 7.67/1.50  --inst_learning_loop_flag               true
% 7.67/1.50  --inst_learning_start                   3000
% 7.67/1.50  --inst_learning_factor                  2
% 7.67/1.50  --inst_start_prop_sim_after_learn       3
% 7.67/1.50  --inst_sel_renew                        solver
% 7.67/1.50  --inst_lit_activity_flag                true
% 7.67/1.50  --inst_restr_to_given                   false
% 7.67/1.50  --inst_activity_threshold               500
% 7.67/1.50  --inst_out_proof                        true
% 7.67/1.50  
% 7.67/1.50  ------ Resolution Options
% 7.67/1.50  
% 7.67/1.50  --resolution_flag                       true
% 7.67/1.50  --res_lit_sel                           adaptive
% 7.67/1.50  --res_lit_sel_side                      none
% 7.67/1.50  --res_ordering                          kbo
% 7.67/1.50  --res_to_prop_solver                    active
% 7.67/1.50  --res_prop_simpl_new                    false
% 7.67/1.50  --res_prop_simpl_given                  true
% 7.67/1.50  --res_passive_queue_type                priority_queues
% 7.67/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.50  --res_passive_queues_freq               [15;5]
% 7.67/1.50  --res_forward_subs                      full
% 7.67/1.50  --res_backward_subs                     full
% 7.67/1.50  --res_forward_subs_resolution           true
% 7.67/1.50  --res_backward_subs_resolution          true
% 7.67/1.50  --res_orphan_elimination                true
% 7.67/1.50  --res_time_limit                        2.
% 7.67/1.50  --res_out_proof                         true
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Options
% 7.67/1.50  
% 7.67/1.50  --superposition_flag                    true
% 7.67/1.50  --sup_passive_queue_type                priority_queues
% 7.67/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.50  --demod_completeness_check              fast
% 7.67/1.50  --demod_use_ground                      true
% 7.67/1.50  --sup_to_prop_solver                    passive
% 7.67/1.50  --sup_prop_simpl_new                    true
% 7.67/1.50  --sup_prop_simpl_given                  true
% 7.67/1.50  --sup_fun_splitting                     false
% 7.67/1.50  --sup_smt_interval                      50000
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Simplification Setup
% 7.67/1.50  
% 7.67/1.50  --sup_indices_passive                   []
% 7.67/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.50  --sup_full_bw                           [BwDemod]
% 7.67/1.50  --sup_immed_triv                        [TrivRules]
% 7.67/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.50  --sup_immed_bw_main                     []
% 7.67/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.50  
% 7.67/1.50  ------ Combination Options
% 7.67/1.50  
% 7.67/1.50  --comb_res_mult                         3
% 7.67/1.50  --comb_sup_mult                         2
% 7.67/1.50  --comb_inst_mult                        10
% 7.67/1.50  
% 7.67/1.50  ------ Debug Options
% 7.67/1.50  
% 7.67/1.50  --dbg_backtrace                         false
% 7.67/1.50  --dbg_dump_prop_clauses                 false
% 7.67/1.50  --dbg_dump_prop_clauses_file            -
% 7.67/1.50  --dbg_out_stat                          false
% 7.67/1.50  ------ Parsing...
% 7.67/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.50  ------ Proving...
% 7.67/1.50  ------ Problem Properties 
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  clauses                                 9
% 7.67/1.50  conjectures                             1
% 7.67/1.50  EPR                                     0
% 7.67/1.50  Horn                                    9
% 7.67/1.50  unary                                   9
% 7.67/1.50  binary                                  0
% 7.67/1.50  lits                                    9
% 7.67/1.50  lits eq                                 9
% 7.67/1.50  fd_pure                                 0
% 7.67/1.50  fd_pseudo                               0
% 7.67/1.50  fd_cond                                 0
% 7.67/1.50  fd_pseudo_cond                          0
% 7.67/1.50  AC symbols                              0
% 7.67/1.50  
% 7.67/1.50  ------ Schedule UEQ
% 7.67/1.50  
% 7.67/1.50  ------ pure equality problem: resolution off 
% 7.67/1.50  
% 7.67/1.50  ------ Option_UEQ Time Limit: Unbounded
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  ------ 
% 7.67/1.50  Current options:
% 7.67/1.50  ------ 
% 7.67/1.50  
% 7.67/1.50  ------ Input Options
% 7.67/1.50  
% 7.67/1.50  --out_options                           all
% 7.67/1.50  --tptp_safe_out                         true
% 7.67/1.50  --problem_path                          ""
% 7.67/1.50  --include_path                          ""
% 7.67/1.50  --clausifier                            res/vclausify_rel
% 7.67/1.50  --clausifier_options                    --mode clausify
% 7.67/1.50  --stdin                                 false
% 7.67/1.50  --stats_out                             all
% 7.67/1.50  
% 7.67/1.50  ------ General Options
% 7.67/1.50  
% 7.67/1.50  --fof                                   false
% 7.67/1.50  --time_out_real                         305.
% 7.67/1.50  --time_out_virtual                      -1.
% 7.67/1.50  --symbol_type_check                     false
% 7.67/1.50  --clausify_out                          false
% 7.67/1.50  --sig_cnt_out                           false
% 7.67/1.50  --trig_cnt_out                          false
% 7.67/1.50  --trig_cnt_out_tolerance                1.
% 7.67/1.50  --trig_cnt_out_sk_spl                   false
% 7.67/1.50  --abstr_cl_out                          false
% 7.67/1.50  
% 7.67/1.50  ------ Global Options
% 7.67/1.50  
% 7.67/1.50  --schedule                              default
% 7.67/1.50  --add_important_lit                     false
% 7.67/1.50  --prop_solver_per_cl                    1000
% 7.67/1.50  --min_unsat_core                        false
% 7.67/1.50  --soft_assumptions                      false
% 7.67/1.50  --soft_lemma_size                       3
% 7.67/1.50  --prop_impl_unit_size                   0
% 7.67/1.50  --prop_impl_unit                        []
% 7.67/1.50  --share_sel_clauses                     true
% 7.67/1.50  --reset_solvers                         false
% 7.67/1.50  --bc_imp_inh                            [conj_cone]
% 7.67/1.50  --conj_cone_tolerance                   3.
% 7.67/1.50  --extra_neg_conj                        none
% 7.67/1.50  --large_theory_mode                     true
% 7.67/1.50  --prolific_symb_bound                   200
% 7.67/1.50  --lt_threshold                          2000
% 7.67/1.50  --clause_weak_htbl                      true
% 7.67/1.50  --gc_record_bc_elim                     false
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing Options
% 7.67/1.50  
% 7.67/1.50  --preprocessing_flag                    true
% 7.67/1.50  --time_out_prep_mult                    0.1
% 7.67/1.50  --splitting_mode                        input
% 7.67/1.50  --splitting_grd                         true
% 7.67/1.50  --splitting_cvd                         false
% 7.67/1.50  --splitting_cvd_svl                     false
% 7.67/1.50  --splitting_nvd                         32
% 7.67/1.50  --sub_typing                            true
% 7.67/1.50  --prep_gs_sim                           true
% 7.67/1.50  --prep_unflatten                        true
% 7.67/1.50  --prep_res_sim                          true
% 7.67/1.50  --prep_upred                            true
% 7.67/1.50  --prep_sem_filter                       exhaustive
% 7.67/1.50  --prep_sem_filter_out                   false
% 7.67/1.50  --pred_elim                             true
% 7.67/1.50  --res_sim_input                         true
% 7.67/1.50  --eq_ax_congr_red                       true
% 7.67/1.50  --pure_diseq_elim                       true
% 7.67/1.50  --brand_transform                       false
% 7.67/1.50  --non_eq_to_eq                          false
% 7.67/1.50  --prep_def_merge                        true
% 7.67/1.50  --prep_def_merge_prop_impl              false
% 7.67/1.50  --prep_def_merge_mbd                    true
% 7.67/1.50  --prep_def_merge_tr_red                 false
% 7.67/1.50  --prep_def_merge_tr_cl                  false
% 7.67/1.50  --smt_preprocessing                     true
% 7.67/1.50  --smt_ac_axioms                         fast
% 7.67/1.50  --preprocessed_out                      false
% 7.67/1.50  --preprocessed_stats                    false
% 7.67/1.50  
% 7.67/1.50  ------ Abstraction refinement Options
% 7.67/1.50  
% 7.67/1.50  --abstr_ref                             []
% 7.67/1.50  --abstr_ref_prep                        false
% 7.67/1.50  --abstr_ref_until_sat                   false
% 7.67/1.50  --abstr_ref_sig_restrict                funpre
% 7.67/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.50  --abstr_ref_under                       []
% 7.67/1.50  
% 7.67/1.50  ------ SAT Options
% 7.67/1.50  
% 7.67/1.50  --sat_mode                              false
% 7.67/1.50  --sat_fm_restart_options                ""
% 7.67/1.50  --sat_gr_def                            false
% 7.67/1.50  --sat_epr_types                         true
% 7.67/1.50  --sat_non_cyclic_types                  false
% 7.67/1.50  --sat_finite_models                     false
% 7.67/1.50  --sat_fm_lemmas                         false
% 7.67/1.50  --sat_fm_prep                           false
% 7.67/1.50  --sat_fm_uc_incr                        true
% 7.67/1.50  --sat_out_model                         small
% 7.67/1.50  --sat_out_clauses                       false
% 7.67/1.50  
% 7.67/1.50  ------ QBF Options
% 7.67/1.50  
% 7.67/1.50  --qbf_mode                              false
% 7.67/1.50  --qbf_elim_univ                         false
% 7.67/1.50  --qbf_dom_inst                          none
% 7.67/1.50  --qbf_dom_pre_inst                      false
% 7.67/1.50  --qbf_sk_in                             false
% 7.67/1.50  --qbf_pred_elim                         true
% 7.67/1.50  --qbf_split                             512
% 7.67/1.50  
% 7.67/1.50  ------ BMC1 Options
% 7.67/1.50  
% 7.67/1.50  --bmc1_incremental                      false
% 7.67/1.50  --bmc1_axioms                           reachable_all
% 7.67/1.50  --bmc1_min_bound                        0
% 7.67/1.50  --bmc1_max_bound                        -1
% 7.67/1.50  --bmc1_max_bound_default                -1
% 7.67/1.50  --bmc1_symbol_reachability              true
% 7.67/1.50  --bmc1_property_lemmas                  false
% 7.67/1.50  --bmc1_k_induction                      false
% 7.67/1.50  --bmc1_non_equiv_states                 false
% 7.67/1.50  --bmc1_deadlock                         false
% 7.67/1.50  --bmc1_ucm                              false
% 7.67/1.50  --bmc1_add_unsat_core                   none
% 7.67/1.50  --bmc1_unsat_core_children              false
% 7.67/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.50  --bmc1_out_stat                         full
% 7.67/1.50  --bmc1_ground_init                      false
% 7.67/1.50  --bmc1_pre_inst_next_state              false
% 7.67/1.50  --bmc1_pre_inst_state                   false
% 7.67/1.50  --bmc1_pre_inst_reach_state             false
% 7.67/1.50  --bmc1_out_unsat_core                   false
% 7.67/1.50  --bmc1_aig_witness_out                  false
% 7.67/1.50  --bmc1_verbose                          false
% 7.67/1.50  --bmc1_dump_clauses_tptp                false
% 7.67/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.50  --bmc1_dump_file                        -
% 7.67/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.50  --bmc1_ucm_extend_mode                  1
% 7.67/1.50  --bmc1_ucm_init_mode                    2
% 7.67/1.50  --bmc1_ucm_cone_mode                    none
% 7.67/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.50  --bmc1_ucm_relax_model                  4
% 7.67/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.50  --bmc1_ucm_layered_model                none
% 7.67/1.50  --bmc1_ucm_max_lemma_size               10
% 7.67/1.50  
% 7.67/1.50  ------ AIG Options
% 7.67/1.50  
% 7.67/1.50  --aig_mode                              false
% 7.67/1.50  
% 7.67/1.50  ------ Instantiation Options
% 7.67/1.50  
% 7.67/1.50  --instantiation_flag                    false
% 7.67/1.50  --inst_sos_flag                         false
% 7.67/1.50  --inst_sos_phase                        true
% 7.67/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.50  --inst_lit_sel_side                     num_symb
% 7.67/1.50  --inst_solver_per_active                1400
% 7.67/1.50  --inst_solver_calls_frac                1.
% 7.67/1.50  --inst_passive_queue_type               priority_queues
% 7.67/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.50  --inst_passive_queues_freq              [25;2]
% 7.67/1.50  --inst_dismatching                      true
% 7.67/1.50  --inst_eager_unprocessed_to_passive     true
% 7.67/1.50  --inst_prop_sim_given                   true
% 7.67/1.50  --inst_prop_sim_new                     false
% 7.67/1.50  --inst_subs_new                         false
% 7.67/1.50  --inst_eq_res_simp                      false
% 7.67/1.50  --inst_subs_given                       false
% 7.67/1.50  --inst_orphan_elimination               true
% 7.67/1.50  --inst_learning_loop_flag               true
% 7.67/1.50  --inst_learning_start                   3000
% 7.67/1.50  --inst_learning_factor                  2
% 7.67/1.50  --inst_start_prop_sim_after_learn       3
% 7.67/1.50  --inst_sel_renew                        solver
% 7.67/1.50  --inst_lit_activity_flag                true
% 7.67/1.50  --inst_restr_to_given                   false
% 7.67/1.50  --inst_activity_threshold               500
% 7.67/1.50  --inst_out_proof                        true
% 7.67/1.50  
% 7.67/1.50  ------ Resolution Options
% 7.67/1.50  
% 7.67/1.50  --resolution_flag                       false
% 7.67/1.50  --res_lit_sel                           adaptive
% 7.67/1.50  --res_lit_sel_side                      none
% 7.67/1.50  --res_ordering                          kbo
% 7.67/1.50  --res_to_prop_solver                    active
% 7.67/1.50  --res_prop_simpl_new                    false
% 7.67/1.50  --res_prop_simpl_given                  true
% 7.67/1.50  --res_passive_queue_type                priority_queues
% 7.67/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.50  --res_passive_queues_freq               [15;5]
% 7.67/1.50  --res_forward_subs                      full
% 7.67/1.50  --res_backward_subs                     full
% 7.67/1.50  --res_forward_subs_resolution           true
% 7.67/1.50  --res_backward_subs_resolution          true
% 7.67/1.50  --res_orphan_elimination                true
% 7.67/1.50  --res_time_limit                        2.
% 7.67/1.50  --res_out_proof                         true
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Options
% 7.67/1.50  
% 7.67/1.50  --superposition_flag                    true
% 7.67/1.50  --sup_passive_queue_type                priority_queues
% 7.67/1.50  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.50  --demod_completeness_check              fast
% 7.67/1.50  --demod_use_ground                      true
% 7.67/1.50  --sup_to_prop_solver                    active
% 7.67/1.50  --sup_prop_simpl_new                    false
% 7.67/1.50  --sup_prop_simpl_given                  false
% 7.67/1.50  --sup_fun_splitting                     true
% 7.67/1.50  --sup_smt_interval                      10000
% 7.67/1.50  
% 7.67/1.50  ------ Superposition Simplification Setup
% 7.67/1.50  
% 7.67/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.50  --sup_full_triv                         [TrivRules]
% 7.67/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.50  --sup_immed_triv                        [TrivRules]
% 7.67/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_immed_bw_main                     []
% 7.67/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.50  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.67/1.50  
% 7.67/1.50  ------ Combination Options
% 7.67/1.50  
% 7.67/1.50  --comb_res_mult                         1
% 7.67/1.50  --comb_sup_mult                         1
% 7.67/1.50  --comb_inst_mult                        1000000
% 7.67/1.50  
% 7.67/1.50  ------ Debug Options
% 7.67/1.50  
% 7.67/1.50  --dbg_backtrace                         false
% 7.67/1.50  --dbg_dump_prop_clauses                 false
% 7.67/1.50  --dbg_dump_prop_clauses_file            -
% 7.67/1.50  --dbg_out_stat                          false
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  ------ Proving...
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  % SZS status Theorem for theBenchmark.p
% 7.67/1.50  
% 7.67/1.50   Resolution empty clause
% 7.67/1.50  
% 7.67/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  fof(f1,axiom,(
% 7.67/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f16,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f1])).
% 7.67/1.50  
% 7.67/1.50  fof(f6,axiom,(
% 7.67/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f21,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f6])).
% 7.67/1.50  
% 7.67/1.50  fof(f5,axiom,(
% 7.67/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f20,plain,(
% 7.67/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.67/1.50    inference(cnf_transformation,[],[f5])).
% 7.67/1.50  
% 7.67/1.50  fof(f9,axiom,(
% 7.67/1.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f24,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.67/1.50    inference(cnf_transformation,[],[f9])).
% 7.67/1.50  
% 7.67/1.50  fof(f8,axiom,(
% 7.67/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f23,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f8])).
% 7.67/1.50  
% 7.67/1.50  fof(f29,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.67/1.50    inference(definition_unfolding,[],[f24,f23])).
% 7.67/1.50  
% 7.67/1.50  fof(f7,axiom,(
% 7.67/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f22,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f7])).
% 7.67/1.50  
% 7.67/1.50  fof(f2,axiom,(
% 7.67/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f17,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f2])).
% 7.67/1.50  
% 7.67/1.50  fof(f27,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.67/1.50    inference(definition_unfolding,[],[f17,f23,f23])).
% 7.67/1.50  
% 7.67/1.50  fof(f4,axiom,(
% 7.67/1.50    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f19,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f4])).
% 7.67/1.50  
% 7.67/1.50  fof(f28,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 7.67/1.50    inference(definition_unfolding,[],[f19,f23])).
% 7.67/1.50  
% 7.67/1.50  fof(f10,axiom,(
% 7.67/1.50    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f25,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f10])).
% 7.67/1.50  
% 7.67/1.50  fof(f30,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.67/1.50    inference(definition_unfolding,[],[f25,f23])).
% 7.67/1.50  
% 7.67/1.50  fof(f11,conjecture,(
% 7.67/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f12,negated_conjecture,(
% 7.67/1.50    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.67/1.50    inference(negated_conjecture,[],[f11])).
% 7.67/1.50  
% 7.67/1.50  fof(f13,plain,(
% 7.67/1.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.67/1.50    inference(ennf_transformation,[],[f12])).
% 7.67/1.50  
% 7.67/1.50  fof(f14,plain,(
% 7.67/1.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.67/1.50    introduced(choice_axiom,[])).
% 7.67/1.50  
% 7.67/1.50  fof(f15,plain,(
% 7.67/1.50    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.67/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 7.67/1.50  
% 7.67/1.50  fof(f26,plain,(
% 7.67/1.50    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.67/1.50    inference(cnf_transformation,[],[f15])).
% 7.67/1.50  
% 7.67/1.50  fof(f3,axiom,(
% 7.67/1.50    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f18,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f3])).
% 7.67/1.50  
% 7.67/1.50  fof(f31,plain,(
% 7.67/1.50    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 7.67/1.50    inference(definition_unfolding,[],[f26,f18,f23])).
% 7.67/1.50  
% 7.67/1.50  cnf(c_0,plain,
% 7.67/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(cnf_transformation,[],[f16]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4,plain,
% 7.67/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.67/1.50      inference(cnf_transformation,[],[f21]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.67/1.50      inference(cnf_transformation,[],[f20]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_31,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_32,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_31,c_3]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_34,plain,
% 7.67/1.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_32]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_41,plain,
% 7.67/1.50      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_34,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.67/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_100,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_179,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_41,c_100]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_198,plain,
% 7.67/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_179,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_201,plain,
% 7.67/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_198,c_41]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.67/1.50      inference(cnf_transformation,[],[f22]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_238,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_201,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_244,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_238,c_198]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_372,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_244]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.67/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 7.67/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_222,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_198,c_2]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_226,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_222,c_3]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_250,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_1,c_226]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_489,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_372,c_250]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_499,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_489,c_3]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_763,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_499,c_0]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_29,plain,
% 7.67/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_259,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_226,c_29]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_261,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_259,c_201]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_419,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_261,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_435,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_419,c_5,c_198]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_719,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_435,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_737,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k1_xboole_0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_719,c_5,c_198]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6774,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_763,c_737]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_56,plain,
% 7.67/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_7,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.67/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_458,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_372,c_7]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_464,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_458,c_3]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_619,plain,
% 7.67/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_56,c_3,c_372,c_464]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_653,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X1) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_619,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_663,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_653,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_487,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_244,c_250]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_501,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_487,c_3]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_773,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_501]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1513,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_663,c_773]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1550,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_1513,c_773]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_21074,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_6774,c_1550]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_386,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_244,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_72,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_81,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_72,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_395,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_386,c_81,c_198]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_514,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_395]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_482,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = X0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_5,c_250]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_505,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = X0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_482,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_414,plain,
% 7.67/1.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_261,c_7]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_439,plain,
% 7.67/1.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_414,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_440,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_439,c_5,c_34]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_506,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_505,c_440]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5598,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X3,k1_xboole_0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_514,c_506]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5671,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_5598,c_32]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_751,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_499]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1431,plain,
% 7.67/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_751,c_395]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_721,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_435,c_250]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_735,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_721,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_736,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_735,c_32]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_7392,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_736]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_20077,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_1431,c_7392]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1150,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_663,c_0]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1751,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_372,c_1150]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1423,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_499,c_751]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1425,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_501,c_751]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1438,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_751,c_0]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1454,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_1425,c_1438]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1455,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_1423,c_1454]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1795,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_1751,c_1455]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_69,plain,
% 7.67/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_29,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_82,plain,
% 7.67/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_69,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_256,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_29,c_226]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4172,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_256]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_17404,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_82,c_4172]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_9955,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_82,c_1150]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_9999,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_9955,c_1550]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_17620,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_17404,c_9999]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_254,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_4,c_226]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3838,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_254]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_17621,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_17620,c_3838,c_9999]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_20236,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_20077,c_1795,c_17621]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_21138,plain,
% 7.67/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_21074,c_5671,c_20236]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_8,negated_conjecture,
% 7.67/1.51      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 7.67/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_27,plain,
% 7.67/1.51      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_27270,plain,
% 7.67/1.51      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_21138,c_27]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1144,plain,
% 7.67/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_663,c_29]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1163,plain,
% 7.67/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_1144,c_619]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1220,plain,
% 7.67/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_1163,c_7]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1228,plain,
% 7.67/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.67/1.51      inference(light_normalisation,[status(thm)],[c_1220,c_201]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1229,plain,
% 7.67/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_1228,c_32]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_11166,plain,
% 7.67/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_1229,c_663]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_27271,plain,
% 7.67/1.51      ( k2_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) != k2_xboole_0(sK0,sK1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_27270,c_7,c_11166]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_699,plain,
% 7.67/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_0,c_435]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1366,plain,
% 7.67/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,X0)) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_699,c_663]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_1405,plain,
% 7.67/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_1366,c_34]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_17375,plain,
% 7.67/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_1405,c_4172]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_17665,plain,
% 7.67/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_17375,c_17621]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_9952,plain,
% 7.67/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_82,c_1550]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_10003,plain,
% 7.67/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_9952,c_9999]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_17666,plain,
% 7.67/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_17665,c_699,c_1795,c_10003]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_25642,plain,
% 7.67/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 7.67/1.51      inference(superposition,[status(thm)],[c_663,c_17666]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_25896,plain,
% 7.67/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_25642,c_17666]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_27272,plain,
% 7.67/1.51      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 7.67/1.51      inference(demodulation,[status(thm)],[c_27271,c_25896]) ).
% 7.67/1.51  
% 7.67/1.51  cnf(c_28670,plain,
% 7.67/1.51      ( $false ),
% 7.67/1.51      inference(theory_normalisation,[status(thm)],[c_27272]) ).
% 7.67/1.51  
% 7.67/1.51  
% 7.67/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.51  
% 7.67/1.51  ------                               Statistics
% 7.67/1.51  
% 7.67/1.51  ------ General
% 7.67/1.51  
% 7.67/1.51  abstr_ref_over_cycles:                  0
% 7.67/1.51  abstr_ref_under_cycles:                 0
% 7.67/1.51  gc_basic_clause_elim:                   0
% 7.67/1.51  forced_gc_time:                         0
% 7.67/1.51  parsing_time:                           0.008
% 7.67/1.51  unif_index_cands_time:                  0.
% 7.67/1.51  unif_index_add_time:                    0.
% 7.67/1.51  orderings_time:                         0.
% 7.67/1.51  out_proof_time:                         0.007
% 7.67/1.51  total_time:                             0.762
% 7.67/1.51  num_of_symbols:                         39
% 7.67/1.51  num_of_terms:                           42723
% 7.67/1.51  
% 7.67/1.51  ------ Preprocessing
% 7.67/1.51  
% 7.67/1.51  num_of_splits:                          0
% 7.67/1.51  num_of_split_atoms:                     3
% 7.67/1.51  num_of_reused_defs:                     6
% 7.67/1.51  num_eq_ax_congr_red:                    0
% 7.67/1.51  num_of_sem_filtered_clauses:            0
% 7.67/1.51  num_of_subtypes:                        0
% 7.67/1.51  monotx_restored_types:                  0
% 7.67/1.51  sat_num_of_epr_types:                   0
% 7.67/1.51  sat_num_of_non_cyclic_types:            0
% 7.67/1.51  sat_guarded_non_collapsed_types:        0
% 7.67/1.51  num_pure_diseq_elim:                    0
% 7.67/1.51  simp_replaced_by:                       0
% 7.67/1.51  res_preprocessed:                       22
% 7.67/1.51  prep_upred:                             0
% 7.67/1.51  prep_unflattend:                        0
% 7.67/1.51  smt_new_axioms:                         0
% 7.67/1.51  pred_elim_cands:                        0
% 7.67/1.51  pred_elim:                              0
% 7.67/1.51  pred_elim_cl:                           0
% 7.67/1.51  pred_elim_cycles:                       0
% 7.67/1.51  merged_defs:                            0
% 7.67/1.51  merged_defs_ncl:                        0
% 7.67/1.51  bin_hyper_res:                          0
% 7.67/1.51  prep_cycles:                            2
% 7.67/1.51  pred_elim_time:                         0.
% 7.67/1.51  splitting_time:                         0.
% 7.67/1.51  sem_filter_time:                        0.
% 7.67/1.51  monotx_time:                            0.
% 7.67/1.51  subtype_inf_time:                       0.
% 7.67/1.51  
% 7.67/1.51  ------ Problem properties
% 7.67/1.51  
% 7.67/1.51  clauses:                                9
% 7.67/1.51  conjectures:                            1
% 7.67/1.51  epr:                                    0
% 7.67/1.51  horn:                                   9
% 7.67/1.51  ground:                                 1
% 7.67/1.51  unary:                                  9
% 7.67/1.51  binary:                                 0
% 7.67/1.51  lits:                                   9
% 7.67/1.51  lits_eq:                                9
% 7.67/1.51  fd_pure:                                0
% 7.67/1.51  fd_pseudo:                              0
% 7.67/1.51  fd_cond:                                0
% 7.67/1.51  fd_pseudo_cond:                         0
% 7.67/1.51  ac_symbols:                             1
% 7.67/1.51  
% 7.67/1.51  ------ Propositional Solver
% 7.67/1.51  
% 7.67/1.51  prop_solver_calls:                      13
% 7.67/1.51  prop_fast_solver_calls:                 56
% 7.67/1.51  smt_solver_calls:                       0
% 7.67/1.51  smt_fast_solver_calls:                  0
% 7.67/1.51  prop_num_of_clauses:                    255
% 7.67/1.51  prop_preprocess_simplified:             360
% 7.67/1.51  prop_fo_subsumed:                       0
% 7.67/1.51  prop_solver_time:                       0.
% 7.67/1.51  smt_solver_time:                        0.
% 7.67/1.51  smt_fast_solver_time:                   0.
% 7.67/1.51  prop_fast_solver_time:                  0.
% 7.67/1.51  prop_unsat_core_time:                   0.
% 7.67/1.51  
% 7.67/1.51  ------ QBF
% 7.67/1.51  
% 7.67/1.51  qbf_q_res:                              0
% 7.67/1.51  qbf_num_tautologies:                    0
% 7.67/1.51  qbf_prep_cycles:                        0
% 7.67/1.51  
% 7.67/1.51  ------ BMC1
% 7.67/1.51  
% 7.67/1.51  bmc1_current_bound:                     -1
% 7.67/1.51  bmc1_last_solved_bound:                 -1
% 7.67/1.51  bmc1_unsat_core_size:                   -1
% 7.67/1.51  bmc1_unsat_core_parents_size:           -1
% 7.67/1.51  bmc1_merge_next_fun:                    0
% 7.67/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.51  
% 7.67/1.51  ------ Instantiation
% 7.67/1.51  
% 7.67/1.51  inst_num_of_clauses:                    0
% 7.67/1.51  inst_num_in_passive:                    0
% 7.67/1.51  inst_num_in_active:                     0
% 7.67/1.51  inst_num_in_unprocessed:                0
% 7.67/1.51  inst_num_of_loops:                      0
% 7.67/1.51  inst_num_of_learning_restarts:          0
% 7.67/1.51  inst_num_moves_active_passive:          0
% 7.67/1.51  inst_lit_activity:                      0
% 7.67/1.51  inst_lit_activity_moves:                0
% 7.67/1.51  inst_num_tautologies:                   0
% 7.67/1.51  inst_num_prop_implied:                  0
% 7.67/1.51  inst_num_existing_simplified:           0
% 7.67/1.51  inst_num_eq_res_simplified:             0
% 7.67/1.51  inst_num_child_elim:                    0
% 7.67/1.51  inst_num_of_dismatching_blockings:      0
% 7.67/1.51  inst_num_of_non_proper_insts:           0
% 7.67/1.51  inst_num_of_duplicates:                 0
% 7.67/1.51  inst_inst_num_from_inst_to_res:         0
% 7.67/1.51  inst_dismatching_checking_time:         0.
% 7.67/1.51  
% 7.67/1.51  ------ Resolution
% 7.67/1.51  
% 7.67/1.51  res_num_of_clauses:                     0
% 7.67/1.51  res_num_in_passive:                     0
% 7.67/1.51  res_num_in_active:                      0
% 7.67/1.51  res_num_of_loops:                       24
% 7.67/1.51  res_forward_subset_subsumed:            0
% 7.67/1.51  res_backward_subset_subsumed:           0
% 7.67/1.51  res_forward_subsumed:                   0
% 7.67/1.51  res_backward_subsumed:                  0
% 7.67/1.51  res_forward_subsumption_resolution:     0
% 7.67/1.51  res_backward_subsumption_resolution:    0
% 7.67/1.51  res_clause_to_clause_subsumption:       62504
% 7.67/1.51  res_orphan_elimination:                 0
% 7.67/1.51  res_tautology_del:                      0
% 7.67/1.51  res_num_eq_res_simplified:              0
% 7.67/1.51  res_num_sel_changes:                    0
% 7.67/1.51  res_moves_from_active_to_pass:          0
% 7.67/1.51  
% 7.67/1.51  ------ Superposition
% 7.67/1.51  
% 7.67/1.51  sup_time_total:                         0.
% 7.67/1.51  sup_time_generating:                    0.
% 7.67/1.51  sup_time_sim_full:                      0.
% 7.67/1.51  sup_time_sim_immed:                     0.
% 7.67/1.51  
% 7.67/1.51  sup_num_of_clauses:                     2891
% 7.67/1.51  sup_num_in_active:                      117
% 7.67/1.51  sup_num_in_passive:                     2774
% 7.67/1.51  sup_num_of_loops:                       153
% 7.67/1.51  sup_fw_superposition:                   10749
% 7.67/1.51  sup_bw_superposition:                   8360
% 7.67/1.51  sup_immediate_simplified:               8736
% 7.67/1.51  sup_given_eliminated:                   6
% 7.67/1.51  comparisons_done:                       0
% 7.67/1.51  comparisons_avoided:                    0
% 7.67/1.51  
% 7.67/1.51  ------ Simplifications
% 7.67/1.51  
% 7.67/1.51  
% 7.67/1.51  sim_fw_subset_subsumed:                 0
% 7.67/1.51  sim_bw_subset_subsumed:                 0
% 7.67/1.51  sim_fw_subsumed:                        1193
% 7.67/1.51  sim_bw_subsumed:                        25
% 7.67/1.51  sim_fw_subsumption_res:                 0
% 7.67/1.51  sim_bw_subsumption_res:                 0
% 7.67/1.51  sim_tautology_del:                      0
% 7.67/1.51  sim_eq_tautology_del:                   2724
% 7.67/1.51  sim_eq_res_simp:                        0
% 7.67/1.51  sim_fw_demodulated:                     5391
% 7.67/1.51  sim_bw_demodulated:                     71
% 7.67/1.51  sim_light_normalised:                   3945
% 7.67/1.51  sim_joinable_taut:                      10
% 7.67/1.51  sim_joinable_simp:                      1
% 7.67/1.51  sim_ac_normalised:                      0
% 7.67/1.51  sim_smt_subsumption:                    0
% 7.67/1.51  
%------------------------------------------------------------------------------
