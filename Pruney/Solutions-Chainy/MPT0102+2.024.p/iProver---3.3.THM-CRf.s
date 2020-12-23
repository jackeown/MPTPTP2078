%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:06 EST 2020

% Result     : Theorem 27.35s
% Output     : CNFRefutation 27.35s
% Verified   : 
% Statistics : Number of formulae       :  252 (783354 expanded)
%              Number of clauses        :  229 (264662 expanded)
%              Number of leaves         :    9 (230086 expanded)
%              Depth                    :   49
%              Number of atoms          :  253 (783355 expanded)
%              Number of equality atoms :  252 (783354 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f14,f18,f18])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f23,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f20,f18,f15,f15])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_4,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_39,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_22,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_63,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_39,c_0])).

cnf(c_70,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_22,c_63])).

cnf(c_74,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_70])).

cnf(c_94,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X2) = X2 ),
    inference(superposition,[status(thm)],[c_3,c_74])).

cnf(c_97,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X2) = X2 ),
    inference(demodulation,[status(thm)],[c_94,c_3])).

cnf(c_33,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_141,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_33])).

cnf(c_227,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
    inference(demodulation,[status(thm)],[c_97,c_141])).

cnf(c_240,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_39,c_227])).

cnf(c_77,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_70,c_0])).

cnf(c_83,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_77])).

cnf(c_283,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_240,c_83])).

cnf(c_81,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_77])).

cnf(c_282,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_240,c_81])).

cnf(c_146,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_70,c_33])).

cnf(c_154,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_146,c_2])).

cnf(c_284,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X1),X2)) = k2_xboole_0(k4_xboole_0(X1,X1),X0) ),
    inference(superposition,[status(thm)],[c_240,c_154])).

cnf(c_286,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X1),X2)) = X0 ),
    inference(demodulation,[status(thm)],[c_284,c_240])).

cnf(c_287,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_286,c_3])).

cnf(c_288,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_283,c_287])).

cnf(c_289,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_282,c_288])).

cnf(c_290,plain,
    ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_289])).

cnf(c_439,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_283,c_290])).

cnf(c_915,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_439,c_2])).

cnf(c_272,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_240,c_0])).

cnf(c_450,plain,
    ( k2_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_272,c_290])).

cnf(c_928,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_915,c_450])).

cnf(c_1908,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_928])).

cnf(c_2833,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1908,c_0])).

cnf(c_673,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k2_xboole_0(X0,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_290,c_33])).

cnf(c_676,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_673,c_450])).

cnf(c_1806,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_676,c_227])).

cnf(c_26,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_2684,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1806,c_26])).

cnf(c_293,plain,
    ( k2_xboole_0(sP0_iProver_split,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_290,c_240])).

cnf(c_438,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_284,c_3,c_290,c_293])).

cnf(c_440,plain,
    ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_439,c_438])).

cnf(c_271,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),X2) = X2 ),
    inference(superposition,[status(thm)],[c_3,c_240])).

cnf(c_452,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),X2) = X2 ),
    inference(demodulation,[status(thm)],[c_271,c_2])).

cnf(c_617,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X1)),X0) ),
    inference(superposition,[status(thm)],[c_452,c_2])).

cnf(c_634,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_617,c_452])).

cnf(c_625,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X1)))) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_452,c_81])).

cnf(c_636,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X2,X2) ),
    inference(demodulation,[status(thm)],[c_634,c_625])).

cnf(c_639,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_636,c_290])).

cnf(c_2692,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2684,c_440,c_639])).

cnf(c_3937,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_2833,c_2692])).

cnf(c_4008,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3937,c_2692])).

cnf(c_5413,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X2) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_4008,c_26])).

cnf(c_5469,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_5413,c_440,c_639])).

cnf(c_5,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_21,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_5])).

cnf(c_105328,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_5469,c_21])).

cnf(c_48,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_148,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_48,c_33])).

cnf(c_50349,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,X3),X0)) ),
    inference(superposition,[status(thm)],[c_3,c_148])).

cnf(c_3924,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_33,c_2692])).

cnf(c_4018,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3924,c_2692])).

cnf(c_4019,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_4018,c_3])).

cnf(c_50370,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1))),X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4019,c_148])).

cnf(c_3930,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_154,c_2692])).

cnf(c_4014,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3930,c_2692])).

cnf(c_20805,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_3,c_4014])).

cnf(c_21102,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_20805,c_3])).

cnf(c_919,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_439,c_227])).

cnf(c_925,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_919,c_450])).

cnf(c_9024,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_925])).

cnf(c_50576,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_148,c_9024])).

cnf(c_2810,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X0) ),
    inference(superposition,[status(thm)],[c_154,c_1908])).

cnf(c_975,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_639,c_2])).

cnf(c_985,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_975,c_450])).

cnf(c_2058,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_154,c_985])).

cnf(c_2082,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2058,c_154])).

cnf(c_2860,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2810,c_2082])).

cnf(c_34,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_35,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_34,c_3])).

cnf(c_2092,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_35,c_141])).

cnf(c_302,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_70,c_26])).

cnf(c_436,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_302,c_3,c_290])).

cnf(c_539,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_436,c_3])).

cnf(c_2201,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_2092,c_539])).

cnf(c_32,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_1016,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_639,c_32])).

cnf(c_1229,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1016,c_3,c_450])).

cnf(c_2275,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_2201,c_1229])).

cnf(c_3628,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_2275,c_2092])).

cnf(c_3634,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),sP0_iProver_split)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3628,c_290,c_440])).

cnf(c_3635,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_3634,c_450])).

cnf(c_3644,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_3635])).

cnf(c_4473,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X3)) = k4_xboole_0(X0,X3) ),
    inference(superposition,[status(thm)],[c_3644,c_3])).

cnf(c_346,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X2)),X2) = X2 ),
    inference(superposition,[status(thm)],[c_26,c_227])).

cnf(c_408,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))),X2) = X2 ),
    inference(demodulation,[status(thm)],[c_346,c_3])).

cnf(c_46230,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X2)),X2) = X2 ),
    inference(superposition,[status(thm)],[c_4473,c_408])).

cnf(c_46523,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)),X2) = X2 ),
    inference(superposition,[status(thm)],[c_2860,c_46230])).

cnf(c_46865,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X2)))),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_1,c_46523])).

cnf(c_3687,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_3635,c_3])).

cnf(c_13077,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_154,c_3687])).

cnf(c_13268,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13077,c_3687])).

cnf(c_13269,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13268,c_3])).

cnf(c_143,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_33])).

cnf(c_38405,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2692,c_143])).

cnf(c_38807,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_38405,c_143])).

cnf(c_887,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_48,c_439])).

cnf(c_1716,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(sP0_iProver_split,X2) ),
    inference(superposition,[status(thm)],[c_887,c_3])).

cnf(c_281,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_240,c_77])).

cnf(c_442,plain,
    ( k4_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_281,c_290])).

cnf(c_1750,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_1716,c_3,c_442])).

cnf(c_2361,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_0,c_1750])).

cnf(c_150,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_74,c_33])).

cnf(c_153,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_150,c_2])).

cnf(c_21494,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),sP0_iProver_split))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_2361,c_153])).

cnf(c_3966,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2692,c_1])).

cnf(c_3990,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3966,c_439,c_440])).

cnf(c_3978,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2692,c_154])).

cnf(c_3983,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_3978,c_154])).

cnf(c_20552,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_3990,c_3983])).

cnf(c_28,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_3,c_3])).

cnf(c_36,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_28,c_3])).

cnf(c_3175,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_36,c_439])).

cnf(c_18014,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_3175,c_39])).

cnf(c_2827,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_1908,c_439])).

cnf(c_5268,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),sP0_iProver_split) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2827,c_3990])).

cnf(c_2047,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_985])).

cnf(c_1936,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_928,c_0])).

cnf(c_3028,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2047,c_1936])).

cnf(c_3064,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_3028,c_2047])).

cnf(c_5323,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5268,c_3064])).

cnf(c_18076,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),k2_xboole_0(X1,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_18014,c_5323])).

cnf(c_3468,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2833,c_33])).

cnf(c_2070,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_985,c_0])).

cnf(c_3276,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2070,c_33])).

cnf(c_3282,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3276,c_2])).

cnf(c_3477,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_3468,c_3282])).

cnf(c_3959,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_2692,c_3])).

cnf(c_3996,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_3959,c_3])).

cnf(c_18077,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_18076,c_3477,c_3996])).

cnf(c_20742,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_20552,c_18077])).

cnf(c_21718,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),sP0_iProver_split))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_21494,c_20742])).

cnf(c_979,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_639,c_227])).

cnf(c_984,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_979,c_450])).

cnf(c_9303,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_984,c_33])).

cnf(c_3010,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_2047])).

cnf(c_3071,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3010,c_2047])).

cnf(c_4341,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3071,c_0])).

cnf(c_9310,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_9303,c_4341])).

cnf(c_21719,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_21718,c_3,c_9310,c_20742])).

cnf(c_22235,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X1,X0),X3)))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_21719,c_2860])).

cnf(c_2837,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_1908,c_1750])).

cnf(c_21502,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X3),sP0_iProver_split))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_2837,c_153])).

cnf(c_21698,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X3),sP0_iProver_split))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_21502,c_20742])).

cnf(c_14934,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_2837,c_1])).

cnf(c_4104,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split),X2) ),
    inference(superposition,[status(thm)],[c_2827,c_26])).

cnf(c_4129,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sP0_iProver_split,X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split),X2) ),
    inference(demodulation,[status(thm)],[c_4104,c_2827])).

cnf(c_4130,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_4129,c_3,c_293,c_440])).

cnf(c_13528,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_4130,c_1229])).

cnf(c_14980,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),sP0_iProver_split) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_14934,c_13528])).

cnf(c_21699,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X1,X0),X3)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_21698,c_14980,c_20742])).

cnf(c_22250,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_22235,c_21699])).

cnf(c_21908,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_21719])).

cnf(c_22422,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_21908])).

cnf(c_3019,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_154,c_2047])).

cnf(c_3069,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3019,c_2047])).

cnf(c_17729,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3069,c_0])).

cnf(c_21408,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_17729,c_153])).

cnf(c_22813,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_22422,c_21408])).

cnf(c_38134,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_22813,c_2692])).

cnf(c_38808,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_38807,c_22250,c_38134])).

cnf(c_47261,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_46865,c_13269,c_38808])).

cnf(c_50643,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_50576,c_3,c_47261])).

cnf(c_50577,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_148,c_984])).

cnf(c_50641,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_50577,c_148])).

cnf(c_50642,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_50641,c_3])).

cnf(c_50644,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_50643,c_50642])).

cnf(c_51666,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,X0))) ),
    inference(demodulation,[status(thm)],[c_50370,c_21102,c_50644])).

cnf(c_51697,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,X3),X0)) ),
    inference(demodulation,[status(thm)],[c_50349,c_51666])).

cnf(c_51698,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),X0),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_51697,c_50644])).

cnf(c_151,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) ),
    inference(superposition,[status(thm)],[c_33,c_33])).

cnf(c_4323,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3071,c_2692])).

cnf(c_4380,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_4323,c_3635])).

cnf(c_6025,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_3,c_4380])).

cnf(c_145,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_63,c_33])).

cnf(c_58308,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X3,X2)) ),
    inference(superposition,[status(thm)],[c_6025,c_145])).

cnf(c_84,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_77,c_2])).

cnf(c_3117,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_84,c_36])).

cnf(c_3042,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2047,c_0])).

cnf(c_3209,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_3117,c_3042])).

cnf(c_20037,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),X3) ),
    inference(superposition,[status(thm)],[c_3209,c_3])).

cnf(c_19606,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X3)),X4))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X2,X1),X4)) ),
    inference(superposition,[status(thm)],[c_17729,c_36])).

cnf(c_3120,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X3)),X4))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X4)) ),
    inference(superposition,[status(thm)],[c_154,c_36])).

cnf(c_3208,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X3)),X4))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X4))) ),
    inference(demodulation,[status(thm)],[c_3120,c_36])).

cnf(c_19674,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_19606,c_3208])).

cnf(c_20130,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_20037,c_19674])).

cnf(c_22682,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_21908,c_2692])).

cnf(c_873,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP0_iProver_split) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_450,c_26])).

cnf(c_50244,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP0_iProver_split),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_873,c_148])).

cnf(c_317,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_26])).

cnf(c_51723,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_50244,c_317,c_50644])).

cnf(c_51724,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_51723,c_145,c_450])).

cnf(c_58437,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X0,X1),X2))))),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_58308,c_6025,c_20130,c_22682,c_51724])).

cnf(c_2798,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_1908])).

cnf(c_942,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_2,c_639])).

cnf(c_1494,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_942,c_2])).

cnf(c_1513,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1494,c_450])).

cnf(c_2862,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2798,c_1513])).

cnf(c_4454,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_3644,c_2862])).

cnf(c_3013,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X0) ),
    inference(superposition,[status(thm)],[c_33,c_2047])).

cnf(c_3070,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3013,c_2047])).

cnf(c_4511,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(light_normalisation,[status(thm)],[c_4454,c_3070])).

cnf(c_13188,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X3))) = k4_xboole_0(k4_xboole_0(X0,X1),X3) ),
    inference(superposition,[status(thm)],[c_3687,c_3])).

cnf(c_13228,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_13188,c_3])).

cnf(c_58438,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_58437,c_4511,c_13228])).

cnf(c_60597,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X1)),X2) ),
    inference(light_normalisation,[status(thm)],[c_151,c_151,c_58438])).

cnf(c_4304,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_26,c_3071])).

cnf(c_4206,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_26,c_2862])).

cnf(c_4286,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_4206,c_317])).

cnf(c_4394,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) ),
    inference(light_normalisation,[status(thm)],[c_4304,c_317,c_4286])).

cnf(c_4395,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_4394,c_3983])).

cnf(c_61057,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X3)),X2),X0) ),
    inference(superposition,[status(thm)],[c_60597,c_4395])).

cnf(c_19471,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_3,c_17729])).

cnf(c_61158,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),X1) = k2_xboole_0(k4_xboole_0(X0,X3),X1) ),
    inference(light_normalisation,[status(thm)],[c_61057,c_19471])).

cnf(c_105329,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_105328,c_51698,c_61158])).

cnf(c_105330,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_105329,c_293,c_887])).

cnf(c_106341,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_105330])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.35/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.35/4.00  
% 27.35/4.00  ------  iProver source info
% 27.35/4.00  
% 27.35/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.35/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.35/4.00  git: non_committed_changes: false
% 27.35/4.00  git: last_make_outside_of_git: false
% 27.35/4.00  
% 27.35/4.00  ------ 
% 27.35/4.00  
% 27.35/4.00  ------ Input Options
% 27.35/4.00  
% 27.35/4.00  --out_options                           all
% 27.35/4.00  --tptp_safe_out                         true
% 27.35/4.00  --problem_path                          ""
% 27.35/4.00  --include_path                          ""
% 27.35/4.00  --clausifier                            res/vclausify_rel
% 27.35/4.00  --clausifier_options                    --mode clausify
% 27.35/4.00  --stdin                                 false
% 27.35/4.00  --stats_out                             all
% 27.35/4.00  
% 27.35/4.00  ------ General Options
% 27.35/4.00  
% 27.35/4.00  --fof                                   false
% 27.35/4.00  --time_out_real                         305.
% 27.35/4.00  --time_out_virtual                      -1.
% 27.35/4.00  --symbol_type_check                     false
% 27.35/4.00  --clausify_out                          false
% 27.35/4.00  --sig_cnt_out                           false
% 27.35/4.00  --trig_cnt_out                          false
% 27.35/4.00  --trig_cnt_out_tolerance                1.
% 27.35/4.00  --trig_cnt_out_sk_spl                   false
% 27.35/4.00  --abstr_cl_out                          false
% 27.35/4.00  
% 27.35/4.00  ------ Global Options
% 27.35/4.00  
% 27.35/4.00  --schedule                              default
% 27.35/4.00  --add_important_lit                     false
% 27.35/4.00  --prop_solver_per_cl                    1000
% 27.35/4.00  --min_unsat_core                        false
% 27.35/4.00  --soft_assumptions                      false
% 27.35/4.00  --soft_lemma_size                       3
% 27.35/4.00  --prop_impl_unit_size                   0
% 27.35/4.00  --prop_impl_unit                        []
% 27.35/4.00  --share_sel_clauses                     true
% 27.35/4.00  --reset_solvers                         false
% 27.35/4.00  --bc_imp_inh                            [conj_cone]
% 27.35/4.00  --conj_cone_tolerance                   3.
% 27.35/4.00  --extra_neg_conj                        none
% 27.35/4.00  --large_theory_mode                     true
% 27.35/4.00  --prolific_symb_bound                   200
% 27.35/4.00  --lt_threshold                          2000
% 27.35/4.00  --clause_weak_htbl                      true
% 27.35/4.00  --gc_record_bc_elim                     false
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing Options
% 27.35/4.00  
% 27.35/4.00  --preprocessing_flag                    true
% 27.35/4.00  --time_out_prep_mult                    0.1
% 27.35/4.00  --splitting_mode                        input
% 27.35/4.00  --splitting_grd                         true
% 27.35/4.00  --splitting_cvd                         false
% 27.35/4.00  --splitting_cvd_svl                     false
% 27.35/4.00  --splitting_nvd                         32
% 27.35/4.00  --sub_typing                            true
% 27.35/4.00  --prep_gs_sim                           true
% 27.35/4.00  --prep_unflatten                        true
% 27.35/4.00  --prep_res_sim                          true
% 27.35/4.00  --prep_upred                            true
% 27.35/4.00  --prep_sem_filter                       exhaustive
% 27.35/4.00  --prep_sem_filter_out                   false
% 27.35/4.00  --pred_elim                             true
% 27.35/4.00  --res_sim_input                         true
% 27.35/4.00  --eq_ax_congr_red                       true
% 27.35/4.00  --pure_diseq_elim                       true
% 27.35/4.00  --brand_transform                       false
% 27.35/4.00  --non_eq_to_eq                          false
% 27.35/4.00  --prep_def_merge                        true
% 27.35/4.00  --prep_def_merge_prop_impl              false
% 27.35/4.00  --prep_def_merge_mbd                    true
% 27.35/4.00  --prep_def_merge_tr_red                 false
% 27.35/4.00  --prep_def_merge_tr_cl                  false
% 27.35/4.00  --smt_preprocessing                     true
% 27.35/4.00  --smt_ac_axioms                         fast
% 27.35/4.00  --preprocessed_out                      false
% 27.35/4.00  --preprocessed_stats                    false
% 27.35/4.00  
% 27.35/4.00  ------ Abstraction refinement Options
% 27.35/4.00  
% 27.35/4.00  --abstr_ref                             []
% 27.35/4.00  --abstr_ref_prep                        false
% 27.35/4.00  --abstr_ref_until_sat                   false
% 27.35/4.00  --abstr_ref_sig_restrict                funpre
% 27.35/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.35/4.00  --abstr_ref_under                       []
% 27.35/4.00  
% 27.35/4.00  ------ SAT Options
% 27.35/4.00  
% 27.35/4.00  --sat_mode                              false
% 27.35/4.00  --sat_fm_restart_options                ""
% 27.35/4.00  --sat_gr_def                            false
% 27.35/4.00  --sat_epr_types                         true
% 27.35/4.00  --sat_non_cyclic_types                  false
% 27.35/4.00  --sat_finite_models                     false
% 27.35/4.00  --sat_fm_lemmas                         false
% 27.35/4.00  --sat_fm_prep                           false
% 27.35/4.00  --sat_fm_uc_incr                        true
% 27.35/4.00  --sat_out_model                         small
% 27.35/4.00  --sat_out_clauses                       false
% 27.35/4.00  
% 27.35/4.00  ------ QBF Options
% 27.35/4.00  
% 27.35/4.00  --qbf_mode                              false
% 27.35/4.00  --qbf_elim_univ                         false
% 27.35/4.00  --qbf_dom_inst                          none
% 27.35/4.00  --qbf_dom_pre_inst                      false
% 27.35/4.00  --qbf_sk_in                             false
% 27.35/4.00  --qbf_pred_elim                         true
% 27.35/4.00  --qbf_split                             512
% 27.35/4.00  
% 27.35/4.00  ------ BMC1 Options
% 27.35/4.00  
% 27.35/4.00  --bmc1_incremental                      false
% 27.35/4.00  --bmc1_axioms                           reachable_all
% 27.35/4.00  --bmc1_min_bound                        0
% 27.35/4.00  --bmc1_max_bound                        -1
% 27.35/4.00  --bmc1_max_bound_default                -1
% 27.35/4.00  --bmc1_symbol_reachability              true
% 27.35/4.00  --bmc1_property_lemmas                  false
% 27.35/4.00  --bmc1_k_induction                      false
% 27.35/4.00  --bmc1_non_equiv_states                 false
% 27.35/4.00  --bmc1_deadlock                         false
% 27.35/4.00  --bmc1_ucm                              false
% 27.35/4.00  --bmc1_add_unsat_core                   none
% 27.35/4.00  --bmc1_unsat_core_children              false
% 27.35/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.35/4.00  --bmc1_out_stat                         full
% 27.35/4.00  --bmc1_ground_init                      false
% 27.35/4.00  --bmc1_pre_inst_next_state              false
% 27.35/4.00  --bmc1_pre_inst_state                   false
% 27.35/4.00  --bmc1_pre_inst_reach_state             false
% 27.35/4.00  --bmc1_out_unsat_core                   false
% 27.35/4.00  --bmc1_aig_witness_out                  false
% 27.35/4.00  --bmc1_verbose                          false
% 27.35/4.00  --bmc1_dump_clauses_tptp                false
% 27.35/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.35/4.00  --bmc1_dump_file                        -
% 27.35/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.35/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.35/4.00  --bmc1_ucm_extend_mode                  1
% 27.35/4.00  --bmc1_ucm_init_mode                    2
% 27.35/4.00  --bmc1_ucm_cone_mode                    none
% 27.35/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.35/4.00  --bmc1_ucm_relax_model                  4
% 27.35/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.35/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.35/4.00  --bmc1_ucm_layered_model                none
% 27.35/4.00  --bmc1_ucm_max_lemma_size               10
% 27.35/4.00  
% 27.35/4.00  ------ AIG Options
% 27.35/4.00  
% 27.35/4.00  --aig_mode                              false
% 27.35/4.00  
% 27.35/4.00  ------ Instantiation Options
% 27.35/4.00  
% 27.35/4.00  --instantiation_flag                    true
% 27.35/4.00  --inst_sos_flag                         false
% 27.35/4.00  --inst_sos_phase                        true
% 27.35/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel_side                     num_symb
% 27.35/4.00  --inst_solver_per_active                1400
% 27.35/4.00  --inst_solver_calls_frac                1.
% 27.35/4.00  --inst_passive_queue_type               priority_queues
% 27.35/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.35/4.00  --inst_passive_queues_freq              [25;2]
% 27.35/4.00  --inst_dismatching                      true
% 27.35/4.00  --inst_eager_unprocessed_to_passive     true
% 27.35/4.00  --inst_prop_sim_given                   true
% 27.35/4.00  --inst_prop_sim_new                     false
% 27.35/4.00  --inst_subs_new                         false
% 27.35/4.00  --inst_eq_res_simp                      false
% 27.35/4.00  --inst_subs_given                       false
% 27.35/4.00  --inst_orphan_elimination               true
% 27.35/4.00  --inst_learning_loop_flag               true
% 27.35/4.00  --inst_learning_start                   3000
% 27.35/4.00  --inst_learning_factor                  2
% 27.35/4.00  --inst_start_prop_sim_after_learn       3
% 27.35/4.00  --inst_sel_renew                        solver
% 27.35/4.00  --inst_lit_activity_flag                true
% 27.35/4.00  --inst_restr_to_given                   false
% 27.35/4.00  --inst_activity_threshold               500
% 27.35/4.00  --inst_out_proof                        true
% 27.35/4.00  
% 27.35/4.00  ------ Resolution Options
% 27.35/4.00  
% 27.35/4.00  --resolution_flag                       true
% 27.35/4.00  --res_lit_sel                           adaptive
% 27.35/4.00  --res_lit_sel_side                      none
% 27.35/4.00  --res_ordering                          kbo
% 27.35/4.00  --res_to_prop_solver                    active
% 27.35/4.00  --res_prop_simpl_new                    false
% 27.35/4.00  --res_prop_simpl_given                  true
% 27.35/4.00  --res_passive_queue_type                priority_queues
% 27.35/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.35/4.00  --res_passive_queues_freq               [15;5]
% 27.35/4.00  --res_forward_subs                      full
% 27.35/4.00  --res_backward_subs                     full
% 27.35/4.00  --res_forward_subs_resolution           true
% 27.35/4.00  --res_backward_subs_resolution          true
% 27.35/4.00  --res_orphan_elimination                true
% 27.35/4.00  --res_time_limit                        2.
% 27.35/4.00  --res_out_proof                         true
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Options
% 27.35/4.00  
% 27.35/4.00  --superposition_flag                    true
% 27.35/4.00  --sup_passive_queue_type                priority_queues
% 27.35/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.35/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.35/4.00  --demod_completeness_check              fast
% 27.35/4.00  --demod_use_ground                      true
% 27.35/4.00  --sup_to_prop_solver                    passive
% 27.35/4.00  --sup_prop_simpl_new                    true
% 27.35/4.00  --sup_prop_simpl_given                  true
% 27.35/4.00  --sup_fun_splitting                     false
% 27.35/4.00  --sup_smt_interval                      50000
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Simplification Setup
% 27.35/4.00  
% 27.35/4.00  --sup_indices_passive                   []
% 27.35/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.35/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.35/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.35/4.00  --sup_full_bw                           [BwDemod]
% 27.35/4.00  --sup_immed_triv                        [TrivRules]
% 27.35/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.35/4.00  --sup_immed_bw_main                     []
% 27.35/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.35/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.35/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.35/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.35/4.00  
% 27.35/4.00  ------ Combination Options
% 27.35/4.00  
% 27.35/4.00  --comb_res_mult                         3
% 27.35/4.00  --comb_sup_mult                         2
% 27.35/4.00  --comb_inst_mult                        10
% 27.35/4.00  
% 27.35/4.00  ------ Debug Options
% 27.35/4.00  
% 27.35/4.00  --dbg_backtrace                         false
% 27.35/4.00  --dbg_dump_prop_clauses                 false
% 27.35/4.00  --dbg_dump_prop_clauses_file            -
% 27.35/4.00  --dbg_out_stat                          false
% 27.35/4.00  ------ Parsing...
% 27.35/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.35/4.00  ------ Proving...
% 27.35/4.00  ------ Problem Properties 
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  clauses                                 6
% 27.35/4.00  conjectures                             1
% 27.35/4.00  EPR                                     0
% 27.35/4.00  Horn                                    6
% 27.35/4.00  unary                                   6
% 27.35/4.00  binary                                  0
% 27.35/4.00  lits                                    6
% 27.35/4.00  lits eq                                 6
% 27.35/4.00  fd_pure                                 0
% 27.35/4.00  fd_pseudo                               0
% 27.35/4.00  fd_cond                                 0
% 27.35/4.00  fd_pseudo_cond                          0
% 27.35/4.00  AC symbols                              0
% 27.35/4.00  
% 27.35/4.00  ------ Schedule UEQ
% 27.35/4.00  
% 27.35/4.00  ------ pure equality problem: resolution off 
% 27.35/4.00  
% 27.35/4.00  ------ Option_UEQ Time Limit: Unbounded
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  ------ 
% 27.35/4.00  Current options:
% 27.35/4.00  ------ 
% 27.35/4.00  
% 27.35/4.00  ------ Input Options
% 27.35/4.00  
% 27.35/4.00  --out_options                           all
% 27.35/4.00  --tptp_safe_out                         true
% 27.35/4.00  --problem_path                          ""
% 27.35/4.00  --include_path                          ""
% 27.35/4.00  --clausifier                            res/vclausify_rel
% 27.35/4.00  --clausifier_options                    --mode clausify
% 27.35/4.00  --stdin                                 false
% 27.35/4.00  --stats_out                             all
% 27.35/4.00  
% 27.35/4.00  ------ General Options
% 27.35/4.00  
% 27.35/4.00  --fof                                   false
% 27.35/4.00  --time_out_real                         305.
% 27.35/4.00  --time_out_virtual                      -1.
% 27.35/4.00  --symbol_type_check                     false
% 27.35/4.00  --clausify_out                          false
% 27.35/4.00  --sig_cnt_out                           false
% 27.35/4.00  --trig_cnt_out                          false
% 27.35/4.00  --trig_cnt_out_tolerance                1.
% 27.35/4.00  --trig_cnt_out_sk_spl                   false
% 27.35/4.00  --abstr_cl_out                          false
% 27.35/4.00  
% 27.35/4.00  ------ Global Options
% 27.35/4.00  
% 27.35/4.00  --schedule                              default
% 27.35/4.00  --add_important_lit                     false
% 27.35/4.00  --prop_solver_per_cl                    1000
% 27.35/4.00  --min_unsat_core                        false
% 27.35/4.00  --soft_assumptions                      false
% 27.35/4.00  --soft_lemma_size                       3
% 27.35/4.00  --prop_impl_unit_size                   0
% 27.35/4.00  --prop_impl_unit                        []
% 27.35/4.00  --share_sel_clauses                     true
% 27.35/4.00  --reset_solvers                         false
% 27.35/4.00  --bc_imp_inh                            [conj_cone]
% 27.35/4.00  --conj_cone_tolerance                   3.
% 27.35/4.00  --extra_neg_conj                        none
% 27.35/4.00  --large_theory_mode                     true
% 27.35/4.00  --prolific_symb_bound                   200
% 27.35/4.00  --lt_threshold                          2000
% 27.35/4.00  --clause_weak_htbl                      true
% 27.35/4.00  --gc_record_bc_elim                     false
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing Options
% 27.35/4.00  
% 27.35/4.00  --preprocessing_flag                    true
% 27.35/4.00  --time_out_prep_mult                    0.1
% 27.35/4.00  --splitting_mode                        input
% 27.35/4.00  --splitting_grd                         true
% 27.35/4.00  --splitting_cvd                         false
% 27.35/4.00  --splitting_cvd_svl                     false
% 27.35/4.00  --splitting_nvd                         32
% 27.35/4.00  --sub_typing                            true
% 27.35/4.00  --prep_gs_sim                           true
% 27.35/4.00  --prep_unflatten                        true
% 27.35/4.00  --prep_res_sim                          true
% 27.35/4.00  --prep_upred                            true
% 27.35/4.00  --prep_sem_filter                       exhaustive
% 27.35/4.00  --prep_sem_filter_out                   false
% 27.35/4.00  --pred_elim                             true
% 27.35/4.00  --res_sim_input                         true
% 27.35/4.00  --eq_ax_congr_red                       true
% 27.35/4.00  --pure_diseq_elim                       true
% 27.35/4.00  --brand_transform                       false
% 27.35/4.00  --non_eq_to_eq                          false
% 27.35/4.00  --prep_def_merge                        true
% 27.35/4.00  --prep_def_merge_prop_impl              false
% 27.35/4.00  --prep_def_merge_mbd                    true
% 27.35/4.00  --prep_def_merge_tr_red                 false
% 27.35/4.00  --prep_def_merge_tr_cl                  false
% 27.35/4.00  --smt_preprocessing                     true
% 27.35/4.00  --smt_ac_axioms                         fast
% 27.35/4.00  --preprocessed_out                      false
% 27.35/4.00  --preprocessed_stats                    false
% 27.35/4.00  
% 27.35/4.00  ------ Abstraction refinement Options
% 27.35/4.00  
% 27.35/4.00  --abstr_ref                             []
% 27.35/4.00  --abstr_ref_prep                        false
% 27.35/4.00  --abstr_ref_until_sat                   false
% 27.35/4.00  --abstr_ref_sig_restrict                funpre
% 27.35/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.35/4.00  --abstr_ref_under                       []
% 27.35/4.00  
% 27.35/4.00  ------ SAT Options
% 27.35/4.00  
% 27.35/4.00  --sat_mode                              false
% 27.35/4.00  --sat_fm_restart_options                ""
% 27.35/4.00  --sat_gr_def                            false
% 27.35/4.00  --sat_epr_types                         true
% 27.35/4.00  --sat_non_cyclic_types                  false
% 27.35/4.00  --sat_finite_models                     false
% 27.35/4.00  --sat_fm_lemmas                         false
% 27.35/4.00  --sat_fm_prep                           false
% 27.35/4.00  --sat_fm_uc_incr                        true
% 27.35/4.00  --sat_out_model                         small
% 27.35/4.00  --sat_out_clauses                       false
% 27.35/4.00  
% 27.35/4.00  ------ QBF Options
% 27.35/4.00  
% 27.35/4.00  --qbf_mode                              false
% 27.35/4.00  --qbf_elim_univ                         false
% 27.35/4.00  --qbf_dom_inst                          none
% 27.35/4.00  --qbf_dom_pre_inst                      false
% 27.35/4.00  --qbf_sk_in                             false
% 27.35/4.00  --qbf_pred_elim                         true
% 27.35/4.00  --qbf_split                             512
% 27.35/4.00  
% 27.35/4.00  ------ BMC1 Options
% 27.35/4.00  
% 27.35/4.00  --bmc1_incremental                      false
% 27.35/4.00  --bmc1_axioms                           reachable_all
% 27.35/4.00  --bmc1_min_bound                        0
% 27.35/4.00  --bmc1_max_bound                        -1
% 27.35/4.00  --bmc1_max_bound_default                -1
% 27.35/4.00  --bmc1_symbol_reachability              true
% 27.35/4.00  --bmc1_property_lemmas                  false
% 27.35/4.00  --bmc1_k_induction                      false
% 27.35/4.00  --bmc1_non_equiv_states                 false
% 27.35/4.00  --bmc1_deadlock                         false
% 27.35/4.00  --bmc1_ucm                              false
% 27.35/4.00  --bmc1_add_unsat_core                   none
% 27.35/4.00  --bmc1_unsat_core_children              false
% 27.35/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.35/4.00  --bmc1_out_stat                         full
% 27.35/4.00  --bmc1_ground_init                      false
% 27.35/4.00  --bmc1_pre_inst_next_state              false
% 27.35/4.00  --bmc1_pre_inst_state                   false
% 27.35/4.00  --bmc1_pre_inst_reach_state             false
% 27.35/4.00  --bmc1_out_unsat_core                   false
% 27.35/4.00  --bmc1_aig_witness_out                  false
% 27.35/4.00  --bmc1_verbose                          false
% 27.35/4.00  --bmc1_dump_clauses_tptp                false
% 27.35/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.35/4.00  --bmc1_dump_file                        -
% 27.35/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.35/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.35/4.00  --bmc1_ucm_extend_mode                  1
% 27.35/4.00  --bmc1_ucm_init_mode                    2
% 27.35/4.00  --bmc1_ucm_cone_mode                    none
% 27.35/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.35/4.00  --bmc1_ucm_relax_model                  4
% 27.35/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.35/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.35/4.00  --bmc1_ucm_layered_model                none
% 27.35/4.00  --bmc1_ucm_max_lemma_size               10
% 27.35/4.00  
% 27.35/4.00  ------ AIG Options
% 27.35/4.00  
% 27.35/4.00  --aig_mode                              false
% 27.35/4.00  
% 27.35/4.00  ------ Instantiation Options
% 27.35/4.00  
% 27.35/4.00  --instantiation_flag                    false
% 27.35/4.00  --inst_sos_flag                         false
% 27.35/4.00  --inst_sos_phase                        true
% 27.35/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel_side                     num_symb
% 27.35/4.00  --inst_solver_per_active                1400
% 27.35/4.00  --inst_solver_calls_frac                1.
% 27.35/4.00  --inst_passive_queue_type               priority_queues
% 27.35/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.35/4.00  --inst_passive_queues_freq              [25;2]
% 27.35/4.00  --inst_dismatching                      true
% 27.35/4.00  --inst_eager_unprocessed_to_passive     true
% 27.35/4.00  --inst_prop_sim_given                   true
% 27.35/4.00  --inst_prop_sim_new                     false
% 27.35/4.00  --inst_subs_new                         false
% 27.35/4.00  --inst_eq_res_simp                      false
% 27.35/4.00  --inst_subs_given                       false
% 27.35/4.00  --inst_orphan_elimination               true
% 27.35/4.00  --inst_learning_loop_flag               true
% 27.35/4.00  --inst_learning_start                   3000
% 27.35/4.00  --inst_learning_factor                  2
% 27.35/4.00  --inst_start_prop_sim_after_learn       3
% 27.35/4.00  --inst_sel_renew                        solver
% 27.35/4.00  --inst_lit_activity_flag                true
% 27.35/4.00  --inst_restr_to_given                   false
% 27.35/4.00  --inst_activity_threshold               500
% 27.35/4.00  --inst_out_proof                        true
% 27.35/4.00  
% 27.35/4.00  ------ Resolution Options
% 27.35/4.00  
% 27.35/4.00  --resolution_flag                       false
% 27.35/4.00  --res_lit_sel                           adaptive
% 27.35/4.00  --res_lit_sel_side                      none
% 27.35/4.00  --res_ordering                          kbo
% 27.35/4.00  --res_to_prop_solver                    active
% 27.35/4.00  --res_prop_simpl_new                    false
% 27.35/4.00  --res_prop_simpl_given                  true
% 27.35/4.00  --res_passive_queue_type                priority_queues
% 27.35/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.35/4.00  --res_passive_queues_freq               [15;5]
% 27.35/4.00  --res_forward_subs                      full
% 27.35/4.00  --res_backward_subs                     full
% 27.35/4.00  --res_forward_subs_resolution           true
% 27.35/4.00  --res_backward_subs_resolution          true
% 27.35/4.00  --res_orphan_elimination                true
% 27.35/4.00  --res_time_limit                        2.
% 27.35/4.00  --res_out_proof                         true
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Options
% 27.35/4.00  
% 27.35/4.00  --superposition_flag                    true
% 27.35/4.00  --sup_passive_queue_type                priority_queues
% 27.35/4.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.35/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.35/4.00  --demod_completeness_check              fast
% 27.35/4.00  --demod_use_ground                      true
% 27.35/4.00  --sup_to_prop_solver                    active
% 27.35/4.00  --sup_prop_simpl_new                    false
% 27.35/4.00  --sup_prop_simpl_given                  false
% 27.35/4.00  --sup_fun_splitting                     true
% 27.35/4.00  --sup_smt_interval                      10000
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Simplification Setup
% 27.35/4.00  
% 27.35/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.35/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.35/4.00  --sup_full_triv                         [TrivRules]
% 27.35/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.35/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.35/4.00  --sup_immed_triv                        [TrivRules]
% 27.35/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_immed_bw_main                     []
% 27.35/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.35/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.35/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 27.35/4.00  
% 27.35/4.00  ------ Combination Options
% 27.35/4.00  
% 27.35/4.00  --comb_res_mult                         1
% 27.35/4.00  --comb_sup_mult                         1
% 27.35/4.00  --comb_inst_mult                        1000000
% 27.35/4.00  
% 27.35/4.00  ------ Debug Options
% 27.35/4.00  
% 27.35/4.00  --dbg_backtrace                         false
% 27.35/4.00  --dbg_dump_prop_clauses                 false
% 27.35/4.00  --dbg_dump_prop_clauses_file            -
% 27.35/4.00  --dbg_out_stat                          false
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  ------ Proving...
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  % SZS status Theorem for theBenchmark.p
% 27.35/4.00  
% 27.35/4.00   Resolution empty clause
% 27.35/4.00  
% 27.35/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  fof(f2,axiom,(
% 27.35/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f14,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f2])).
% 27.35/4.00  
% 27.35/4.00  fof(f6,axiom,(
% 27.35/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f18,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.35/4.00    inference(cnf_transformation,[],[f6])).
% 27.35/4.00  
% 27.35/4.00  fof(f21,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.35/4.00    inference(definition_unfolding,[],[f14,f18,f18])).
% 27.35/4.00  
% 27.35/4.00  fof(f1,axiom,(
% 27.35/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f13,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f1])).
% 27.35/4.00  
% 27.35/4.00  fof(f7,axiom,(
% 27.35/4.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f19,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 27.35/4.00    inference(cnf_transformation,[],[f7])).
% 27.35/4.00  
% 27.35/4.00  fof(f22,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 27.35/4.00    inference(definition_unfolding,[],[f19,f18])).
% 27.35/4.00  
% 27.35/4.00  fof(f5,axiom,(
% 27.35/4.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f17,plain,(
% 27.35/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f5])).
% 27.35/4.00  
% 27.35/4.00  fof(f4,axiom,(
% 27.35/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f16,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.35/4.00    inference(cnf_transformation,[],[f4])).
% 27.35/4.00  
% 27.35/4.00  fof(f8,conjecture,(
% 27.35/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f9,negated_conjecture,(
% 27.35/4.00    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 27.35/4.00    inference(negated_conjecture,[],[f8])).
% 27.35/4.00  
% 27.35/4.00  fof(f10,plain,(
% 27.35/4.00    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 27.35/4.00    inference(ennf_transformation,[],[f9])).
% 27.35/4.00  
% 27.35/4.00  fof(f11,plain,(
% 27.35/4.00    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 27.35/4.00    introduced(choice_axiom,[])).
% 27.35/4.00  
% 27.35/4.00  fof(f12,plain,(
% 27.35/4.00    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 27.35/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 27.35/4.00  
% 27.35/4.00  fof(f20,plain,(
% 27.35/4.00    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 27.35/4.00    inference(cnf_transformation,[],[f12])).
% 27.35/4.00  
% 27.35/4.00  fof(f3,axiom,(
% 27.35/4.00    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f15,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f3])).
% 27.35/4.00  
% 27.35/4.00  fof(f23,plain,(
% 27.35/4.00    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 27.35/4.00    inference(definition_unfolding,[],[f20,f18,f15,f15])).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f21]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_0,plain,
% 27.35/4.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f13]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 27.35/4.00      inference(cnf_transformation,[],[f22]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_39,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f17]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(cnf_transformation,[],[f16]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_22,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_63,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_39,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_70,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_22,c_63]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_74,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_70]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_94,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X2) = X2 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_74]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_97,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X2) = X2 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_94,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_33,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_141,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_0,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_227,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_97,c_141]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_240,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_39,c_227]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_77,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_70,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_83,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_77]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_283,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_240,c_83]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_81,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_77]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_282,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_240,c_81]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_146,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_70,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_154,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_146,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_284,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X1),X2)) = k2_xboole_0(k4_xboole_0(X1,X1),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_240,c_154]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_286,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X1),X2)) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_284,c_240]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_287,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_286,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_288,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_283,c_287]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_289,plain,
% 27.35/4.00      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_282,c_288]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_290,plain,
% 27.35/4.00      ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
% 27.35/4.00      inference(splitting,
% 27.35/4.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 27.35/4.00                [c_289]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_439,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = sP0_iProver_split ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_283,c_290]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_915,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_439,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_272,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_240,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_450,plain,
% 27.35/4.00      ( k2_xboole_0(X0,sP0_iProver_split) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_272,c_290]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_928,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_915,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1908,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_0,c_928]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2833,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1908,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_673,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k2_xboole_0(X0,sP0_iProver_split) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_290,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_676,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = X0 ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_673,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1806,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_676,c_227]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_26,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2684,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1806,c_26]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_293,plain,
% 27.35/4.00      ( k2_xboole_0(sP0_iProver_split,X0) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_290,c_240]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_438,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_284,c_3,c_290,c_293]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_440,plain,
% 27.35/4.00      ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_439,c_438]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_271,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),X2) = X2 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_240]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_452,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X0)),X2) = X2 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_271,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_617,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X1)),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_452,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_634,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_617,c_452]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_625,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X1)))) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_452,c_81]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_636,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X2,X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_634,c_625]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_639,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = sP0_iProver_split ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_636,c_290]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2692,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_2684,c_440,c_639]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3937,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2833,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4008,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3937,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5413,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X2) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4008,c_26]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5469,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_5413,c_440,c_639]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5,negated_conjecture,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f23]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_0,c_5]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_105328,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_5469,c_21]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_48,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_148,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_48,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50349,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,X3),X0)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_148]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3924,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X0,X1)),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_33,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4018,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3924,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4019,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_4018,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50370,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1))),X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1)))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4019,c_148]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3930,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_154,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4014,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3930,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_20805,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_4014]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21102,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_20805,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_919,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_439,c_227]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_925,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_919,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9024,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_0,c_925]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50576,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_148,c_9024]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2810,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_154,c_1908]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_975,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_639,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_985,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_975,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2058,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_154,c_985]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2082,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_2058,c_154]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2860,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_2810,c_2082]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_34,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_35,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_34,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2092,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_35,c_141]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_302,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_70,c_26]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_436,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = sP0_iProver_split ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_302,c_3,c_290]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_539,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_436,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2201,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2092,c_539]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_32,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1016,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_639,c_32]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1229,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_1016,c_3,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2275,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = sP0_iProver_split ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_2201,c_1229]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3628,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,sP0_iProver_split) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2275,c_2092]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3634,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),sP0_iProver_split)) = X0 ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_3628,c_290,c_440]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3635,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3634,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3644,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_3635]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4473,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X3)) = k4_xboole_0(X0,X3) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3644,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_346,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X2)),X2) = X2 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_26,c_227]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_408,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))),X2) = X2 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_346,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_46230,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X2)),X2) = X2 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4473,c_408]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_46523,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)),X2) = X2 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2860,c_46230]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_46865,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X2)))),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_46523]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3687,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3635,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13077,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_154,c_3687]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13268,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_13077,c_3687]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13269,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X3)))) = k4_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_13268,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_143,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_38405,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2692,c_143]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_38807,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_38405,c_143]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_887,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_48,c_439]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1716,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(sP0_iProver_split,X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_887,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_281,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(X0,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_240,c_77]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_442,plain,
% 27.35/4.00      ( k4_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_281,c_290]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1750,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = sP0_iProver_split ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_1716,c_3,c_442]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2361,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_0,c_1750]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_150,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_74,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_153,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_150,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21494,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),sP0_iProver_split))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2361,c_153]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3966,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2692,c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3990,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_3966,c_439,c_440]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3978,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2692,c_154]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3983,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3978,c_154]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_20552,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3990,c_3983]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_28,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_36,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_28,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3175,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_36,c_439]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_18014,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3175,c_39]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2827,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1908,c_439]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5268,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),sP0_iProver_split) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2827,c_3990]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2047,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_0,c_985]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1936,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_928,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3028,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2047,c_1936]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3064,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3028,c_2047]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5323,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_5268,c_3064]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_18076,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),k2_xboole_0(X1,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_18014,c_5323]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3468,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2833,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2070,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_985,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3276,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2070,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3282,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3276,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3477,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_3468,c_3282]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3959,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2692,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3996,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3959,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_18077,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_18076,c_3477,c_3996]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_20742,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_20552,c_18077]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21718,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),sP0_iProver_split))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_21494,c_20742]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_979,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_639,c_227]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_984,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_979,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9303,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_984,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3010,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2,c_2047]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3071,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3010,c_2047]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4341,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3071,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9310,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_9303,c_4341]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21719,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_21718,c_3,c_9310,c_20742]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_22235,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X1,X0),X3)))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_21719,c_2860]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2837,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1908,c_1750]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21502,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X3),sP0_iProver_split))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2837,c_153]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21698,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X3),sP0_iProver_split))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_21502,c_20742]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_14934,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),sP0_iProver_split) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2837,c_1]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4104,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2827,c_26]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4129,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sP0_iProver_split,X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),sP0_iProver_split),X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_4104,c_2827]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4130,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_4129,c_3,c_293,c_440]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13528,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_4130,c_1229]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_14980,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),sP0_iProver_split) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_14934,c_13528]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21699,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X1,X0),X3)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_21698,c_14980,c_20742]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_22250,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_22235,c_21699]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21908,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_0,c_21719]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_22422,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_0,c_21908]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3019,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_154,c_2047]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3069,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3019,c_2047]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_17729,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3069,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21408,plain,
% 27.35/4.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_17729,c_153]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_22813,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_22422,c_21408]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_38134,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_22813,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_38808,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_38807,c_22250,c_38134]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_47261,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_46865,c_13269,c_38808]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50643,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_50576,c_3,c_47261]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50577,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_148,c_984]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50641,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_50577,c_148]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50642,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X3)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_50641,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50644,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k4_xboole_0(X0,X1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_50643,c_50642]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_51666,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,X0))) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_50370,c_21102,c_50644]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_51697,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,X3),X0)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_50349,c_51666]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_51698,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),X0),k4_xboole_0(X0,X1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_51697,c_50644]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_151,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_33,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4323,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3071,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4380,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_4323,c_3635]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6025,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = X2 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_4380]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_145,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_63,c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_58308,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X3,X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_6025,c_145]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_84,plain,
% 27.35/4.00      ( k2_xboole_0(X0,X0) = X0 ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_77,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3117,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_84,c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3042,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2047,c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3209,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3117,c_3042]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_20037,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),X3) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3209,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_19606,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X3)),X4))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X2,X1),X4)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_17729,c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3120,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X3)),X4))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X4)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_154,c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3208,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X3)),X4))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X4))) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3120,c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_19674,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_19606,c_3208]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_20130,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_20037,c_19674]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_22682,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_21908,c_2692]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_873,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP0_iProver_split) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_450,c_26]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_50244,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP0_iProver_split),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,X1)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_873,c_148]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_317,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_26]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_51723,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),sP0_iProver_split)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X1,X0)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_50244,c_317,c_50644]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_51724,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X1,X0)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_51723,c_145,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_58437,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X0,X1),X2))))),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X1)),X2) ),
% 27.35/4.00      inference(demodulation,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_58308,c_6025,c_20130,c_22682,c_51724]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2798,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2,c_1908]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_942,plain,
% 27.35/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = sP0_iProver_split ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_2,c_639]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1494,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),sP0_iProver_split) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_942,c_2]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1513,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_1494,c_450]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2862,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_2798,c_1513]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4454,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3644,c_2862]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3013,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_33,c_2047]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3070,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_3013,c_2047]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4511,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_4454,c_3070]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13188,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X3))) = k4_xboole_0(k4_xboole_0(X0,X1),X3) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3687,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13228,plain,
% 27.35/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_13188,c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_58438,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X1)),X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_58437,c_4511,c_13228]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_60597,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X3,k4_xboole_0(X0,X1)),X2) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_151,c_151,c_58438]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4304,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_26,c_3071]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4206,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_26,c_2862]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4286,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_4206,c_317]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4394,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_4304,c_317,c_4286]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4395,plain,
% 27.35/4.00      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,X2) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_4394,c_3983]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_61057,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X3)),X2),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_60597,c_4395]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_19471,plain,
% 27.35/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_3,c_17729]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_61158,plain,
% 27.35/4.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3),X1) = k2_xboole_0(k4_xboole_0(X0,X3),X1) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_61057,c_19471]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_105329,plain,
% 27.35/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_105328,c_51698,c_61158]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_105330,plain,
% 27.35/4.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_105329,c_293,c_887]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_106341,plain,
% 27.35/4.00      ( $false ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1,c_105330]) ).
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  ------                               Statistics
% 27.35/4.00  
% 27.35/4.00  ------ General
% 27.35/4.00  
% 27.35/4.00  abstr_ref_over_cycles:                  0
% 27.35/4.00  abstr_ref_under_cycles:                 0
% 27.35/4.00  gc_basic_clause_elim:                   0
% 27.35/4.00  forced_gc_time:                         0
% 27.35/4.00  parsing_time:                           0.008
% 27.35/4.00  unif_index_cands_time:                  0.
% 27.35/4.00  unif_index_add_time:                    0.
% 27.35/4.00  orderings_time:                         0.
% 27.35/4.00  out_proof_time:                         0.013
% 27.35/4.00  total_time:                             3.126
% 27.35/4.00  num_of_symbols:                         38
% 27.35/4.00  num_of_terms:                           175035
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing
% 27.35/4.00  
% 27.35/4.00  num_of_splits:                          0
% 27.35/4.00  num_of_split_atoms:                     3
% 27.35/4.00  num_of_reused_defs:                     0
% 27.35/4.00  num_eq_ax_congr_red:                    0
% 27.35/4.00  num_of_sem_filtered_clauses:            0
% 27.35/4.00  num_of_subtypes:                        0
% 27.35/4.00  monotx_restored_types:                  0
% 27.35/4.00  sat_num_of_epr_types:                   0
% 27.35/4.00  sat_num_of_non_cyclic_types:            0
% 27.35/4.00  sat_guarded_non_collapsed_types:        0
% 27.35/4.00  num_pure_diseq_elim:                    0
% 27.35/4.00  simp_replaced_by:                       0
% 27.35/4.00  res_preprocessed:                       16
% 27.35/4.00  prep_upred:                             0
% 27.35/4.00  prep_unflattend:                        0
% 27.35/4.00  smt_new_axioms:                         0
% 27.35/4.00  pred_elim_cands:                        0
% 27.35/4.00  pred_elim:                              0
% 27.35/4.00  pred_elim_cl:                           0
% 27.35/4.00  pred_elim_cycles:                       0
% 27.35/4.00  merged_defs:                            0
% 27.35/4.00  merged_defs_ncl:                        0
% 27.35/4.00  bin_hyper_res:                          0
% 27.35/4.00  prep_cycles:                            2
% 27.35/4.00  pred_elim_time:                         0.
% 27.35/4.00  splitting_time:                         0.
% 27.35/4.00  sem_filter_time:                        0.
% 27.35/4.00  monotx_time:                            0.
% 27.35/4.00  subtype_inf_time:                       0.
% 27.35/4.00  
% 27.35/4.00  ------ Problem properties
% 27.35/4.00  
% 27.35/4.00  clauses:                                6
% 27.35/4.00  conjectures:                            1
% 27.35/4.00  epr:                                    0
% 27.35/4.00  horn:                                   6
% 27.35/4.00  ground:                                 1
% 27.35/4.00  unary:                                  6
% 27.35/4.00  binary:                                 0
% 27.35/4.00  lits:                                   6
% 27.35/4.00  lits_eq:                                6
% 27.35/4.00  fd_pure:                                0
% 27.35/4.00  fd_pseudo:                              0
% 27.35/4.00  fd_cond:                                0
% 27.35/4.00  fd_pseudo_cond:                         0
% 27.35/4.00  ac_symbols:                             1
% 27.35/4.00  
% 27.35/4.00  ------ Propositional Solver
% 27.35/4.00  
% 27.35/4.00  prop_solver_calls:                      13
% 27.35/4.00  prop_fast_solver_calls:                 44
% 27.35/4.00  smt_solver_calls:                       0
% 27.35/4.00  smt_fast_solver_calls:                  0
% 27.35/4.00  prop_num_of_clauses:                    469
% 27.35/4.00  prop_preprocess_simplified:             313
% 27.35/4.00  prop_fo_subsumed:                       0
% 27.35/4.00  prop_solver_time:                       0.
% 27.35/4.00  smt_solver_time:                        0.
% 27.35/4.00  smt_fast_solver_time:                   0.
% 27.35/4.00  prop_fast_solver_time:                  0.
% 27.35/4.00  prop_unsat_core_time:                   0.
% 27.35/4.00  
% 27.35/4.00  ------ QBF
% 27.35/4.00  
% 27.35/4.00  qbf_q_res:                              0
% 27.35/4.00  qbf_num_tautologies:                    0
% 27.35/4.00  qbf_prep_cycles:                        0
% 27.35/4.00  
% 27.35/4.00  ------ BMC1
% 27.35/4.00  
% 27.35/4.00  bmc1_current_bound:                     -1
% 27.35/4.00  bmc1_last_solved_bound:                 -1
% 27.35/4.00  bmc1_unsat_core_size:                   -1
% 27.35/4.00  bmc1_unsat_core_parents_size:           -1
% 27.35/4.00  bmc1_merge_next_fun:                    0
% 27.35/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.35/4.00  
% 27.35/4.00  ------ Instantiation
% 27.35/4.00  
% 27.35/4.00  inst_num_of_clauses:                    0
% 27.35/4.00  inst_num_in_passive:                    0
% 27.35/4.00  inst_num_in_active:                     0
% 27.35/4.00  inst_num_in_unprocessed:                0
% 27.35/4.00  inst_num_of_loops:                      0
% 27.35/4.00  inst_num_of_learning_restarts:          0
% 27.35/4.00  inst_num_moves_active_passive:          0
% 27.35/4.00  inst_lit_activity:                      0
% 27.35/4.00  inst_lit_activity_moves:                0
% 27.35/4.00  inst_num_tautologies:                   0
% 27.35/4.00  inst_num_prop_implied:                  0
% 27.35/4.00  inst_num_existing_simplified:           0
% 27.35/4.00  inst_num_eq_res_simplified:             0
% 27.35/4.00  inst_num_child_elim:                    0
% 27.35/4.00  inst_num_of_dismatching_blockings:      0
% 27.35/4.00  inst_num_of_non_proper_insts:           0
% 27.35/4.00  inst_num_of_duplicates:                 0
% 27.35/4.00  inst_inst_num_from_inst_to_res:         0
% 27.35/4.00  inst_dismatching_checking_time:         0.
% 27.35/4.00  
% 27.35/4.00  ------ Resolution
% 27.35/4.00  
% 27.35/4.00  res_num_of_clauses:                     0
% 27.35/4.00  res_num_in_passive:                     0
% 27.35/4.00  res_num_in_active:                      0
% 27.35/4.00  res_num_of_loops:                       18
% 27.35/4.00  res_forward_subset_subsumed:            0
% 27.35/4.00  res_backward_subset_subsumed:           0
% 27.35/4.00  res_forward_subsumed:                   0
% 27.35/4.00  res_backward_subsumed:                  0
% 27.35/4.00  res_forward_subsumption_resolution:     0
% 27.35/4.00  res_backward_subsumption_resolution:    0
% 27.35/4.00  res_clause_to_clause_subsumption:       332435
% 27.35/4.00  res_orphan_elimination:                 0
% 27.35/4.00  res_tautology_del:                      0
% 27.35/4.00  res_num_eq_res_simplified:              0
% 27.35/4.00  res_num_sel_changes:                    0
% 27.35/4.00  res_moves_from_active_to_pass:          0
% 27.35/4.00  
% 27.35/4.00  ------ Superposition
% 27.35/4.00  
% 27.35/4.00  sup_time_total:                         0.
% 27.35/4.00  sup_time_generating:                    0.
% 27.35/4.00  sup_time_sim_full:                      0.
% 27.35/4.00  sup_time_sim_immed:                     0.
% 27.35/4.00  
% 27.35/4.00  sup_num_of_clauses:                     9441
% 27.35/4.00  sup_num_in_active:                      224
% 27.35/4.00  sup_num_in_passive:                     9217
% 27.35/4.00  sup_num_of_loops:                       281
% 27.35/4.00  sup_fw_superposition:                   36343
% 27.35/4.00  sup_bw_superposition:                   29310
% 27.35/4.00  sup_immediate_simplified:               34985
% 27.35/4.00  sup_given_eliminated:                   10
% 27.35/4.00  comparisons_done:                       0
% 27.35/4.00  comparisons_avoided:                    0
% 27.35/4.00  
% 27.35/4.00  ------ Simplifications
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  sim_fw_subset_subsumed:                 0
% 27.35/4.00  sim_bw_subset_subsumed:                 0
% 27.35/4.00  sim_fw_subsumed:                        4402
% 27.35/4.00  sim_bw_subsumed:                        125
% 27.35/4.00  sim_fw_subsumption_res:                 0
% 27.35/4.00  sim_bw_subsumption_res:                 0
% 27.35/4.00  sim_tautology_del:                      0
% 27.35/4.00  sim_eq_tautology_del:                   10603
% 27.35/4.00  sim_eq_res_simp:                        0
% 27.35/4.00  sim_fw_demodulated:                     26196
% 27.35/4.00  sim_bw_demodulated:                     319
% 27.35/4.00  sim_light_normalised:                   13499
% 27.35/4.00  sim_joinable_taut:                      370
% 27.35/4.00  sim_joinable_simp:                      0
% 27.35/4.00  sim_ac_normalised:                      0
% 27.35/4.00  sim_smt_subsumption:                    0
% 27.35/4.00  
%------------------------------------------------------------------------------
