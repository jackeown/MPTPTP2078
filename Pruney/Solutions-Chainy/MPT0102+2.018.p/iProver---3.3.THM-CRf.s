%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:05 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :  158 (12952 expanded)
%              Number of clauses        :  124 (4221 expanded)
%              Number of leaves         :   13 (3839 expanded)
%              Depth                    :   32
%              Number of atoms          :  159 (12953 expanded)
%              Number of equality atoms :  158 (12952 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f24,f24])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f19,f24])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f26,f19])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f28,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f28,f24,f19,f19])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19,f24])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_44,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_82,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44,c_6])).

cnf(c_252,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44,c_82])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_267,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_252,c_5])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_29,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_4])).

cnf(c_46,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_29])).

cnf(c_48,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_46,c_4])).

cnf(c_268,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_267,c_29,c_48])).

cnf(c_271,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_268,c_44])).

cnf(c_273,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_271,c_268])).

cnf(c_330,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_273,c_5])).

cnf(c_336,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_330,c_268])).

cnf(c_434,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_336])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_30,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_9])).

cnf(c_44360,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_434,c_30])).

cnf(c_2,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_99,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_79,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_18751,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_99,c_79])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_430,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_336])).

cnf(c_464,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_79,c_430])).

cnf(c_506,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_464,c_5])).

cnf(c_517,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_506,c_5,c_268])).

cnf(c_756,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_517])).

cnf(c_18807,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_18751,c_3,c_756])).

cnf(c_491,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_464])).

cnf(c_109,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_128,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_109,c_5])).

cnf(c_509,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_464,c_8])).

cnf(c_510,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_464,c_1])).

cnf(c_513,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_510,c_3,c_5])).

cnf(c_514,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_509,c_513])).

cnf(c_515,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_514,c_3,c_6])).

cnf(c_436,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_79,c_336])).

cnf(c_865,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_436,c_1])).

cnf(c_60,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_599,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_60])).

cnf(c_870,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_865,c_3,c_599])).

cnf(c_33722,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_128,c_128,c_430,c_515,c_870])).

cnf(c_33796,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_491,c_33722])).

cnf(c_69,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_2575,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_464,c_69])).

cnf(c_2774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2575,c_5])).

cnf(c_2775,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_2774,c_3,c_5])).

cnf(c_70,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_74,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_70,c_5])).

cnf(c_7320,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_74,c_69])).

cnf(c_770,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_517])).

cnf(c_501,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_464,c_8])).

cnf(c_31,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_522,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_501,c_5,c_31])).

cnf(c_523,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_522,c_3,c_6])).

cnf(c_548,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_523])).

cnf(c_1383,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_770,c_548])).

cnf(c_1427,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1383,c_5])).

cnf(c_1428,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1427,c_3])).

cnf(c_447,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_336,c_8])).

cnf(c_95,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_449,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_447,c_3,c_95])).

cnf(c_705,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_449])).

cnf(c_1214,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_705,c_0])).

cnf(c_445,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_336,c_5])).

cnf(c_66,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_75,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_66,c_5])).

cnf(c_450,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_445,c_75,c_268])).

cnf(c_1206,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_705,c_450])).

cnf(c_5567,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1214,c_1206])).

cnf(c_941,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_450,c_5])).

cnf(c_947,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_941,c_75,c_268])).

cnf(c_4154,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_705,c_947])).

cnf(c_5748,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5567,c_75,c_705,c_4154])).

cnf(c_18378,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1428,c_5748])).

cnf(c_29781,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X2))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18378,c_69])).

cnf(c_331,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_273,c_8])).

cnf(c_333,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_331,c_273])).

cnf(c_334,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0) = k2_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_333,c_4])).

cnf(c_335,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_334,c_31])).

cnf(c_7114,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_335,c_74])).

cnf(c_247,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_82])).

cnf(c_287,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_247,c_3,c_268])).

cnf(c_7469,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7114,c_287])).

cnf(c_8265,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_7469,c_8])).

cnf(c_8283,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_8265,c_3,c_5,c_523])).

cnf(c_8284,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_8283,c_3,c_31,c_464])).

cnf(c_8297,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_8284])).

cnf(c_408,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_79,c_0])).

cnf(c_8818,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X2,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8297,c_408])).

cnf(c_8844,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8818,c_3,c_5,c_273])).

cnf(c_8845,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_8844,c_75,c_705])).

cnf(c_21598,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_8845,c_513])).

cnf(c_1209,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_705,c_336])).

cnf(c_361,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_287])).

cnf(c_22755,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1209,c_361])).

cnf(c_23019,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22755,c_3])).

cnf(c_23220,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_23019,c_548])).

cnf(c_1626,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_1209,c_60])).

cnf(c_1637,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
    inference(demodulation,[status(thm)],[c_1626,c_1209])).

cnf(c_1638,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_1637,c_4,c_5,c_31])).

cnf(c_7760,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1638,c_5])).

cnf(c_23359,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k1_xboole_0)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_23220,c_7760])).

cnf(c_23360,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
    inference(light_normalisation,[status(thm)],[c_23359,c_3])).

cnf(c_24100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_23360,c_60])).

cnf(c_24152,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_24100,c_4,c_336])).

cnf(c_24305,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_24152,c_1])).

cnf(c_24370,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_24305,c_8297])).

cnf(c_27234,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))),X0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_8297,c_24370])).

cnf(c_466,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_430,c_79])).

cnf(c_483,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_466,c_4])).

cnf(c_24196,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_24152,c_483])).

cnf(c_24792,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_5,c_24196])).

cnf(c_27388,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_27234,c_24792])).

cnf(c_29816,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_29781,c_21598,c_27388])).

cnf(c_34290,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_33796,c_2775,c_7320,c_29816])).

cnf(c_44361,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_44360,c_18807,c_34290])).

cnf(c_45209,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_44361])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.50/2.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.50/2.02  
% 11.50/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.50/2.02  
% 11.50/2.02  ------  iProver source info
% 11.50/2.02  
% 11.50/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.50/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.50/2.02  git: non_committed_changes: false
% 11.50/2.02  git: last_make_outside_of_git: false
% 11.50/2.02  
% 11.50/2.02  ------ 
% 11.50/2.02  
% 11.50/2.02  ------ Input Options
% 11.50/2.02  
% 11.50/2.02  --out_options                           all
% 11.50/2.02  --tptp_safe_out                         true
% 11.50/2.02  --problem_path                          ""
% 11.50/2.02  --include_path                          ""
% 11.50/2.02  --clausifier                            res/vclausify_rel
% 11.50/2.02  --clausifier_options                    --mode clausify
% 11.50/2.02  --stdin                                 false
% 11.50/2.02  --stats_out                             all
% 11.50/2.02  
% 11.50/2.02  ------ General Options
% 11.50/2.02  
% 11.50/2.02  --fof                                   false
% 11.50/2.02  --time_out_real                         305.
% 11.50/2.02  --time_out_virtual                      -1.
% 11.50/2.02  --symbol_type_check                     false
% 11.50/2.02  --clausify_out                          false
% 11.50/2.02  --sig_cnt_out                           false
% 11.50/2.02  --trig_cnt_out                          false
% 11.50/2.02  --trig_cnt_out_tolerance                1.
% 11.50/2.02  --trig_cnt_out_sk_spl                   false
% 11.50/2.02  --abstr_cl_out                          false
% 11.50/2.02  
% 11.50/2.02  ------ Global Options
% 11.50/2.02  
% 11.50/2.02  --schedule                              default
% 11.50/2.02  --add_important_lit                     false
% 11.50/2.02  --prop_solver_per_cl                    1000
% 11.50/2.02  --min_unsat_core                        false
% 11.50/2.02  --soft_assumptions                      false
% 11.50/2.02  --soft_lemma_size                       3
% 11.50/2.02  --prop_impl_unit_size                   0
% 11.50/2.02  --prop_impl_unit                        []
% 11.50/2.02  --share_sel_clauses                     true
% 11.50/2.02  --reset_solvers                         false
% 11.50/2.02  --bc_imp_inh                            [conj_cone]
% 11.50/2.02  --conj_cone_tolerance                   3.
% 11.50/2.02  --extra_neg_conj                        none
% 11.50/2.02  --large_theory_mode                     true
% 11.50/2.02  --prolific_symb_bound                   200
% 11.50/2.02  --lt_threshold                          2000
% 11.50/2.02  --clause_weak_htbl                      true
% 11.50/2.02  --gc_record_bc_elim                     false
% 11.50/2.02  
% 11.50/2.02  ------ Preprocessing Options
% 11.50/2.02  
% 11.50/2.02  --preprocessing_flag                    true
% 11.50/2.02  --time_out_prep_mult                    0.1
% 11.50/2.02  --splitting_mode                        input
% 11.50/2.02  --splitting_grd                         true
% 11.50/2.02  --splitting_cvd                         false
% 11.50/2.02  --splitting_cvd_svl                     false
% 11.50/2.02  --splitting_nvd                         32
% 11.50/2.02  --sub_typing                            true
% 11.50/2.02  --prep_gs_sim                           true
% 11.50/2.02  --prep_unflatten                        true
% 11.50/2.02  --prep_res_sim                          true
% 11.50/2.02  --prep_upred                            true
% 11.50/2.02  --prep_sem_filter                       exhaustive
% 11.50/2.02  --prep_sem_filter_out                   false
% 11.50/2.02  --pred_elim                             true
% 11.50/2.02  --res_sim_input                         true
% 11.50/2.02  --eq_ax_congr_red                       true
% 11.50/2.02  --pure_diseq_elim                       true
% 11.50/2.02  --brand_transform                       false
% 11.50/2.02  --non_eq_to_eq                          false
% 11.50/2.02  --prep_def_merge                        true
% 11.50/2.02  --prep_def_merge_prop_impl              false
% 11.50/2.02  --prep_def_merge_mbd                    true
% 11.50/2.02  --prep_def_merge_tr_red                 false
% 11.50/2.02  --prep_def_merge_tr_cl                  false
% 11.50/2.02  --smt_preprocessing                     true
% 11.50/2.02  --smt_ac_axioms                         fast
% 11.50/2.02  --preprocessed_out                      false
% 11.50/2.02  --preprocessed_stats                    false
% 11.50/2.02  
% 11.50/2.02  ------ Abstraction refinement Options
% 11.50/2.02  
% 11.50/2.02  --abstr_ref                             []
% 11.50/2.02  --abstr_ref_prep                        false
% 11.50/2.02  --abstr_ref_until_sat                   false
% 11.50/2.02  --abstr_ref_sig_restrict                funpre
% 11.50/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.50/2.02  --abstr_ref_under                       []
% 11.50/2.02  
% 11.50/2.02  ------ SAT Options
% 11.50/2.02  
% 11.50/2.02  --sat_mode                              false
% 11.50/2.02  --sat_fm_restart_options                ""
% 11.50/2.02  --sat_gr_def                            false
% 11.50/2.02  --sat_epr_types                         true
% 11.50/2.02  --sat_non_cyclic_types                  false
% 11.50/2.02  --sat_finite_models                     false
% 11.50/2.02  --sat_fm_lemmas                         false
% 11.50/2.02  --sat_fm_prep                           false
% 11.50/2.02  --sat_fm_uc_incr                        true
% 11.50/2.02  --sat_out_model                         small
% 11.50/2.02  --sat_out_clauses                       false
% 11.50/2.02  
% 11.50/2.02  ------ QBF Options
% 11.50/2.02  
% 11.50/2.02  --qbf_mode                              false
% 11.50/2.02  --qbf_elim_univ                         false
% 11.50/2.02  --qbf_dom_inst                          none
% 11.50/2.02  --qbf_dom_pre_inst                      false
% 11.50/2.02  --qbf_sk_in                             false
% 11.50/2.02  --qbf_pred_elim                         true
% 11.50/2.02  --qbf_split                             512
% 11.50/2.02  
% 11.50/2.02  ------ BMC1 Options
% 11.50/2.02  
% 11.50/2.02  --bmc1_incremental                      false
% 11.50/2.02  --bmc1_axioms                           reachable_all
% 11.50/2.02  --bmc1_min_bound                        0
% 11.50/2.02  --bmc1_max_bound                        -1
% 11.50/2.02  --bmc1_max_bound_default                -1
% 11.50/2.02  --bmc1_symbol_reachability              true
% 11.50/2.02  --bmc1_property_lemmas                  false
% 11.50/2.02  --bmc1_k_induction                      false
% 11.50/2.02  --bmc1_non_equiv_states                 false
% 11.50/2.02  --bmc1_deadlock                         false
% 11.50/2.02  --bmc1_ucm                              false
% 11.50/2.02  --bmc1_add_unsat_core                   none
% 11.50/2.02  --bmc1_unsat_core_children              false
% 11.50/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.50/2.02  --bmc1_out_stat                         full
% 11.50/2.02  --bmc1_ground_init                      false
% 11.50/2.02  --bmc1_pre_inst_next_state              false
% 11.50/2.02  --bmc1_pre_inst_state                   false
% 11.50/2.02  --bmc1_pre_inst_reach_state             false
% 11.50/2.02  --bmc1_out_unsat_core                   false
% 11.50/2.02  --bmc1_aig_witness_out                  false
% 11.50/2.02  --bmc1_verbose                          false
% 11.50/2.02  --bmc1_dump_clauses_tptp                false
% 11.50/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.50/2.02  --bmc1_dump_file                        -
% 11.50/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.50/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.50/2.02  --bmc1_ucm_extend_mode                  1
% 11.50/2.02  --bmc1_ucm_init_mode                    2
% 11.50/2.02  --bmc1_ucm_cone_mode                    none
% 11.50/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.50/2.02  --bmc1_ucm_relax_model                  4
% 11.50/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.50/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.50/2.02  --bmc1_ucm_layered_model                none
% 11.50/2.02  --bmc1_ucm_max_lemma_size               10
% 11.50/2.02  
% 11.50/2.02  ------ AIG Options
% 11.50/2.02  
% 11.50/2.02  --aig_mode                              false
% 11.50/2.02  
% 11.50/2.02  ------ Instantiation Options
% 11.50/2.02  
% 11.50/2.02  --instantiation_flag                    true
% 11.50/2.02  --inst_sos_flag                         false
% 11.50/2.02  --inst_sos_phase                        true
% 11.50/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.50/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.50/2.02  --inst_lit_sel_side                     num_symb
% 11.50/2.02  --inst_solver_per_active                1400
% 11.50/2.02  --inst_solver_calls_frac                1.
% 11.50/2.02  --inst_passive_queue_type               priority_queues
% 11.50/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.50/2.02  --inst_passive_queues_freq              [25;2]
% 11.50/2.02  --inst_dismatching                      true
% 11.50/2.02  --inst_eager_unprocessed_to_passive     true
% 11.50/2.02  --inst_prop_sim_given                   true
% 11.50/2.02  --inst_prop_sim_new                     false
% 11.50/2.02  --inst_subs_new                         false
% 11.50/2.02  --inst_eq_res_simp                      false
% 11.50/2.02  --inst_subs_given                       false
% 11.50/2.02  --inst_orphan_elimination               true
% 11.50/2.02  --inst_learning_loop_flag               true
% 11.50/2.02  --inst_learning_start                   3000
% 11.50/2.02  --inst_learning_factor                  2
% 11.50/2.02  --inst_start_prop_sim_after_learn       3
% 11.50/2.02  --inst_sel_renew                        solver
% 11.50/2.02  --inst_lit_activity_flag                true
% 11.50/2.02  --inst_restr_to_given                   false
% 11.50/2.02  --inst_activity_threshold               500
% 11.50/2.02  --inst_out_proof                        true
% 11.50/2.02  
% 11.50/2.02  ------ Resolution Options
% 11.50/2.02  
% 11.50/2.02  --resolution_flag                       true
% 11.50/2.02  --res_lit_sel                           adaptive
% 11.50/2.02  --res_lit_sel_side                      none
% 11.50/2.02  --res_ordering                          kbo
% 11.50/2.02  --res_to_prop_solver                    active
% 11.50/2.02  --res_prop_simpl_new                    false
% 11.50/2.02  --res_prop_simpl_given                  true
% 11.50/2.02  --res_passive_queue_type                priority_queues
% 11.50/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.50/2.02  --res_passive_queues_freq               [15;5]
% 11.50/2.02  --res_forward_subs                      full
% 11.50/2.02  --res_backward_subs                     full
% 11.50/2.02  --res_forward_subs_resolution           true
% 11.50/2.02  --res_backward_subs_resolution          true
% 11.50/2.02  --res_orphan_elimination                true
% 11.50/2.02  --res_time_limit                        2.
% 11.50/2.02  --res_out_proof                         true
% 11.50/2.02  
% 11.50/2.02  ------ Superposition Options
% 11.50/2.02  
% 11.50/2.02  --superposition_flag                    true
% 11.50/2.02  --sup_passive_queue_type                priority_queues
% 11.50/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.50/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.50/2.02  --demod_completeness_check              fast
% 11.50/2.02  --demod_use_ground                      true
% 11.50/2.02  --sup_to_prop_solver                    passive
% 11.50/2.02  --sup_prop_simpl_new                    true
% 11.50/2.02  --sup_prop_simpl_given                  true
% 11.50/2.02  --sup_fun_splitting                     false
% 11.50/2.02  --sup_smt_interval                      50000
% 11.50/2.02  
% 11.50/2.02  ------ Superposition Simplification Setup
% 11.50/2.02  
% 11.50/2.02  --sup_indices_passive                   []
% 11.50/2.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.50/2.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.50/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.50/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.50/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.50/2.02  --sup_full_bw                           [BwDemod]
% 11.50/2.02  --sup_immed_triv                        [TrivRules]
% 11.50/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.50/2.02  --sup_immed_bw_main                     []
% 11.50/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.50/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.50/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.50/2.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.50/2.02  
% 11.50/2.02  ------ Combination Options
% 11.50/2.02  
% 11.50/2.02  --comb_res_mult                         3
% 11.50/2.02  --comb_sup_mult                         2
% 11.50/2.02  --comb_inst_mult                        10
% 11.50/2.02  
% 11.50/2.02  ------ Debug Options
% 11.50/2.02  
% 11.50/2.02  --dbg_backtrace                         false
% 11.50/2.02  --dbg_dump_prop_clauses                 false
% 11.50/2.02  --dbg_dump_prop_clauses_file            -
% 11.50/2.02  --dbg_out_stat                          false
% 11.50/2.02  ------ Parsing...
% 11.50/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.50/2.02  
% 11.50/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.50/2.02  
% 11.50/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.50/2.02  
% 11.50/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.50/2.02  ------ Proving...
% 11.50/2.02  ------ Problem Properties 
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  clauses                                 10
% 11.50/2.02  conjectures                             1
% 11.50/2.02  EPR                                     0
% 11.50/2.02  Horn                                    10
% 11.50/2.02  unary                                   10
% 11.50/2.02  binary                                  0
% 11.50/2.02  lits                                    10
% 11.50/2.02  lits eq                                 10
% 11.50/2.02  fd_pure                                 0
% 11.50/2.02  fd_pseudo                               0
% 11.50/2.02  fd_cond                                 0
% 11.50/2.02  fd_pseudo_cond                          0
% 11.50/2.02  AC symbols                              0
% 11.50/2.02  
% 11.50/2.02  ------ Schedule UEQ
% 11.50/2.02  
% 11.50/2.02  ------ pure equality problem: resolution off 
% 11.50/2.02  
% 11.50/2.02  ------ Option_UEQ Time Limit: Unbounded
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  ------ 
% 11.50/2.02  Current options:
% 11.50/2.02  ------ 
% 11.50/2.02  
% 11.50/2.02  ------ Input Options
% 11.50/2.02  
% 11.50/2.02  --out_options                           all
% 11.50/2.02  --tptp_safe_out                         true
% 11.50/2.02  --problem_path                          ""
% 11.50/2.02  --include_path                          ""
% 11.50/2.02  --clausifier                            res/vclausify_rel
% 11.50/2.02  --clausifier_options                    --mode clausify
% 11.50/2.02  --stdin                                 false
% 11.50/2.02  --stats_out                             all
% 11.50/2.02  
% 11.50/2.02  ------ General Options
% 11.50/2.02  
% 11.50/2.02  --fof                                   false
% 11.50/2.02  --time_out_real                         305.
% 11.50/2.02  --time_out_virtual                      -1.
% 11.50/2.02  --symbol_type_check                     false
% 11.50/2.02  --clausify_out                          false
% 11.50/2.02  --sig_cnt_out                           false
% 11.50/2.02  --trig_cnt_out                          false
% 11.50/2.02  --trig_cnt_out_tolerance                1.
% 11.50/2.02  --trig_cnt_out_sk_spl                   false
% 11.50/2.02  --abstr_cl_out                          false
% 11.50/2.02  
% 11.50/2.02  ------ Global Options
% 11.50/2.02  
% 11.50/2.02  --schedule                              default
% 11.50/2.02  --add_important_lit                     false
% 11.50/2.02  --prop_solver_per_cl                    1000
% 11.50/2.02  --min_unsat_core                        false
% 11.50/2.02  --soft_assumptions                      false
% 11.50/2.02  --soft_lemma_size                       3
% 11.50/2.02  --prop_impl_unit_size                   0
% 11.50/2.02  --prop_impl_unit                        []
% 11.50/2.02  --share_sel_clauses                     true
% 11.50/2.02  --reset_solvers                         false
% 11.50/2.02  --bc_imp_inh                            [conj_cone]
% 11.50/2.02  --conj_cone_tolerance                   3.
% 11.50/2.02  --extra_neg_conj                        none
% 11.50/2.02  --large_theory_mode                     true
% 11.50/2.02  --prolific_symb_bound                   200
% 11.50/2.02  --lt_threshold                          2000
% 11.50/2.02  --clause_weak_htbl                      true
% 11.50/2.02  --gc_record_bc_elim                     false
% 11.50/2.02  
% 11.50/2.02  ------ Preprocessing Options
% 11.50/2.02  
% 11.50/2.02  --preprocessing_flag                    true
% 11.50/2.02  --time_out_prep_mult                    0.1
% 11.50/2.02  --splitting_mode                        input
% 11.50/2.02  --splitting_grd                         true
% 11.50/2.02  --splitting_cvd                         false
% 11.50/2.02  --splitting_cvd_svl                     false
% 11.50/2.02  --splitting_nvd                         32
% 11.50/2.02  --sub_typing                            true
% 11.50/2.02  --prep_gs_sim                           true
% 11.50/2.02  --prep_unflatten                        true
% 11.50/2.02  --prep_res_sim                          true
% 11.50/2.02  --prep_upred                            true
% 11.50/2.02  --prep_sem_filter                       exhaustive
% 11.50/2.02  --prep_sem_filter_out                   false
% 11.50/2.02  --pred_elim                             true
% 11.50/2.02  --res_sim_input                         true
% 11.50/2.02  --eq_ax_congr_red                       true
% 11.50/2.02  --pure_diseq_elim                       true
% 11.50/2.02  --brand_transform                       false
% 11.50/2.02  --non_eq_to_eq                          false
% 11.50/2.02  --prep_def_merge                        true
% 11.50/2.02  --prep_def_merge_prop_impl              false
% 11.50/2.02  --prep_def_merge_mbd                    true
% 11.50/2.02  --prep_def_merge_tr_red                 false
% 11.50/2.02  --prep_def_merge_tr_cl                  false
% 11.50/2.02  --smt_preprocessing                     true
% 11.50/2.02  --smt_ac_axioms                         fast
% 11.50/2.02  --preprocessed_out                      false
% 11.50/2.02  --preprocessed_stats                    false
% 11.50/2.02  
% 11.50/2.02  ------ Abstraction refinement Options
% 11.50/2.02  
% 11.50/2.02  --abstr_ref                             []
% 11.50/2.02  --abstr_ref_prep                        false
% 11.50/2.02  --abstr_ref_until_sat                   false
% 11.50/2.02  --abstr_ref_sig_restrict                funpre
% 11.50/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.50/2.02  --abstr_ref_under                       []
% 11.50/2.02  
% 11.50/2.02  ------ SAT Options
% 11.50/2.02  
% 11.50/2.02  --sat_mode                              false
% 11.50/2.02  --sat_fm_restart_options                ""
% 11.50/2.02  --sat_gr_def                            false
% 11.50/2.02  --sat_epr_types                         true
% 11.50/2.02  --sat_non_cyclic_types                  false
% 11.50/2.02  --sat_finite_models                     false
% 11.50/2.02  --sat_fm_lemmas                         false
% 11.50/2.02  --sat_fm_prep                           false
% 11.50/2.02  --sat_fm_uc_incr                        true
% 11.50/2.02  --sat_out_model                         small
% 11.50/2.02  --sat_out_clauses                       false
% 11.50/2.02  
% 11.50/2.02  ------ QBF Options
% 11.50/2.02  
% 11.50/2.02  --qbf_mode                              false
% 11.50/2.02  --qbf_elim_univ                         false
% 11.50/2.02  --qbf_dom_inst                          none
% 11.50/2.02  --qbf_dom_pre_inst                      false
% 11.50/2.02  --qbf_sk_in                             false
% 11.50/2.02  --qbf_pred_elim                         true
% 11.50/2.02  --qbf_split                             512
% 11.50/2.02  
% 11.50/2.02  ------ BMC1 Options
% 11.50/2.02  
% 11.50/2.02  --bmc1_incremental                      false
% 11.50/2.02  --bmc1_axioms                           reachable_all
% 11.50/2.02  --bmc1_min_bound                        0
% 11.50/2.02  --bmc1_max_bound                        -1
% 11.50/2.02  --bmc1_max_bound_default                -1
% 11.50/2.02  --bmc1_symbol_reachability              true
% 11.50/2.02  --bmc1_property_lemmas                  false
% 11.50/2.02  --bmc1_k_induction                      false
% 11.50/2.02  --bmc1_non_equiv_states                 false
% 11.50/2.02  --bmc1_deadlock                         false
% 11.50/2.02  --bmc1_ucm                              false
% 11.50/2.02  --bmc1_add_unsat_core                   none
% 11.50/2.02  --bmc1_unsat_core_children              false
% 11.50/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.50/2.02  --bmc1_out_stat                         full
% 11.50/2.02  --bmc1_ground_init                      false
% 11.50/2.02  --bmc1_pre_inst_next_state              false
% 11.50/2.02  --bmc1_pre_inst_state                   false
% 11.50/2.02  --bmc1_pre_inst_reach_state             false
% 11.50/2.02  --bmc1_out_unsat_core                   false
% 11.50/2.02  --bmc1_aig_witness_out                  false
% 11.50/2.02  --bmc1_verbose                          false
% 11.50/2.02  --bmc1_dump_clauses_tptp                false
% 11.50/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.50/2.02  --bmc1_dump_file                        -
% 11.50/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.50/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.50/2.02  --bmc1_ucm_extend_mode                  1
% 11.50/2.02  --bmc1_ucm_init_mode                    2
% 11.50/2.02  --bmc1_ucm_cone_mode                    none
% 11.50/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.50/2.02  --bmc1_ucm_relax_model                  4
% 11.50/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.50/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.50/2.02  --bmc1_ucm_layered_model                none
% 11.50/2.02  --bmc1_ucm_max_lemma_size               10
% 11.50/2.02  
% 11.50/2.02  ------ AIG Options
% 11.50/2.02  
% 11.50/2.02  --aig_mode                              false
% 11.50/2.02  
% 11.50/2.02  ------ Instantiation Options
% 11.50/2.02  
% 11.50/2.02  --instantiation_flag                    false
% 11.50/2.02  --inst_sos_flag                         false
% 11.50/2.02  --inst_sos_phase                        true
% 11.50/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.50/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.50/2.02  --inst_lit_sel_side                     num_symb
% 11.50/2.02  --inst_solver_per_active                1400
% 11.50/2.02  --inst_solver_calls_frac                1.
% 11.50/2.02  --inst_passive_queue_type               priority_queues
% 11.50/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.50/2.02  --inst_passive_queues_freq              [25;2]
% 11.50/2.02  --inst_dismatching                      true
% 11.50/2.02  --inst_eager_unprocessed_to_passive     true
% 11.50/2.02  --inst_prop_sim_given                   true
% 11.50/2.02  --inst_prop_sim_new                     false
% 11.50/2.02  --inst_subs_new                         false
% 11.50/2.02  --inst_eq_res_simp                      false
% 11.50/2.02  --inst_subs_given                       false
% 11.50/2.02  --inst_orphan_elimination               true
% 11.50/2.02  --inst_learning_loop_flag               true
% 11.50/2.02  --inst_learning_start                   3000
% 11.50/2.02  --inst_learning_factor                  2
% 11.50/2.02  --inst_start_prop_sim_after_learn       3
% 11.50/2.02  --inst_sel_renew                        solver
% 11.50/2.02  --inst_lit_activity_flag                true
% 11.50/2.02  --inst_restr_to_given                   false
% 11.50/2.02  --inst_activity_threshold               500
% 11.50/2.02  --inst_out_proof                        true
% 11.50/2.02  
% 11.50/2.02  ------ Resolution Options
% 11.50/2.02  
% 11.50/2.02  --resolution_flag                       false
% 11.50/2.02  --res_lit_sel                           adaptive
% 11.50/2.02  --res_lit_sel_side                      none
% 11.50/2.02  --res_ordering                          kbo
% 11.50/2.02  --res_to_prop_solver                    active
% 11.50/2.02  --res_prop_simpl_new                    false
% 11.50/2.02  --res_prop_simpl_given                  true
% 11.50/2.02  --res_passive_queue_type                priority_queues
% 11.50/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.50/2.02  --res_passive_queues_freq               [15;5]
% 11.50/2.02  --res_forward_subs                      full
% 11.50/2.02  --res_backward_subs                     full
% 11.50/2.02  --res_forward_subs_resolution           true
% 11.50/2.02  --res_backward_subs_resolution          true
% 11.50/2.02  --res_orphan_elimination                true
% 11.50/2.02  --res_time_limit                        2.
% 11.50/2.02  --res_out_proof                         true
% 11.50/2.02  
% 11.50/2.02  ------ Superposition Options
% 11.50/2.02  
% 11.50/2.02  --superposition_flag                    true
% 11.50/2.02  --sup_passive_queue_type                priority_queues
% 11.50/2.02  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.50/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.50/2.02  --demod_completeness_check              fast
% 11.50/2.02  --demod_use_ground                      true
% 11.50/2.02  --sup_to_prop_solver                    active
% 11.50/2.02  --sup_prop_simpl_new                    false
% 11.50/2.02  --sup_prop_simpl_given                  false
% 11.50/2.02  --sup_fun_splitting                     true
% 11.50/2.02  --sup_smt_interval                      10000
% 11.50/2.02  
% 11.50/2.02  ------ Superposition Simplification Setup
% 11.50/2.02  
% 11.50/2.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.50/2.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.50/2.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.50/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.50/2.02  --sup_full_triv                         [TrivRules]
% 11.50/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.50/2.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.50/2.02  --sup_immed_triv                        [TrivRules]
% 11.50/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/2.02  --sup_immed_bw_main                     []
% 11.50/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.50/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.50/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/2.02  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.50/2.02  
% 11.50/2.02  ------ Combination Options
% 11.50/2.02  
% 11.50/2.02  --comb_res_mult                         1
% 11.50/2.02  --comb_sup_mult                         1
% 11.50/2.02  --comb_inst_mult                        1000000
% 11.50/2.02  
% 11.50/2.02  ------ Debug Options
% 11.50/2.02  
% 11.50/2.02  --dbg_backtrace                         false
% 11.50/2.02  --dbg_dump_prop_clauses                 false
% 11.50/2.02  --dbg_dump_prop_clauses_file            -
% 11.50/2.02  --dbg_out_stat                          false
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  ------ Proving...
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  % SZS status Theorem for theBenchmark.p
% 11.50/2.02  
% 11.50/2.02   Resolution empty clause
% 11.50/2.02  
% 11.50/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.50/2.02  
% 11.50/2.02  fof(f2,axiom,(
% 11.50/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f18,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.50/2.02    inference(cnf_transformation,[],[f2])).
% 11.50/2.02  
% 11.50/2.02  fof(f8,axiom,(
% 11.50/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f24,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.50/2.02    inference(cnf_transformation,[],[f8])).
% 11.50/2.02  
% 11.50/2.02  fof(f29,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.50/2.02    inference(definition_unfolding,[],[f18,f24,f24])).
% 11.50/2.02  
% 11.50/2.02  fof(f11,axiom,(
% 11.50/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f27,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.50/2.02    inference(cnf_transformation,[],[f11])).
% 11.50/2.02  
% 11.50/2.02  fof(f3,axiom,(
% 11.50/2.02    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f19,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.50/2.02    inference(cnf_transformation,[],[f3])).
% 11.50/2.02  
% 11.50/2.02  fof(f33,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.50/2.02    inference(definition_unfolding,[],[f27,f19,f24])).
% 11.50/2.02  
% 11.50/2.02  fof(f6,axiom,(
% 11.50/2.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f22,plain,(
% 11.50/2.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.50/2.02    inference(cnf_transformation,[],[f6])).
% 11.50/2.02  
% 11.50/2.02  fof(f9,axiom,(
% 11.50/2.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f25,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.50/2.02    inference(cnf_transformation,[],[f9])).
% 11.50/2.02  
% 11.50/2.02  fof(f31,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 11.50/2.02    inference(definition_unfolding,[],[f25,f24])).
% 11.50/2.02  
% 11.50/2.02  fof(f7,axiom,(
% 11.50/2.02    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f23,plain,(
% 11.50/2.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.50/2.02    inference(cnf_transformation,[],[f7])).
% 11.50/2.02  
% 11.50/2.02  fof(f10,axiom,(
% 11.50/2.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f26,plain,(
% 11.50/2.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.50/2.02    inference(cnf_transformation,[],[f10])).
% 11.50/2.02  
% 11.50/2.02  fof(f32,plain,(
% 11.50/2.02    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 11.50/2.02    inference(definition_unfolding,[],[f26,f19])).
% 11.50/2.02  
% 11.50/2.02  fof(f1,axiom,(
% 11.50/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f17,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.50/2.02    inference(cnf_transformation,[],[f1])).
% 11.50/2.02  
% 11.50/2.02  fof(f12,conjecture,(
% 11.50/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f13,negated_conjecture,(
% 11.50/2.02    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.50/2.02    inference(negated_conjecture,[],[f12])).
% 11.50/2.02  
% 11.50/2.02  fof(f14,plain,(
% 11.50/2.02    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.50/2.02    inference(ennf_transformation,[],[f13])).
% 11.50/2.02  
% 11.50/2.02  fof(f15,plain,(
% 11.50/2.02    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.50/2.02    introduced(choice_axiom,[])).
% 11.50/2.02  
% 11.50/2.02  fof(f16,plain,(
% 11.50/2.02    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.50/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 11.50/2.02  
% 11.50/2.02  fof(f28,plain,(
% 11.50/2.02    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.50/2.02    inference(cnf_transformation,[],[f16])).
% 11.50/2.02  
% 11.50/2.02  fof(f34,plain,(
% 11.50/2.02    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 11.50/2.02    inference(definition_unfolding,[],[f28,f24,f19,f19])).
% 11.50/2.02  
% 11.50/2.02  fof(f4,axiom,(
% 11.50/2.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f20,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.50/2.02    inference(cnf_transformation,[],[f4])).
% 11.50/2.02  
% 11.50/2.02  fof(f30,plain,(
% 11.50/2.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.50/2.02    inference(definition_unfolding,[],[f20,f19,f24])).
% 11.50/2.02  
% 11.50/2.02  fof(f5,axiom,(
% 11.50/2.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.50/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/2.02  
% 11.50/2.02  fof(f21,plain,(
% 11.50/2.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.50/2.02    inference(cnf_transformation,[],[f5])).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.50/2.02      inference(cnf_transformation,[],[f29]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 11.50/2.02      inference(cnf_transformation,[],[f33]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_4,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.50/2.02      inference(cnf_transformation,[],[f22]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_44,plain,
% 11.50/2.02      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_6,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 11.50/2.02      inference(cnf_transformation,[],[f31]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_82,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_44,c_6]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_252,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_44,c_82]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_5,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.50/2.02      inference(cnf_transformation,[],[f23]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_267,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_252,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_7,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.50/2.02      inference(cnf_transformation,[],[f32]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_29,plain,
% 11.50/2.02      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_7,c_4]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_46,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_29]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_48,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_46,c_4]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_268,plain,
% 11.50/2.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_267,c_29,c_48]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_271,plain,
% 11.50/2.02      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_268,c_44]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_273,plain,
% 11.50/2.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_271,c_268]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_330,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_273,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_336,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_330,c_268]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_434,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_8,c_336]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_0,plain,
% 11.50/2.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.50/2.02      inference(cnf_transformation,[],[f17]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_9,negated_conjecture,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.50/2.02      inference(cnf_transformation,[],[f34]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_30,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_0,c_9]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_44360,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_434,c_30]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_2,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.50/2.02      inference(cnf_transformation,[],[f30]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_99,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_79,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_18751,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_99,c_79]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_3,plain,
% 11.50/2.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.50/2.02      inference(cnf_transformation,[],[f21]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_430,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_0,c_336]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_464,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_79,c_430]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_506,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_464,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_517,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_506,c_5,c_268]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_756,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_517]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_18807,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_18751,c_3,c_756]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_491,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_464]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_109,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_128,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,X0))) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_109,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_509,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_464,c_8]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_510,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_464,c_1]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_513,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_510,c_3,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_514,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_509,c_513]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_515,plain,
% 11.50/2.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_514,c_3,c_6]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_436,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_79,c_336]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_865,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_436,c_1]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_60,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_599,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_60]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_870,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_865,c_3,c_599]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_33722,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.50/2.02      inference(light_normalisation,
% 11.50/2.02                [status(thm)],
% 11.50/2.02                [c_128,c_128,c_430,c_515,c_870]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_33796,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_491,c_33722]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_69,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_2575,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k1_xboole_0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_464,c_69]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_2774,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_2575,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_2775,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_2774,c_3,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_70,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_74,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_70,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_7320,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_74,c_69]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_770,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_0,c_517]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_501,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_464,c_8]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_31,plain,
% 11.50/2.02      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_522,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_501,c_5,c_31]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_523,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_522,c_3,c_6]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_548,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_523]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1383,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_770,c_548]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1427,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_1383,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1428,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_1427,c_3]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_447,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_336,c_8]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_95,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_449,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_447,c_3,c_95]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_705,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_0,c_449]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1214,plain,
% 11.50/2.02      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_705,c_0]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_445,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_336,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_66,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_75,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_66,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_450,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_445,c_75,c_268]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1206,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_705,c_450]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_5567,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X0),X2)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1214,c_1206]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_941,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_450,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_947,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_941,c_75,c_268]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_4154,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X3)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_705,c_947]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_5748,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_5567,c_75,c_705,c_4154]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_18378,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1428,c_5748]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_29781,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X2))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X2),k1_xboole_0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_18378,c_69]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_331,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k2_xboole_0(X0,X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_273,c_8]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_333,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X0) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_331,c_273]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_334,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0) = k2_xboole_0(X0,X0) ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_333,c_4]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_335,plain,
% 11.50/2.02      ( k2_xboole_0(X0,X0) = X0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_334,c_31]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_7114,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_335,c_74]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_247,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_82]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_287,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_247,c_3,c_268]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_7469,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_7114,c_287]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8265,plain,
% 11.50/2.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_7469,c_8]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8283,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0)))) = X0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_8265,c_3,c_5,c_523]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8284,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_8283,c_3,c_31,c_464]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8297,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_8284]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_408,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_79,c_0]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8818,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X2,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_8297,c_408]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8844,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_8818,c_3,c_5,c_273]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_8845,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_8844,c_75,c_705]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_21598,plain,
% 11.50/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_8845,c_513]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1209,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_705,c_336]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_361,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_287]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_22755,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1209,c_361]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_23019,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k1_xboole_0 ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_22755,c_3]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_23220,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),X0) = X0 ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_23019,c_548]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1626,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1209,c_60]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1637,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_1626,c_1209]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_1638,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_1637,c_4,c_5,c_31]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_7760,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X3)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1638,c_5]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_23359,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k1_xboole_0)),X1) = X1 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_23220,c_7760]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_23360,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_23359,c_3]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_24100,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_23360,c_60]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_24152,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_24100,c_4,c_336]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_24305,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_24152,c_1]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_24370,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_24305,c_8297]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_27234,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))),X0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_8297,c_24370]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_466,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(X1,X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_430,c_79]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_483,plain,
% 11.50/2.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(X1,X0) ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_466,c_4]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_24196,plain,
% 11.50/2.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_24152,c_483]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_24792,plain,
% 11.50/2.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_5,c_24196]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_27388,plain,
% 11.50/2.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_27234,c_24792]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_29816,plain,
% 11.50/2.02      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.50/2.02      inference(light_normalisation,[status(thm)],[c_29781,c_21598,c_27388]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_34290,plain,
% 11.50/2.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.50/2.02      inference(light_normalisation,
% 11.50/2.02                [status(thm)],
% 11.50/2.02                [c_33796,c_2775,c_7320,c_29816]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_44361,plain,
% 11.50/2.02      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.50/2.02      inference(demodulation,[status(thm)],[c_44360,c_18807,c_34290]) ).
% 11.50/2.02  
% 11.50/2.02  cnf(c_45209,plain,
% 11.50/2.02      ( $false ),
% 11.50/2.02      inference(superposition,[status(thm)],[c_1,c_44361]) ).
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.50/2.02  
% 11.50/2.02  ------                               Statistics
% 11.50/2.02  
% 11.50/2.02  ------ General
% 11.50/2.02  
% 11.50/2.02  abstr_ref_over_cycles:                  0
% 11.50/2.02  abstr_ref_under_cycles:                 0
% 11.50/2.02  gc_basic_clause_elim:                   0
% 11.50/2.02  forced_gc_time:                         0
% 11.50/2.02  parsing_time:                           0.012
% 11.50/2.02  unif_index_cands_time:                  0.
% 11.50/2.02  unif_index_add_time:                    0.
% 11.50/2.02  orderings_time:                         0.
% 11.50/2.02  out_proof_time:                         0.01
% 11.50/2.02  total_time:                             1.494
% 11.50/2.02  num_of_symbols:                         39
% 11.50/2.02  num_of_terms:                           61064
% 11.50/2.02  
% 11.50/2.02  ------ Preprocessing
% 11.50/2.02  
% 11.50/2.02  num_of_splits:                          0
% 11.50/2.02  num_of_split_atoms:                     3
% 11.50/2.02  num_of_reused_defs:                     1
% 11.50/2.02  num_eq_ax_congr_red:                    0
% 11.50/2.02  num_of_sem_filtered_clauses:            0
% 11.50/2.02  num_of_subtypes:                        0
% 11.50/2.02  monotx_restored_types:                  0
% 11.50/2.02  sat_num_of_epr_types:                   0
% 11.50/2.02  sat_num_of_non_cyclic_types:            0
% 11.50/2.02  sat_guarded_non_collapsed_types:        0
% 11.50/2.02  num_pure_diseq_elim:                    0
% 11.50/2.02  simp_replaced_by:                       0
% 11.50/2.02  res_preprocessed:                       24
% 11.50/2.02  prep_upred:                             0
% 11.50/2.02  prep_unflattend:                        0
% 11.50/2.02  smt_new_axioms:                         0
% 11.50/2.02  pred_elim_cands:                        0
% 11.50/2.02  pred_elim:                              0
% 11.50/2.02  pred_elim_cl:                           0
% 11.50/2.02  pred_elim_cycles:                       0
% 11.50/2.02  merged_defs:                            0
% 11.50/2.02  merged_defs_ncl:                        0
% 11.50/2.02  bin_hyper_res:                          0
% 11.50/2.02  prep_cycles:                            2
% 11.50/2.02  pred_elim_time:                         0.
% 11.50/2.02  splitting_time:                         0.
% 11.50/2.02  sem_filter_time:                        0.
% 11.50/2.02  monotx_time:                            0.001
% 11.50/2.02  subtype_inf_time:                       0.
% 11.50/2.02  
% 11.50/2.02  ------ Problem properties
% 11.50/2.02  
% 11.50/2.02  clauses:                                10
% 11.50/2.02  conjectures:                            1
% 11.50/2.02  epr:                                    0
% 11.50/2.02  horn:                                   10
% 11.50/2.02  ground:                                 1
% 11.50/2.02  unary:                                  10
% 11.50/2.02  binary:                                 0
% 11.50/2.02  lits:                                   10
% 11.50/2.02  lits_eq:                                10
% 11.50/2.02  fd_pure:                                0
% 11.50/2.02  fd_pseudo:                              0
% 11.50/2.02  fd_cond:                                0
% 11.50/2.02  fd_pseudo_cond:                         0
% 11.50/2.02  ac_symbols:                             1
% 11.50/2.02  
% 11.50/2.02  ------ Propositional Solver
% 11.50/2.02  
% 11.50/2.02  prop_solver_calls:                      13
% 11.50/2.02  prop_fast_solver_calls:                 60
% 11.50/2.02  smt_solver_calls:                       0
% 11.50/2.02  smt_fast_solver_calls:                  0
% 11.50/2.02  prop_num_of_clauses:                    321
% 11.50/2.02  prop_preprocess_simplified:             407
% 11.50/2.02  prop_fo_subsumed:                       0
% 11.50/2.02  prop_solver_time:                       0.
% 11.50/2.02  smt_solver_time:                        0.
% 11.50/2.02  smt_fast_solver_time:                   0.
% 11.50/2.02  prop_fast_solver_time:                  0.
% 11.50/2.02  prop_unsat_core_time:                   0.
% 11.50/2.02  
% 11.50/2.02  ------ QBF
% 11.50/2.02  
% 11.50/2.02  qbf_q_res:                              0
% 11.50/2.02  qbf_num_tautologies:                    0
% 11.50/2.02  qbf_prep_cycles:                        0
% 11.50/2.02  
% 11.50/2.02  ------ BMC1
% 11.50/2.02  
% 11.50/2.02  bmc1_current_bound:                     -1
% 11.50/2.02  bmc1_last_solved_bound:                 -1
% 11.50/2.02  bmc1_unsat_core_size:                   -1
% 11.50/2.02  bmc1_unsat_core_parents_size:           -1
% 11.50/2.02  bmc1_merge_next_fun:                    0
% 11.50/2.02  bmc1_unsat_core_clauses_time:           0.
% 11.50/2.02  
% 11.50/2.02  ------ Instantiation
% 11.50/2.02  
% 11.50/2.02  inst_num_of_clauses:                    0
% 11.50/2.02  inst_num_in_passive:                    0
% 11.50/2.02  inst_num_in_active:                     0
% 11.50/2.02  inst_num_in_unprocessed:                0
% 11.50/2.02  inst_num_of_loops:                      0
% 11.50/2.02  inst_num_of_learning_restarts:          0
% 11.50/2.02  inst_num_moves_active_passive:          0
% 11.50/2.02  inst_lit_activity:                      0
% 11.50/2.02  inst_lit_activity_moves:                0
% 11.50/2.02  inst_num_tautologies:                   0
% 11.50/2.02  inst_num_prop_implied:                  0
% 11.50/2.02  inst_num_existing_simplified:           0
% 11.50/2.02  inst_num_eq_res_simplified:             0
% 11.50/2.02  inst_num_child_elim:                    0
% 11.50/2.02  inst_num_of_dismatching_blockings:      0
% 11.50/2.02  inst_num_of_non_proper_insts:           0
% 11.50/2.02  inst_num_of_duplicates:                 0
% 11.50/2.02  inst_inst_num_from_inst_to_res:         0
% 11.50/2.02  inst_dismatching_checking_time:         0.
% 11.50/2.02  
% 11.50/2.02  ------ Resolution
% 11.50/2.02  
% 11.50/2.02  res_num_of_clauses:                     0
% 11.50/2.02  res_num_in_passive:                     0
% 11.50/2.02  res_num_in_active:                      0
% 11.50/2.02  res_num_of_loops:                       26
% 11.50/2.02  res_forward_subset_subsumed:            0
% 11.50/2.02  res_backward_subset_subsumed:           0
% 11.50/2.02  res_forward_subsumed:                   0
% 11.50/2.02  res_backward_subsumed:                  0
% 11.50/2.02  res_forward_subsumption_resolution:     0
% 11.50/2.02  res_backward_subsumption_resolution:    0
% 11.50/2.02  res_clause_to_clause_subsumption:       108150
% 11.50/2.02  res_orphan_elimination:                 0
% 11.50/2.02  res_tautology_del:                      0
% 11.50/2.02  res_num_eq_res_simplified:              0
% 11.50/2.02  res_num_sel_changes:                    0
% 11.50/2.02  res_moves_from_active_to_pass:          0
% 11.50/2.02  
% 11.50/2.02  ------ Superposition
% 11.50/2.02  
% 11.50/2.02  sup_time_total:                         0.
% 11.50/2.02  sup_time_generating:                    0.
% 11.50/2.02  sup_time_sim_full:                      0.
% 11.50/2.02  sup_time_sim_immed:                     0.
% 11.50/2.02  
% 11.50/2.02  sup_num_of_clauses:                     3937
% 11.50/2.02  sup_num_in_active:                      145
% 11.50/2.02  sup_num_in_passive:                     3792
% 11.50/2.02  sup_num_of_loops:                       194
% 11.50/2.02  sup_fw_superposition:                   16044
% 11.50/2.02  sup_bw_superposition:                   14987
% 11.50/2.02  sup_immediate_simplified:               12573
% 11.50/2.02  sup_given_eliminated:                   5
% 11.50/2.02  comparisons_done:                       0
% 11.50/2.02  comparisons_avoided:                    0
% 11.50/2.02  
% 11.50/2.02  ------ Simplifications
% 11.50/2.02  
% 11.50/2.02  
% 11.50/2.02  sim_fw_subset_subsumed:                 0
% 11.50/2.02  sim_bw_subset_subsumed:                 0
% 11.50/2.02  sim_fw_subsumed:                        2181
% 11.50/2.02  sim_bw_subsumed:                        31
% 11.50/2.02  sim_fw_subsumption_res:                 0
% 11.50/2.02  sim_bw_subsumption_res:                 0
% 11.50/2.02  sim_tautology_del:                      0
% 11.50/2.02  sim_eq_tautology_del:                   3912
% 11.50/2.02  sim_eq_res_simp:                        0
% 11.50/2.02  sim_fw_demodulated:                     8822
% 11.50/2.02  sim_bw_demodulated:                     238
% 11.50/2.02  sim_light_normalised:                   4906
% 11.50/2.02  sim_joinable_taut:                      41
% 11.50/2.02  sim_joinable_simp:                      0
% 11.50/2.02  sim_ac_normalised:                      0
% 11.50/2.02  sim_smt_subsumption:                    0
% 11.50/2.02  
%------------------------------------------------------------------------------
