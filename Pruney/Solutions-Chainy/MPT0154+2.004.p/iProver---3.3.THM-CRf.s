%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:52 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :   82 (9696 expanded)
%              Number of clauses        :   45 (1741 expanded)
%              Number of leaves         :   13 (3070 expanded)
%              Depth                    :   24
%              Number of atoms          :   83 (9697 expanded)
%              Number of equality atoms :   82 (9696 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f18,f31,f31])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f24,f20,f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f23,f20,f31,f20,f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f30,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f31,f32])).

fof(f40,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f30,f32,f33])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_84,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_98,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_84,c_5])).

cnf(c_112,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_98,c_3])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_129,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_112,c_0])).

cnf(c_131,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_112,c_2])).

cnf(c_94,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_84])).

cnf(c_100,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_94,c_98])).

cnf(c_110,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_98,c_0])).

cnf(c_117,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_110,c_98])).

cnf(c_135,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_131,c_98,c_100,c_117])).

cnf(c_136,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_129,c_112,c_135])).

cnf(c_261,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_136,c_0])).

cnf(c_268,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_261,c_112,c_135])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_273,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_268,c_6])).

cnf(c_270,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_268,c_136])).

cnf(c_284,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_273,c_270])).

cnf(c_143,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_100,c_100,c_135])).

cnf(c_285,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_284,c_98,c_143])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_263,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_136,c_7])).

cnf(c_287,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(demodulation,[status(thm)],[c_263,c_268])).

cnf(c_288,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_287,c_143])).

cnf(c_312,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_7,c_288])).

cnf(c_361,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
    inference(superposition,[status(thm)],[c_7,c_312])).

cnf(c_22453,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(superposition,[status(thm)],[c_285,c_361])).

cnf(c_365,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
    inference(superposition,[status(thm)],[c_270,c_312])).

cnf(c_374,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_365,c_135])).

cnf(c_505,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_374,c_288])).

cnf(c_596,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_505,c_7])).

cnf(c_969,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_596,c_312])).

cnf(c_22532,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_22453,c_135,c_969])).

cnf(c_23857,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_22532])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_30,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_3,c_8])).

cnf(c_31,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(superposition,[status(thm)],[c_3,c_30])).

cnf(c_39,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_7,c_31])).

cnf(c_300,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_288,c_39])).

cnf(c_24407,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0)) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_23857,c_300])).

cnf(c_24408,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_24407])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:24:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.37/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/1.48  
% 7.37/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.37/1.48  
% 7.37/1.48  ------  iProver source info
% 7.37/1.48  
% 7.37/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.37/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.37/1.48  git: non_committed_changes: false
% 7.37/1.48  git: last_make_outside_of_git: false
% 7.37/1.48  
% 7.37/1.48  ------ 
% 7.37/1.48  
% 7.37/1.48  ------ Input Options
% 7.37/1.48  
% 7.37/1.48  --out_options                           all
% 7.37/1.48  --tptp_safe_out                         true
% 7.37/1.48  --problem_path                          ""
% 7.37/1.48  --include_path                          ""
% 7.37/1.48  --clausifier                            res/vclausify_rel
% 7.37/1.48  --clausifier_options                    --mode clausify
% 7.37/1.48  --stdin                                 false
% 7.37/1.48  --stats_out                             all
% 7.37/1.48  
% 7.37/1.48  ------ General Options
% 7.37/1.48  
% 7.37/1.48  --fof                                   false
% 7.37/1.48  --time_out_real                         305.
% 7.37/1.48  --time_out_virtual                      -1.
% 7.37/1.48  --symbol_type_check                     false
% 7.37/1.48  --clausify_out                          false
% 7.37/1.48  --sig_cnt_out                           false
% 7.37/1.48  --trig_cnt_out                          false
% 7.37/1.48  --trig_cnt_out_tolerance                1.
% 7.37/1.48  --trig_cnt_out_sk_spl                   false
% 7.37/1.48  --abstr_cl_out                          false
% 7.37/1.48  
% 7.37/1.48  ------ Global Options
% 7.37/1.48  
% 7.37/1.48  --schedule                              default
% 7.37/1.48  --add_important_lit                     false
% 7.37/1.48  --prop_solver_per_cl                    1000
% 7.37/1.48  --min_unsat_core                        false
% 7.37/1.48  --soft_assumptions                      false
% 7.37/1.48  --soft_lemma_size                       3
% 7.37/1.48  --prop_impl_unit_size                   0
% 7.37/1.48  --prop_impl_unit                        []
% 7.37/1.48  --share_sel_clauses                     true
% 7.37/1.48  --reset_solvers                         false
% 7.37/1.48  --bc_imp_inh                            [conj_cone]
% 7.37/1.48  --conj_cone_tolerance                   3.
% 7.37/1.48  --extra_neg_conj                        none
% 7.37/1.48  --large_theory_mode                     true
% 7.37/1.48  --prolific_symb_bound                   200
% 7.37/1.48  --lt_threshold                          2000
% 7.37/1.48  --clause_weak_htbl                      true
% 7.37/1.48  --gc_record_bc_elim                     false
% 7.37/1.48  
% 7.37/1.48  ------ Preprocessing Options
% 7.37/1.48  
% 7.37/1.48  --preprocessing_flag                    true
% 7.37/1.48  --time_out_prep_mult                    0.1
% 7.37/1.48  --splitting_mode                        input
% 7.37/1.48  --splitting_grd                         true
% 7.37/1.48  --splitting_cvd                         false
% 7.37/1.48  --splitting_cvd_svl                     false
% 7.37/1.48  --splitting_nvd                         32
% 7.37/1.48  --sub_typing                            true
% 7.37/1.48  --prep_gs_sim                           true
% 7.37/1.48  --prep_unflatten                        true
% 7.37/1.48  --prep_res_sim                          true
% 7.37/1.48  --prep_upred                            true
% 7.37/1.48  --prep_sem_filter                       exhaustive
% 7.37/1.48  --prep_sem_filter_out                   false
% 7.37/1.48  --pred_elim                             true
% 7.37/1.48  --res_sim_input                         true
% 7.37/1.48  --eq_ax_congr_red                       true
% 7.37/1.48  --pure_diseq_elim                       true
% 7.37/1.48  --brand_transform                       false
% 7.37/1.48  --non_eq_to_eq                          false
% 7.37/1.48  --prep_def_merge                        true
% 7.37/1.48  --prep_def_merge_prop_impl              false
% 7.37/1.48  --prep_def_merge_mbd                    true
% 7.37/1.48  --prep_def_merge_tr_red                 false
% 7.37/1.48  --prep_def_merge_tr_cl                  false
% 7.37/1.48  --smt_preprocessing                     true
% 7.37/1.48  --smt_ac_axioms                         fast
% 7.37/1.48  --preprocessed_out                      false
% 7.37/1.48  --preprocessed_stats                    false
% 7.37/1.48  
% 7.37/1.48  ------ Abstraction refinement Options
% 7.37/1.48  
% 7.37/1.48  --abstr_ref                             []
% 7.37/1.48  --abstr_ref_prep                        false
% 7.37/1.48  --abstr_ref_until_sat                   false
% 7.37/1.48  --abstr_ref_sig_restrict                funpre
% 7.37/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.48  --abstr_ref_under                       []
% 7.37/1.48  
% 7.37/1.48  ------ SAT Options
% 7.37/1.48  
% 7.37/1.48  --sat_mode                              false
% 7.37/1.48  --sat_fm_restart_options                ""
% 7.37/1.48  --sat_gr_def                            false
% 7.37/1.48  --sat_epr_types                         true
% 7.37/1.48  --sat_non_cyclic_types                  false
% 7.37/1.48  --sat_finite_models                     false
% 7.37/1.48  --sat_fm_lemmas                         false
% 7.37/1.48  --sat_fm_prep                           false
% 7.37/1.48  --sat_fm_uc_incr                        true
% 7.37/1.48  --sat_out_model                         small
% 7.37/1.48  --sat_out_clauses                       false
% 7.37/1.48  
% 7.37/1.48  ------ QBF Options
% 7.37/1.48  
% 7.37/1.48  --qbf_mode                              false
% 7.37/1.48  --qbf_elim_univ                         false
% 7.37/1.48  --qbf_dom_inst                          none
% 7.37/1.48  --qbf_dom_pre_inst                      false
% 7.37/1.48  --qbf_sk_in                             false
% 7.37/1.48  --qbf_pred_elim                         true
% 7.37/1.48  --qbf_split                             512
% 7.37/1.48  
% 7.37/1.48  ------ BMC1 Options
% 7.37/1.48  
% 7.37/1.48  --bmc1_incremental                      false
% 7.37/1.48  --bmc1_axioms                           reachable_all
% 7.37/1.48  --bmc1_min_bound                        0
% 7.37/1.48  --bmc1_max_bound                        -1
% 7.37/1.48  --bmc1_max_bound_default                -1
% 7.37/1.48  --bmc1_symbol_reachability              true
% 7.37/1.48  --bmc1_property_lemmas                  false
% 7.37/1.48  --bmc1_k_induction                      false
% 7.37/1.48  --bmc1_non_equiv_states                 false
% 7.37/1.48  --bmc1_deadlock                         false
% 7.37/1.48  --bmc1_ucm                              false
% 7.37/1.48  --bmc1_add_unsat_core                   none
% 7.37/1.48  --bmc1_unsat_core_children              false
% 7.37/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.48  --bmc1_out_stat                         full
% 7.37/1.48  --bmc1_ground_init                      false
% 7.37/1.48  --bmc1_pre_inst_next_state              false
% 7.37/1.48  --bmc1_pre_inst_state                   false
% 7.37/1.48  --bmc1_pre_inst_reach_state             false
% 7.37/1.48  --bmc1_out_unsat_core                   false
% 7.37/1.48  --bmc1_aig_witness_out                  false
% 7.37/1.48  --bmc1_verbose                          false
% 7.37/1.48  --bmc1_dump_clauses_tptp                false
% 7.37/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.48  --bmc1_dump_file                        -
% 7.37/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.48  --bmc1_ucm_extend_mode                  1
% 7.37/1.48  --bmc1_ucm_init_mode                    2
% 7.37/1.48  --bmc1_ucm_cone_mode                    none
% 7.37/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.48  --bmc1_ucm_relax_model                  4
% 7.37/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.48  --bmc1_ucm_layered_model                none
% 7.37/1.48  --bmc1_ucm_max_lemma_size               10
% 7.37/1.48  
% 7.37/1.48  ------ AIG Options
% 7.37/1.48  
% 7.37/1.48  --aig_mode                              false
% 7.37/1.48  
% 7.37/1.48  ------ Instantiation Options
% 7.37/1.48  
% 7.37/1.48  --instantiation_flag                    true
% 7.37/1.48  --inst_sos_flag                         false
% 7.37/1.48  --inst_sos_phase                        true
% 7.37/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.48  --inst_lit_sel_side                     num_symb
% 7.37/1.48  --inst_solver_per_active                1400
% 7.37/1.48  --inst_solver_calls_frac                1.
% 7.37/1.48  --inst_passive_queue_type               priority_queues
% 7.37/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.48  --inst_passive_queues_freq              [25;2]
% 7.37/1.48  --inst_dismatching                      true
% 7.37/1.48  --inst_eager_unprocessed_to_passive     true
% 7.37/1.48  --inst_prop_sim_given                   true
% 7.37/1.48  --inst_prop_sim_new                     false
% 7.37/1.48  --inst_subs_new                         false
% 7.37/1.48  --inst_eq_res_simp                      false
% 7.37/1.48  --inst_subs_given                       false
% 7.37/1.48  --inst_orphan_elimination               true
% 7.37/1.48  --inst_learning_loop_flag               true
% 7.37/1.48  --inst_learning_start                   3000
% 7.37/1.48  --inst_learning_factor                  2
% 7.37/1.48  --inst_start_prop_sim_after_learn       3
% 7.37/1.48  --inst_sel_renew                        solver
% 7.37/1.48  --inst_lit_activity_flag                true
% 7.37/1.48  --inst_restr_to_given                   false
% 7.37/1.48  --inst_activity_threshold               500
% 7.37/1.48  --inst_out_proof                        true
% 7.37/1.48  
% 7.37/1.48  ------ Resolution Options
% 7.37/1.48  
% 7.37/1.48  --resolution_flag                       true
% 7.37/1.48  --res_lit_sel                           adaptive
% 7.37/1.48  --res_lit_sel_side                      none
% 7.37/1.48  --res_ordering                          kbo
% 7.37/1.48  --res_to_prop_solver                    active
% 7.37/1.48  --res_prop_simpl_new                    false
% 7.37/1.48  --res_prop_simpl_given                  true
% 7.37/1.48  --res_passive_queue_type                priority_queues
% 7.37/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.48  --res_passive_queues_freq               [15;5]
% 7.37/1.48  --res_forward_subs                      full
% 7.37/1.48  --res_backward_subs                     full
% 7.37/1.48  --res_forward_subs_resolution           true
% 7.37/1.48  --res_backward_subs_resolution          true
% 7.37/1.48  --res_orphan_elimination                true
% 7.37/1.48  --res_time_limit                        2.
% 7.37/1.48  --res_out_proof                         true
% 7.37/1.48  
% 7.37/1.48  ------ Superposition Options
% 7.37/1.48  
% 7.37/1.48  --superposition_flag                    true
% 7.37/1.48  --sup_passive_queue_type                priority_queues
% 7.37/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.48  --demod_completeness_check              fast
% 7.37/1.48  --demod_use_ground                      true
% 7.37/1.48  --sup_to_prop_solver                    passive
% 7.37/1.48  --sup_prop_simpl_new                    true
% 7.37/1.48  --sup_prop_simpl_given                  true
% 7.37/1.48  --sup_fun_splitting                     false
% 7.37/1.48  --sup_smt_interval                      50000
% 7.37/1.48  
% 7.37/1.48  ------ Superposition Simplification Setup
% 7.37/1.48  
% 7.37/1.48  --sup_indices_passive                   []
% 7.37/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.48  --sup_full_bw                           [BwDemod]
% 7.37/1.48  --sup_immed_triv                        [TrivRules]
% 7.37/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.48  --sup_immed_bw_main                     []
% 7.37/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.48  
% 7.37/1.48  ------ Combination Options
% 7.37/1.48  
% 7.37/1.48  --comb_res_mult                         3
% 7.37/1.48  --comb_sup_mult                         2
% 7.37/1.48  --comb_inst_mult                        10
% 7.37/1.48  
% 7.37/1.48  ------ Debug Options
% 7.37/1.48  
% 7.37/1.48  --dbg_backtrace                         false
% 7.37/1.48  --dbg_dump_prop_clauses                 false
% 7.37/1.48  --dbg_dump_prop_clauses_file            -
% 7.37/1.48  --dbg_out_stat                          false
% 7.37/1.48  ------ Parsing...
% 7.37/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.37/1.48  
% 7.37/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.37/1.48  
% 7.37/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.37/1.48  
% 7.37/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.37/1.48  ------ Proving...
% 7.37/1.48  ------ Problem Properties 
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  clauses                                 9
% 7.37/1.48  conjectures                             1
% 7.37/1.48  EPR                                     0
% 7.37/1.48  Horn                                    9
% 7.37/1.48  unary                                   9
% 7.37/1.48  binary                                  0
% 7.37/1.48  lits                                    9
% 7.37/1.48  lits eq                                 9
% 7.37/1.48  fd_pure                                 0
% 7.37/1.48  fd_pseudo                               0
% 7.37/1.48  fd_cond                                 0
% 7.37/1.48  fd_pseudo_cond                          0
% 7.37/1.48  AC symbols                              0
% 7.37/1.48  
% 7.37/1.48  ------ Schedule UEQ
% 7.37/1.48  
% 7.37/1.48  ------ pure equality problem: resolution off 
% 7.37/1.48  
% 7.37/1.48  ------ Option_UEQ Time Limit: Unbounded
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  ------ 
% 7.37/1.48  Current options:
% 7.37/1.48  ------ 
% 7.37/1.48  
% 7.37/1.48  ------ Input Options
% 7.37/1.48  
% 7.37/1.48  --out_options                           all
% 7.37/1.48  --tptp_safe_out                         true
% 7.37/1.48  --problem_path                          ""
% 7.37/1.48  --include_path                          ""
% 7.37/1.48  --clausifier                            res/vclausify_rel
% 7.37/1.48  --clausifier_options                    --mode clausify
% 7.37/1.48  --stdin                                 false
% 7.37/1.48  --stats_out                             all
% 7.37/1.48  
% 7.37/1.48  ------ General Options
% 7.37/1.48  
% 7.37/1.48  --fof                                   false
% 7.37/1.48  --time_out_real                         305.
% 7.37/1.48  --time_out_virtual                      -1.
% 7.37/1.48  --symbol_type_check                     false
% 7.37/1.48  --clausify_out                          false
% 7.37/1.48  --sig_cnt_out                           false
% 7.37/1.48  --trig_cnt_out                          false
% 7.37/1.48  --trig_cnt_out_tolerance                1.
% 7.37/1.48  --trig_cnt_out_sk_spl                   false
% 7.37/1.48  --abstr_cl_out                          false
% 7.37/1.48  
% 7.37/1.48  ------ Global Options
% 7.37/1.48  
% 7.37/1.48  --schedule                              default
% 7.37/1.48  --add_important_lit                     false
% 7.37/1.48  --prop_solver_per_cl                    1000
% 7.37/1.48  --min_unsat_core                        false
% 7.37/1.48  --soft_assumptions                      false
% 7.37/1.48  --soft_lemma_size                       3
% 7.37/1.48  --prop_impl_unit_size                   0
% 7.37/1.48  --prop_impl_unit                        []
% 7.37/1.48  --share_sel_clauses                     true
% 7.37/1.48  --reset_solvers                         false
% 7.37/1.48  --bc_imp_inh                            [conj_cone]
% 7.37/1.48  --conj_cone_tolerance                   3.
% 7.37/1.48  --extra_neg_conj                        none
% 7.37/1.48  --large_theory_mode                     true
% 7.37/1.48  --prolific_symb_bound                   200
% 7.37/1.48  --lt_threshold                          2000
% 7.37/1.48  --clause_weak_htbl                      true
% 7.37/1.48  --gc_record_bc_elim                     false
% 7.37/1.48  
% 7.37/1.48  ------ Preprocessing Options
% 7.37/1.48  
% 7.37/1.48  --preprocessing_flag                    true
% 7.37/1.48  --time_out_prep_mult                    0.1
% 7.37/1.48  --splitting_mode                        input
% 7.37/1.48  --splitting_grd                         true
% 7.37/1.48  --splitting_cvd                         false
% 7.37/1.48  --splitting_cvd_svl                     false
% 7.37/1.48  --splitting_nvd                         32
% 7.37/1.48  --sub_typing                            true
% 7.37/1.48  --prep_gs_sim                           true
% 7.37/1.48  --prep_unflatten                        true
% 7.37/1.48  --prep_res_sim                          true
% 7.37/1.48  --prep_upred                            true
% 7.37/1.48  --prep_sem_filter                       exhaustive
% 7.37/1.48  --prep_sem_filter_out                   false
% 7.37/1.48  --pred_elim                             true
% 7.37/1.48  --res_sim_input                         true
% 7.37/1.48  --eq_ax_congr_red                       true
% 7.37/1.48  --pure_diseq_elim                       true
% 7.37/1.48  --brand_transform                       false
% 7.37/1.48  --non_eq_to_eq                          false
% 7.37/1.48  --prep_def_merge                        true
% 7.37/1.48  --prep_def_merge_prop_impl              false
% 7.37/1.48  --prep_def_merge_mbd                    true
% 7.37/1.48  --prep_def_merge_tr_red                 false
% 7.37/1.48  --prep_def_merge_tr_cl                  false
% 7.37/1.48  --smt_preprocessing                     true
% 7.37/1.48  --smt_ac_axioms                         fast
% 7.37/1.48  --preprocessed_out                      false
% 7.37/1.48  --preprocessed_stats                    false
% 7.37/1.48  
% 7.37/1.48  ------ Abstraction refinement Options
% 7.37/1.48  
% 7.37/1.48  --abstr_ref                             []
% 7.37/1.48  --abstr_ref_prep                        false
% 7.37/1.48  --abstr_ref_until_sat                   false
% 7.37/1.48  --abstr_ref_sig_restrict                funpre
% 7.37/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.48  --abstr_ref_under                       []
% 7.37/1.48  
% 7.37/1.48  ------ SAT Options
% 7.37/1.48  
% 7.37/1.48  --sat_mode                              false
% 7.37/1.48  --sat_fm_restart_options                ""
% 7.37/1.48  --sat_gr_def                            false
% 7.37/1.48  --sat_epr_types                         true
% 7.37/1.48  --sat_non_cyclic_types                  false
% 7.37/1.48  --sat_finite_models                     false
% 7.37/1.48  --sat_fm_lemmas                         false
% 7.37/1.48  --sat_fm_prep                           false
% 7.37/1.48  --sat_fm_uc_incr                        true
% 7.37/1.48  --sat_out_model                         small
% 7.37/1.48  --sat_out_clauses                       false
% 7.37/1.48  
% 7.37/1.48  ------ QBF Options
% 7.37/1.48  
% 7.37/1.48  --qbf_mode                              false
% 7.37/1.48  --qbf_elim_univ                         false
% 7.37/1.48  --qbf_dom_inst                          none
% 7.37/1.48  --qbf_dom_pre_inst                      false
% 7.37/1.48  --qbf_sk_in                             false
% 7.37/1.48  --qbf_pred_elim                         true
% 7.37/1.48  --qbf_split                             512
% 7.37/1.48  
% 7.37/1.48  ------ BMC1 Options
% 7.37/1.48  
% 7.37/1.48  --bmc1_incremental                      false
% 7.37/1.48  --bmc1_axioms                           reachable_all
% 7.37/1.48  --bmc1_min_bound                        0
% 7.37/1.48  --bmc1_max_bound                        -1
% 7.37/1.48  --bmc1_max_bound_default                -1
% 7.37/1.48  --bmc1_symbol_reachability              true
% 7.37/1.48  --bmc1_property_lemmas                  false
% 7.37/1.48  --bmc1_k_induction                      false
% 7.37/1.48  --bmc1_non_equiv_states                 false
% 7.37/1.48  --bmc1_deadlock                         false
% 7.37/1.48  --bmc1_ucm                              false
% 7.37/1.48  --bmc1_add_unsat_core                   none
% 7.37/1.48  --bmc1_unsat_core_children              false
% 7.37/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.48  --bmc1_out_stat                         full
% 7.37/1.48  --bmc1_ground_init                      false
% 7.37/1.48  --bmc1_pre_inst_next_state              false
% 7.37/1.48  --bmc1_pre_inst_state                   false
% 7.37/1.48  --bmc1_pre_inst_reach_state             false
% 7.37/1.48  --bmc1_out_unsat_core                   false
% 7.37/1.48  --bmc1_aig_witness_out                  false
% 7.37/1.48  --bmc1_verbose                          false
% 7.37/1.48  --bmc1_dump_clauses_tptp                false
% 7.37/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.48  --bmc1_dump_file                        -
% 7.37/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.48  --bmc1_ucm_extend_mode                  1
% 7.37/1.48  --bmc1_ucm_init_mode                    2
% 7.37/1.48  --bmc1_ucm_cone_mode                    none
% 7.37/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.48  --bmc1_ucm_relax_model                  4
% 7.37/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.48  --bmc1_ucm_layered_model                none
% 7.37/1.48  --bmc1_ucm_max_lemma_size               10
% 7.37/1.48  
% 7.37/1.48  ------ AIG Options
% 7.37/1.48  
% 7.37/1.48  --aig_mode                              false
% 7.37/1.48  
% 7.37/1.48  ------ Instantiation Options
% 7.37/1.48  
% 7.37/1.48  --instantiation_flag                    false
% 7.37/1.48  --inst_sos_flag                         false
% 7.37/1.48  --inst_sos_phase                        true
% 7.37/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.48  --inst_lit_sel_side                     num_symb
% 7.37/1.48  --inst_solver_per_active                1400
% 7.37/1.48  --inst_solver_calls_frac                1.
% 7.37/1.48  --inst_passive_queue_type               priority_queues
% 7.37/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.48  --inst_passive_queues_freq              [25;2]
% 7.37/1.48  --inst_dismatching                      true
% 7.37/1.48  --inst_eager_unprocessed_to_passive     true
% 7.37/1.48  --inst_prop_sim_given                   true
% 7.37/1.48  --inst_prop_sim_new                     false
% 7.37/1.48  --inst_subs_new                         false
% 7.37/1.48  --inst_eq_res_simp                      false
% 7.37/1.48  --inst_subs_given                       false
% 7.37/1.48  --inst_orphan_elimination               true
% 7.37/1.48  --inst_learning_loop_flag               true
% 7.37/1.48  --inst_learning_start                   3000
% 7.37/1.48  --inst_learning_factor                  2
% 7.37/1.48  --inst_start_prop_sim_after_learn       3
% 7.37/1.48  --inst_sel_renew                        solver
% 7.37/1.48  --inst_lit_activity_flag                true
% 7.37/1.48  --inst_restr_to_given                   false
% 7.37/1.48  --inst_activity_threshold               500
% 7.37/1.48  --inst_out_proof                        true
% 7.37/1.48  
% 7.37/1.48  ------ Resolution Options
% 7.37/1.48  
% 7.37/1.48  --resolution_flag                       false
% 7.37/1.48  --res_lit_sel                           adaptive
% 7.37/1.48  --res_lit_sel_side                      none
% 7.37/1.48  --res_ordering                          kbo
% 7.37/1.48  --res_to_prop_solver                    active
% 7.37/1.48  --res_prop_simpl_new                    false
% 7.37/1.48  --res_prop_simpl_given                  true
% 7.37/1.48  --res_passive_queue_type                priority_queues
% 7.37/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.48  --res_passive_queues_freq               [15;5]
% 7.37/1.48  --res_forward_subs                      full
% 7.37/1.48  --res_backward_subs                     full
% 7.37/1.48  --res_forward_subs_resolution           true
% 7.37/1.48  --res_backward_subs_resolution          true
% 7.37/1.48  --res_orphan_elimination                true
% 7.37/1.48  --res_time_limit                        2.
% 7.37/1.48  --res_out_proof                         true
% 7.37/1.48  
% 7.37/1.48  ------ Superposition Options
% 7.37/1.48  
% 7.37/1.48  --superposition_flag                    true
% 7.37/1.48  --sup_passive_queue_type                priority_queues
% 7.37/1.48  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.48  --demod_completeness_check              fast
% 7.37/1.48  --demod_use_ground                      true
% 7.37/1.48  --sup_to_prop_solver                    active
% 7.37/1.48  --sup_prop_simpl_new                    false
% 7.37/1.48  --sup_prop_simpl_given                  false
% 7.37/1.48  --sup_fun_splitting                     true
% 7.37/1.48  --sup_smt_interval                      10000
% 7.37/1.48  
% 7.37/1.48  ------ Superposition Simplification Setup
% 7.37/1.48  
% 7.37/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.37/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.37/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.48  --sup_full_triv                         [TrivRules]
% 7.37/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.37/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.37/1.48  --sup_immed_triv                        [TrivRules]
% 7.37/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.48  --sup_immed_bw_main                     []
% 7.37/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.37/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.48  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.37/1.48  
% 7.37/1.48  ------ Combination Options
% 7.37/1.48  
% 7.37/1.48  --comb_res_mult                         1
% 7.37/1.48  --comb_sup_mult                         1
% 7.37/1.48  --comb_inst_mult                        1000000
% 7.37/1.48  
% 7.37/1.48  ------ Debug Options
% 7.37/1.48  
% 7.37/1.48  --dbg_backtrace                         false
% 7.37/1.48  --dbg_dump_prop_clauses                 false
% 7.37/1.48  --dbg_dump_prop_clauses_file            -
% 7.37/1.48  --dbg_out_stat                          false
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  ------ Proving...
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  % SZS status Theorem for theBenchmark.p
% 7.37/1.48  
% 7.37/1.48   Resolution empty clause
% 7.37/1.48  
% 7.37/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.37/1.48  
% 7.37/1.48  fof(f2,axiom,(
% 7.37/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f19,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.37/1.48    inference(cnf_transformation,[],[f2])).
% 7.37/1.48  
% 7.37/1.48  fof(f1,axiom,(
% 7.37/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f18,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.37/1.48    inference(cnf_transformation,[],[f1])).
% 7.37/1.48  
% 7.37/1.48  fof(f9,axiom,(
% 7.37/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f26,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.37/1.48    inference(cnf_transformation,[],[f9])).
% 7.37/1.48  
% 7.37/1.48  fof(f3,axiom,(
% 7.37/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f20,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.37/1.48    inference(cnf_transformation,[],[f3])).
% 7.37/1.48  
% 7.37/1.48  fof(f31,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.37/1.48    inference(definition_unfolding,[],[f26,f20])).
% 7.37/1.48  
% 7.37/1.48  fof(f36,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.37/1.48    inference(definition_unfolding,[],[f18,f31,f31])).
% 7.37/1.48  
% 7.37/1.48  fof(f4,axiom,(
% 7.37/1.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f21,plain,(
% 7.37/1.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.37/1.48    inference(cnf_transformation,[],[f4])).
% 7.37/1.48  
% 7.37/1.48  fof(f37,plain,(
% 7.37/1.48    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 7.37/1.48    inference(definition_unfolding,[],[f21,f31])).
% 7.37/1.48  
% 7.37/1.48  fof(f5,axiom,(
% 7.37/1.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f22,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.37/1.48    inference(cnf_transformation,[],[f5])).
% 7.37/1.48  
% 7.37/1.48  fof(f38,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 7.37/1.48    inference(definition_unfolding,[],[f22,f31])).
% 7.37/1.48  
% 7.37/1.48  fof(f7,axiom,(
% 7.37/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f24,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.37/1.48    inference(cnf_transformation,[],[f7])).
% 7.37/1.48  
% 7.37/1.48  fof(f34,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 7.37/1.48    inference(definition_unfolding,[],[f24,f20,f20])).
% 7.37/1.48  
% 7.37/1.48  fof(f6,axiom,(
% 7.37/1.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f23,plain,(
% 7.37/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.37/1.48    inference(cnf_transformation,[],[f6])).
% 7.37/1.48  
% 7.37/1.48  fof(f39,plain,(
% 7.37/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2))) )),
% 7.37/1.48    inference(definition_unfolding,[],[f23,f20,f31,f20,f20])).
% 7.37/1.48  
% 7.37/1.48  fof(f8,axiom,(
% 7.37/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f25,plain,(
% 7.37/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.37/1.48    inference(cnf_transformation,[],[f8])).
% 7.37/1.48  
% 7.37/1.48  fof(f13,conjecture,(
% 7.37/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f14,negated_conjecture,(
% 7.37/1.48    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.37/1.48    inference(negated_conjecture,[],[f13])).
% 7.37/1.48  
% 7.37/1.48  fof(f15,plain,(
% 7.37/1.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 7.37/1.48    inference(ennf_transformation,[],[f14])).
% 7.37/1.48  
% 7.37/1.48  fof(f16,plain,(
% 7.37/1.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 7.37/1.48    introduced(choice_axiom,[])).
% 7.37/1.48  
% 7.37/1.48  fof(f17,plain,(
% 7.37/1.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 7.37/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 7.37/1.48  
% 7.37/1.48  fof(f30,plain,(
% 7.37/1.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 7.37/1.48    inference(cnf_transformation,[],[f17])).
% 7.37/1.48  
% 7.37/1.48  fof(f11,axiom,(
% 7.37/1.48    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f28,plain,(
% 7.37/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 7.37/1.48    inference(cnf_transformation,[],[f11])).
% 7.37/1.48  
% 7.37/1.48  fof(f10,axiom,(
% 7.37/1.48    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 7.37/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.48  
% 7.37/1.48  fof(f27,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 7.37/1.48    inference(cnf_transformation,[],[f10])).
% 7.37/1.48  
% 7.37/1.48  fof(f32,plain,(
% 7.37/1.48    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 7.37/1.48    inference(definition_unfolding,[],[f27,f31])).
% 7.37/1.48  
% 7.37/1.48  fof(f33,plain,(
% 7.37/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2)) )),
% 7.37/1.48    inference(definition_unfolding,[],[f28,f31,f32])).
% 7.37/1.48  
% 7.37/1.48  fof(f40,plain,(
% 7.37/1.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0))))),
% 7.37/1.48    inference(definition_unfolding,[],[f30,f32,f33])).
% 7.37/1.48  
% 7.37/1.48  cnf(c_3,plain,
% 7.37/1.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.37/1.48      inference(cnf_transformation,[],[f19]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_2,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.37/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_4,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 7.37/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_84,plain,
% 7.37/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_5,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 7.37/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_98,plain,
% 7.37/1.48      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_84,c_5]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_112,plain,
% 7.37/1.48      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_98,c_3]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_0,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 7.37/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_129,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_112,c_0]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_131,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_112,c_2]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_94,plain,
% 7.37/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_3,c_84]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_100,plain,
% 7.37/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_94,c_98]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_110,plain,
% 7.37/1.48      ( k3_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_98,c_0]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_117,plain,
% 7.37/1.48      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_110,c_98]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_135,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.37/1.48      inference(light_normalisation,[status(thm)],[c_131,c_98,c_100,c_117]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_136,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_129,c_112,c_135]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_261,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_136,c_0]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_268,plain,
% 7.37/1.48      ( k3_xboole_0(X0,X0) = X0 ),
% 7.37/1.48      inference(light_normalisation,[status(thm)],[c_261,c_112,c_135]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_6,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) ),
% 7.37/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_273,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_268,c_6]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_270,plain,
% 7.37/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_268,c_136]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_284,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
% 7.37/1.48      inference(light_normalisation,[status(thm)],[c_273,c_270]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_143,plain,
% 7.37/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.37/1.48      inference(light_normalisation,[status(thm)],[c_100,c_100,c_135]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_285,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_284,c_98,c_143]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_7,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.37/1.48      inference(cnf_transformation,[],[f25]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_263,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_136,c_7]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_287,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_263,c_268]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_288,plain,
% 7.37/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_287,c_143]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_312,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_7,c_288]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_361,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_7,c_312]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_22453,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_285,c_361]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_365,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_270,c_312]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_374,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.37/1.48      inference(light_normalisation,[status(thm)],[c_365,c_135]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_505,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_374,c_288]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_596,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_505,c_7]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_969,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_596,c_312]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_22532,plain,
% 7.37/1.48      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_22453,c_135,c_969]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_23857,plain,
% 7.37/1.48      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_3,c_22532]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_8,negated_conjecture,
% 7.37/1.48      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
% 7.37/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_30,plain,
% 7.37/1.48      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_3,c_8]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_31,plain,
% 7.37/1.48      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 7.37/1.48      inference(superposition,[status(thm)],[c_3,c_30]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_39,plain,
% 7.37/1.48      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_7,c_31]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_300,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_288,c_39]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_24407,plain,
% 7.37/1.48      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0)) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 7.37/1.48      inference(demodulation,[status(thm)],[c_23857,c_300]) ).
% 7.37/1.48  
% 7.37/1.48  cnf(c_24408,plain,
% 7.37/1.48      ( $false ),
% 7.37/1.48      inference(theory_normalisation,[status(thm)],[c_24407]) ).
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.37/1.48  
% 7.37/1.48  ------                               Statistics
% 7.37/1.48  
% 7.37/1.48  ------ General
% 7.37/1.48  
% 7.37/1.48  abstr_ref_over_cycles:                  0
% 7.37/1.48  abstr_ref_under_cycles:                 0
% 7.37/1.48  gc_basic_clause_elim:                   0
% 7.37/1.48  forced_gc_time:                         0
% 7.37/1.48  parsing_time:                           0.009
% 7.37/1.48  unif_index_cands_time:                  0.
% 7.37/1.48  unif_index_add_time:                    0.
% 7.37/1.48  orderings_time:                         0.
% 7.37/1.48  out_proof_time:                         0.006
% 7.37/1.48  total_time:                             0.649
% 7.37/1.48  num_of_symbols:                         37
% 7.37/1.48  num_of_terms:                           41425
% 7.37/1.48  
% 7.37/1.48  ------ Preprocessing
% 7.37/1.48  
% 7.37/1.48  num_of_splits:                          0
% 7.37/1.48  num_of_split_atoms:                     0
% 7.37/1.48  num_of_reused_defs:                     0
% 7.37/1.48  num_eq_ax_congr_red:                    0
% 7.37/1.48  num_of_sem_filtered_clauses:            0
% 7.37/1.48  num_of_subtypes:                        0
% 7.37/1.48  monotx_restored_types:                  0
% 7.37/1.48  sat_num_of_epr_types:                   0
% 7.37/1.48  sat_num_of_non_cyclic_types:            0
% 7.37/1.48  sat_guarded_non_collapsed_types:        0
% 7.37/1.48  num_pure_diseq_elim:                    0
% 7.37/1.48  simp_replaced_by:                       0
% 7.37/1.48  res_preprocessed:                       23
% 7.37/1.48  prep_upred:                             0
% 7.37/1.48  prep_unflattend:                        0
% 7.37/1.48  smt_new_axioms:                         0
% 7.37/1.48  pred_elim_cands:                        0
% 7.37/1.48  pred_elim:                              0
% 7.37/1.48  pred_elim_cl:                           0
% 7.37/1.48  pred_elim_cycles:                       0
% 7.37/1.48  merged_defs:                            0
% 7.37/1.48  merged_defs_ncl:                        0
% 7.37/1.48  bin_hyper_res:                          0
% 7.37/1.48  prep_cycles:                            2
% 7.37/1.48  pred_elim_time:                         0.
% 7.37/1.48  splitting_time:                         0.
% 7.37/1.48  sem_filter_time:                        0.
% 7.37/1.48  monotx_time:                            0.
% 7.37/1.48  subtype_inf_time:                       0.
% 7.37/1.48  
% 7.37/1.48  ------ Problem properties
% 7.37/1.48  
% 7.37/1.48  clauses:                                9
% 7.37/1.48  conjectures:                            1
% 7.37/1.48  epr:                                    0
% 7.37/1.48  horn:                                   9
% 7.37/1.48  ground:                                 1
% 7.37/1.48  unary:                                  9
% 7.37/1.48  binary:                                 0
% 7.37/1.48  lits:                                   9
% 7.37/1.48  lits_eq:                                9
% 7.37/1.48  fd_pure:                                0
% 7.37/1.48  fd_pseudo:                              0
% 7.37/1.48  fd_cond:                                0
% 7.37/1.48  fd_pseudo_cond:                         0
% 7.37/1.48  ac_symbols:                             1
% 7.37/1.48  
% 7.37/1.48  ------ Propositional Solver
% 7.37/1.48  
% 7.37/1.48  prop_solver_calls:                      13
% 7.37/1.48  prop_fast_solver_calls:                 60
% 7.37/1.48  smt_solver_calls:                       0
% 7.37/1.48  smt_fast_solver_calls:                  0
% 7.37/1.48  prop_num_of_clauses:                    209
% 7.37/1.48  prop_preprocess_simplified:             362
% 7.37/1.48  prop_fo_subsumed:                       0
% 7.37/1.48  prop_solver_time:                       0.
% 7.37/1.48  smt_solver_time:                        0.
% 7.37/1.48  smt_fast_solver_time:                   0.
% 7.37/1.48  prop_fast_solver_time:                  0.
% 7.37/1.48  prop_unsat_core_time:                   0.
% 7.37/1.48  
% 7.37/1.48  ------ QBF
% 7.37/1.48  
% 7.37/1.48  qbf_q_res:                              0
% 7.37/1.48  qbf_num_tautologies:                    0
% 7.37/1.48  qbf_prep_cycles:                        0
% 7.37/1.48  
% 7.37/1.48  ------ BMC1
% 7.37/1.48  
% 7.37/1.48  bmc1_current_bound:                     -1
% 7.37/1.48  bmc1_last_solved_bound:                 -1
% 7.37/1.48  bmc1_unsat_core_size:                   -1
% 7.37/1.48  bmc1_unsat_core_parents_size:           -1
% 7.37/1.48  bmc1_merge_next_fun:                    0
% 7.37/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.37/1.48  
% 7.37/1.48  ------ Instantiation
% 7.37/1.48  
% 7.37/1.48  inst_num_of_clauses:                    0
% 7.37/1.48  inst_num_in_passive:                    0
% 7.37/1.48  inst_num_in_active:                     0
% 7.37/1.48  inst_num_in_unprocessed:                0
% 7.37/1.48  inst_num_of_loops:                      0
% 7.37/1.48  inst_num_of_learning_restarts:          0
% 7.37/1.48  inst_num_moves_active_passive:          0
% 7.37/1.48  inst_lit_activity:                      0
% 7.37/1.48  inst_lit_activity_moves:                0
% 7.37/1.48  inst_num_tautologies:                   0
% 7.37/1.48  inst_num_prop_implied:                  0
% 7.37/1.48  inst_num_existing_simplified:           0
% 7.37/1.48  inst_num_eq_res_simplified:             0
% 7.37/1.48  inst_num_child_elim:                    0
% 7.37/1.48  inst_num_of_dismatching_blockings:      0
% 7.37/1.48  inst_num_of_non_proper_insts:           0
% 7.37/1.48  inst_num_of_duplicates:                 0
% 7.37/1.48  inst_inst_num_from_inst_to_res:         0
% 7.37/1.48  inst_dismatching_checking_time:         0.
% 7.37/1.48  
% 7.37/1.48  ------ Resolution
% 7.37/1.48  
% 7.37/1.48  res_num_of_clauses:                     0
% 7.37/1.48  res_num_in_passive:                     0
% 7.37/1.48  res_num_in_active:                      0
% 7.37/1.48  res_num_of_loops:                       25
% 7.37/1.48  res_forward_subset_subsumed:            0
% 7.37/1.48  res_backward_subset_subsumed:           0
% 7.37/1.48  res_forward_subsumed:                   0
% 7.37/1.48  res_backward_subsumed:                  0
% 7.37/1.48  res_forward_subsumption_resolution:     0
% 7.37/1.48  res_backward_subsumption_resolution:    0
% 7.37/1.48  res_clause_to_clause_subsumption:       60009
% 7.37/1.48  res_orphan_elimination:                 0
% 7.37/1.48  res_tautology_del:                      0
% 7.37/1.48  res_num_eq_res_simplified:              0
% 7.37/1.48  res_num_sel_changes:                    0
% 7.37/1.48  res_moves_from_active_to_pass:          0
% 7.37/1.48  
% 7.37/1.48  ------ Superposition
% 7.37/1.48  
% 7.37/1.48  sup_time_total:                         0.
% 7.37/1.48  sup_time_generating:                    0.
% 7.37/1.48  sup_time_sim_full:                      0.
% 7.37/1.48  sup_time_sim_immed:                     0.
% 7.37/1.48  
% 7.37/1.48  sup_num_of_clauses:                     1820
% 7.37/1.48  sup_num_in_active:                      102
% 7.37/1.48  sup_num_in_passive:                     1718
% 7.37/1.48  sup_num_of_loops:                       128
% 7.37/1.48  sup_fw_superposition:                   8860
% 7.37/1.48  sup_bw_superposition:                   7307
% 7.37/1.48  sup_immediate_simplified:               6842
% 7.37/1.48  sup_given_eliminated:                   6
% 7.37/1.48  comparisons_done:                       0
% 7.37/1.48  comparisons_avoided:                    0
% 7.37/1.48  
% 7.37/1.48  ------ Simplifications
% 7.37/1.48  
% 7.37/1.48  
% 7.37/1.48  sim_fw_subset_subsumed:                 0
% 7.37/1.48  sim_bw_subset_subsumed:                 0
% 7.37/1.48  sim_fw_subsumed:                        670
% 7.37/1.48  sim_bw_subsumed:                        4
% 7.37/1.48  sim_fw_subsumption_res:                 0
% 7.37/1.48  sim_bw_subsumption_res:                 0
% 7.37/1.48  sim_tautology_del:                      0
% 7.37/1.48  sim_eq_tautology_del:                   1844
% 7.37/1.48  sim_eq_res_simp:                        0
% 7.37/1.48  sim_fw_demodulated:                     5127
% 7.37/1.48  sim_bw_demodulated:                     66
% 7.37/1.48  sim_light_normalised:                   2617
% 7.37/1.48  sim_joinable_taut:                      234
% 7.37/1.48  sim_joinable_simp:                      1
% 7.37/1.48  sim_ac_normalised:                      0
% 7.37/1.48  sim_smt_subsumption:                    0
% 7.37/1.48  
%------------------------------------------------------------------------------
