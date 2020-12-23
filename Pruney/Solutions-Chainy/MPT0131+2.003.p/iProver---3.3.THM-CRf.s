%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:18 EST 2020

% Result     : Theorem 15.39s
% Output     : CNFRefutation 15.39s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 809 expanded)
%              Number of clauses        :   43 ( 246 expanded)
%              Number of leaves         :   15 ( 238 expanded)
%              Depth                    :   18
%              Number of atoms          :   86 ( 810 expanded)
%              Number of equality atoms :   85 ( 809 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   13 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f21,f27,f27])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
    inference(definition_unfolding,[],[f23,f27,f27])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) != k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) != k3_enumset1(X0,X1,X2,X3,X4)
   => k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f32,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f27,f34])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f27,f33])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f28,f27,f34,f33])).

fof(f42,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f32,f27,f36,f35])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_45,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_33,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_50,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_45,c_33])).

cnf(c_118,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1,c_50])).

cnf(c_126,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_118,c_50])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_235,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_126,c_2])).

cnf(c_238,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_235,c_2])).

cnf(c_3,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4744,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_238,c_3])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_5,c_0])).

cnf(c_29,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)))))))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_20,c_2])).

cnf(c_60634,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_4744,c_29])).

cnf(c_32,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_498,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)),X3)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_3,c_32])).

cnf(c_148,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)),X3)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),X3) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_575,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,X1),X0),X3)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) ),
    inference(demodulation,[status(thm)],[c_498,c_148,c_238])).

cnf(c_60635,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_60634,c_575])).

cnf(c_119,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X0),X2)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_141,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
    inference(demodulation,[status(thm)],[c_119,c_126])).

cnf(c_134,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X3) ),
    inference(superposition,[status(thm)],[c_2,c_2])).

cnf(c_136,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
    inference(demodulation,[status(thm)],[c_134,c_2])).

cnf(c_142,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X3,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
    inference(demodulation,[status(thm)],[c_141,c_136])).

cnf(c_31,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_261,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_31])).

cnf(c_302,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) = k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)) ),
    inference(superposition,[status(thm)],[c_3,c_261])).

cnf(c_346,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)) ),
    inference(light_normalisation,[status(thm)],[c_302,c_238])).

cnf(c_347,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1) ),
    inference(demodulation,[status(thm)],[c_346,c_33])).

cnf(c_60636,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) ),
    inference(demodulation,[status(thm)],[c_60635,c_2,c_142,c_347])).

cnf(c_60637,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) ),
    inference(demodulation,[status(thm)],[c_60636,c_141])).

cnf(c_60638,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_60637,c_2,c_4744])).

cnf(c_62564,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(superposition,[status(thm)],[c_0,c_60638])).

cnf(c_60659,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X3) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X0),X1)) ),
    inference(superposition,[status(thm)],[c_2,c_4744])).

cnf(c_60986,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))),X3) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X0),X1)) ),
    inference(demodulation,[status(thm)],[c_60659,c_141])).

cnf(c_60987,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X2),X0),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X3,X1)),X0)),X2) ),
    inference(demodulation,[status(thm)],[c_60986,c_2,c_4744])).

cnf(c_62566,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_62564,c_60987])).

cnf(c_62567,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_62566])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.39/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.39/2.49  
% 15.39/2.49  ------  iProver source info
% 15.39/2.49  
% 15.39/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.39/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.39/2.49  git: non_committed_changes: false
% 15.39/2.49  git: last_make_outside_of_git: false
% 15.39/2.49  
% 15.39/2.49  ------ 
% 15.39/2.49  
% 15.39/2.49  ------ Input Options
% 15.39/2.49  
% 15.39/2.49  --out_options                           all
% 15.39/2.49  --tptp_safe_out                         true
% 15.39/2.49  --problem_path                          ""
% 15.39/2.49  --include_path                          ""
% 15.39/2.49  --clausifier                            res/vclausify_rel
% 15.39/2.49  --clausifier_options                    ""
% 15.39/2.49  --stdin                                 false
% 15.39/2.49  --stats_out                             all
% 15.39/2.49  
% 15.39/2.49  ------ General Options
% 15.39/2.49  
% 15.39/2.49  --fof                                   false
% 15.39/2.49  --time_out_real                         305.
% 15.39/2.49  --time_out_virtual                      -1.
% 15.39/2.49  --symbol_type_check                     false
% 15.39/2.49  --clausify_out                          false
% 15.39/2.49  --sig_cnt_out                           false
% 15.39/2.49  --trig_cnt_out                          false
% 15.39/2.49  --trig_cnt_out_tolerance                1.
% 15.39/2.49  --trig_cnt_out_sk_spl                   false
% 15.39/2.49  --abstr_cl_out                          false
% 15.39/2.49  
% 15.39/2.49  ------ Global Options
% 15.39/2.49  
% 15.39/2.49  --schedule                              default
% 15.39/2.49  --add_important_lit                     false
% 15.39/2.49  --prop_solver_per_cl                    1000
% 15.39/2.49  --min_unsat_core                        false
% 15.39/2.49  --soft_assumptions                      false
% 15.39/2.49  --soft_lemma_size                       3
% 15.39/2.49  --prop_impl_unit_size                   0
% 15.39/2.49  --prop_impl_unit                        []
% 15.39/2.49  --share_sel_clauses                     true
% 15.39/2.49  --reset_solvers                         false
% 15.39/2.49  --bc_imp_inh                            [conj_cone]
% 15.39/2.49  --conj_cone_tolerance                   3.
% 15.39/2.49  --extra_neg_conj                        none
% 15.39/2.49  --large_theory_mode                     true
% 15.39/2.49  --prolific_symb_bound                   200
% 15.39/2.49  --lt_threshold                          2000
% 15.39/2.49  --clause_weak_htbl                      true
% 15.39/2.49  --gc_record_bc_elim                     false
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing Options
% 15.39/2.49  
% 15.39/2.49  --preprocessing_flag                    true
% 15.39/2.49  --time_out_prep_mult                    0.1
% 15.39/2.49  --splitting_mode                        input
% 15.39/2.49  --splitting_grd                         true
% 15.39/2.49  --splitting_cvd                         false
% 15.39/2.49  --splitting_cvd_svl                     false
% 15.39/2.49  --splitting_nvd                         32
% 15.39/2.49  --sub_typing                            true
% 15.39/2.49  --prep_gs_sim                           true
% 15.39/2.49  --prep_unflatten                        true
% 15.39/2.49  --prep_res_sim                          true
% 15.39/2.49  --prep_upred                            true
% 15.39/2.49  --prep_sem_filter                       exhaustive
% 15.39/2.49  --prep_sem_filter_out                   false
% 15.39/2.49  --pred_elim                             true
% 15.39/2.49  --res_sim_input                         true
% 15.39/2.49  --eq_ax_congr_red                       true
% 15.39/2.49  --pure_diseq_elim                       true
% 15.39/2.49  --brand_transform                       false
% 15.39/2.49  --non_eq_to_eq                          false
% 15.39/2.49  --prep_def_merge                        true
% 15.39/2.49  --prep_def_merge_prop_impl              false
% 15.39/2.49  --prep_def_merge_mbd                    true
% 15.39/2.49  --prep_def_merge_tr_red                 false
% 15.39/2.49  --prep_def_merge_tr_cl                  false
% 15.39/2.49  --smt_preprocessing                     true
% 15.39/2.49  --smt_ac_axioms                         fast
% 15.39/2.49  --preprocessed_out                      false
% 15.39/2.49  --preprocessed_stats                    false
% 15.39/2.49  
% 15.39/2.49  ------ Abstraction refinement Options
% 15.39/2.49  
% 15.39/2.49  --abstr_ref                             []
% 15.39/2.49  --abstr_ref_prep                        false
% 15.39/2.49  --abstr_ref_until_sat                   false
% 15.39/2.49  --abstr_ref_sig_restrict                funpre
% 15.39/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.39/2.49  --abstr_ref_under                       []
% 15.39/2.49  
% 15.39/2.49  ------ SAT Options
% 15.39/2.49  
% 15.39/2.49  --sat_mode                              false
% 15.39/2.49  --sat_fm_restart_options                ""
% 15.39/2.49  --sat_gr_def                            false
% 15.39/2.49  --sat_epr_types                         true
% 15.39/2.49  --sat_non_cyclic_types                  false
% 15.39/2.49  --sat_finite_models                     false
% 15.39/2.49  --sat_fm_lemmas                         false
% 15.39/2.49  --sat_fm_prep                           false
% 15.39/2.49  --sat_fm_uc_incr                        true
% 15.39/2.49  --sat_out_model                         small
% 15.39/2.49  --sat_out_clauses                       false
% 15.39/2.49  
% 15.39/2.49  ------ QBF Options
% 15.39/2.49  
% 15.39/2.49  --qbf_mode                              false
% 15.39/2.49  --qbf_elim_univ                         false
% 15.39/2.49  --qbf_dom_inst                          none
% 15.39/2.49  --qbf_dom_pre_inst                      false
% 15.39/2.49  --qbf_sk_in                             false
% 15.39/2.49  --qbf_pred_elim                         true
% 15.39/2.49  --qbf_split                             512
% 15.39/2.49  
% 15.39/2.49  ------ BMC1 Options
% 15.39/2.49  
% 15.39/2.49  --bmc1_incremental                      false
% 15.39/2.49  --bmc1_axioms                           reachable_all
% 15.39/2.49  --bmc1_min_bound                        0
% 15.39/2.49  --bmc1_max_bound                        -1
% 15.39/2.49  --bmc1_max_bound_default                -1
% 15.39/2.49  --bmc1_symbol_reachability              true
% 15.39/2.49  --bmc1_property_lemmas                  false
% 15.39/2.49  --bmc1_k_induction                      false
% 15.39/2.49  --bmc1_non_equiv_states                 false
% 15.39/2.49  --bmc1_deadlock                         false
% 15.39/2.49  --bmc1_ucm                              false
% 15.39/2.49  --bmc1_add_unsat_core                   none
% 15.39/2.49  --bmc1_unsat_core_children              false
% 15.39/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.39/2.49  --bmc1_out_stat                         full
% 15.39/2.49  --bmc1_ground_init                      false
% 15.39/2.49  --bmc1_pre_inst_next_state              false
% 15.39/2.49  --bmc1_pre_inst_state                   false
% 15.39/2.49  --bmc1_pre_inst_reach_state             false
% 15.39/2.49  --bmc1_out_unsat_core                   false
% 15.39/2.49  --bmc1_aig_witness_out                  false
% 15.39/2.49  --bmc1_verbose                          false
% 15.39/2.49  --bmc1_dump_clauses_tptp                false
% 15.39/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.39/2.49  --bmc1_dump_file                        -
% 15.39/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.39/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.39/2.49  --bmc1_ucm_extend_mode                  1
% 15.39/2.49  --bmc1_ucm_init_mode                    2
% 15.39/2.49  --bmc1_ucm_cone_mode                    none
% 15.39/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.39/2.49  --bmc1_ucm_relax_model                  4
% 15.39/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.39/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.39/2.49  --bmc1_ucm_layered_model                none
% 15.39/2.49  --bmc1_ucm_max_lemma_size               10
% 15.39/2.49  
% 15.39/2.49  ------ AIG Options
% 15.39/2.49  
% 15.39/2.49  --aig_mode                              false
% 15.39/2.49  
% 15.39/2.49  ------ Instantiation Options
% 15.39/2.49  
% 15.39/2.49  --instantiation_flag                    true
% 15.39/2.49  --inst_sos_flag                         true
% 15.39/2.49  --inst_sos_phase                        true
% 15.39/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel_side                     num_symb
% 15.39/2.49  --inst_solver_per_active                1400
% 15.39/2.49  --inst_solver_calls_frac                1.
% 15.39/2.49  --inst_passive_queue_type               priority_queues
% 15.39/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.39/2.49  --inst_passive_queues_freq              [25;2]
% 15.39/2.49  --inst_dismatching                      true
% 15.39/2.49  --inst_eager_unprocessed_to_passive     true
% 15.39/2.49  --inst_prop_sim_given                   true
% 15.39/2.49  --inst_prop_sim_new                     false
% 15.39/2.49  --inst_subs_new                         false
% 15.39/2.49  --inst_eq_res_simp                      false
% 15.39/2.49  --inst_subs_given                       false
% 15.39/2.49  --inst_orphan_elimination               true
% 15.39/2.49  --inst_learning_loop_flag               true
% 15.39/2.49  --inst_learning_start                   3000
% 15.39/2.49  --inst_learning_factor                  2
% 15.39/2.49  --inst_start_prop_sim_after_learn       3
% 15.39/2.49  --inst_sel_renew                        solver
% 15.39/2.49  --inst_lit_activity_flag                true
% 15.39/2.49  --inst_restr_to_given                   false
% 15.39/2.49  --inst_activity_threshold               500
% 15.39/2.49  --inst_out_proof                        true
% 15.39/2.49  
% 15.39/2.49  ------ Resolution Options
% 15.39/2.49  
% 15.39/2.49  --resolution_flag                       true
% 15.39/2.49  --res_lit_sel                           adaptive
% 15.39/2.49  --res_lit_sel_side                      none
% 15.39/2.49  --res_ordering                          kbo
% 15.39/2.49  --res_to_prop_solver                    active
% 15.39/2.49  --res_prop_simpl_new                    false
% 15.39/2.49  --res_prop_simpl_given                  true
% 15.39/2.49  --res_passive_queue_type                priority_queues
% 15.39/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.39/2.49  --res_passive_queues_freq               [15;5]
% 15.39/2.49  --res_forward_subs                      full
% 15.39/2.49  --res_backward_subs                     full
% 15.39/2.49  --res_forward_subs_resolution           true
% 15.39/2.49  --res_backward_subs_resolution          true
% 15.39/2.49  --res_orphan_elimination                true
% 15.39/2.49  --res_time_limit                        2.
% 15.39/2.49  --res_out_proof                         true
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Options
% 15.39/2.49  
% 15.39/2.49  --superposition_flag                    true
% 15.39/2.49  --sup_passive_queue_type                priority_queues
% 15.39/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.39/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.39/2.49  --demod_completeness_check              fast
% 15.39/2.49  --demod_use_ground                      true
% 15.39/2.49  --sup_to_prop_solver                    passive
% 15.39/2.49  --sup_prop_simpl_new                    true
% 15.39/2.49  --sup_prop_simpl_given                  true
% 15.39/2.49  --sup_fun_splitting                     true
% 15.39/2.49  --sup_smt_interval                      50000
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Simplification Setup
% 15.39/2.49  
% 15.39/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.39/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.39/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.39/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.39/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_immed_triv                        [TrivRules]
% 15.39/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_bw_main                     []
% 15.39/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.39/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_input_bw                          []
% 15.39/2.49  
% 15.39/2.49  ------ Combination Options
% 15.39/2.49  
% 15.39/2.49  --comb_res_mult                         3
% 15.39/2.49  --comb_sup_mult                         2
% 15.39/2.49  --comb_inst_mult                        10
% 15.39/2.49  
% 15.39/2.49  ------ Debug Options
% 15.39/2.49  
% 15.39/2.49  --dbg_backtrace                         false
% 15.39/2.49  --dbg_dump_prop_clauses                 false
% 15.39/2.49  --dbg_dump_prop_clauses_file            -
% 15.39/2.49  --dbg_out_stat                          false
% 15.39/2.49  ------ Parsing...
% 15.39/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.39/2.49  ------ Proving...
% 15.39/2.49  ------ Problem Properties 
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  clauses                                 8
% 15.39/2.49  conjectures                             1
% 15.39/2.49  EPR                                     0
% 15.39/2.49  Horn                                    8
% 15.39/2.49  unary                                   8
% 15.39/2.49  binary                                  0
% 15.39/2.49  lits                                    8
% 15.39/2.49  lits eq                                 8
% 15.39/2.49  fd_pure                                 0
% 15.39/2.49  fd_pseudo                               0
% 15.39/2.49  fd_cond                                 0
% 15.39/2.49  fd_pseudo_cond                          0
% 15.39/2.49  AC symbols                              1
% 15.39/2.49  
% 15.39/2.49  ------ Schedule UEQ
% 15.39/2.49  
% 15.39/2.49  ------ pure equality problem: resolution off 
% 15.39/2.49  
% 15.39/2.49  ------ Option_UEQ Time Limit: Unbounded
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  ------ 
% 15.39/2.49  Current options:
% 15.39/2.49  ------ 
% 15.39/2.49  
% 15.39/2.49  ------ Input Options
% 15.39/2.49  
% 15.39/2.49  --out_options                           all
% 15.39/2.49  --tptp_safe_out                         true
% 15.39/2.49  --problem_path                          ""
% 15.39/2.49  --include_path                          ""
% 15.39/2.49  --clausifier                            res/vclausify_rel
% 15.39/2.49  --clausifier_options                    ""
% 15.39/2.49  --stdin                                 false
% 15.39/2.49  --stats_out                             all
% 15.39/2.49  
% 15.39/2.49  ------ General Options
% 15.39/2.49  
% 15.39/2.49  --fof                                   false
% 15.39/2.49  --time_out_real                         305.
% 15.39/2.49  --time_out_virtual                      -1.
% 15.39/2.49  --symbol_type_check                     false
% 15.39/2.49  --clausify_out                          false
% 15.39/2.49  --sig_cnt_out                           false
% 15.39/2.49  --trig_cnt_out                          false
% 15.39/2.49  --trig_cnt_out_tolerance                1.
% 15.39/2.49  --trig_cnt_out_sk_spl                   false
% 15.39/2.49  --abstr_cl_out                          false
% 15.39/2.49  
% 15.39/2.49  ------ Global Options
% 15.39/2.49  
% 15.39/2.49  --schedule                              default
% 15.39/2.49  --add_important_lit                     false
% 15.39/2.49  --prop_solver_per_cl                    1000
% 15.39/2.49  --min_unsat_core                        false
% 15.39/2.49  --soft_assumptions                      false
% 15.39/2.49  --soft_lemma_size                       3
% 15.39/2.49  --prop_impl_unit_size                   0
% 15.39/2.49  --prop_impl_unit                        []
% 15.39/2.49  --share_sel_clauses                     true
% 15.39/2.49  --reset_solvers                         false
% 15.39/2.49  --bc_imp_inh                            [conj_cone]
% 15.39/2.49  --conj_cone_tolerance                   3.
% 15.39/2.49  --extra_neg_conj                        none
% 15.39/2.49  --large_theory_mode                     true
% 15.39/2.49  --prolific_symb_bound                   200
% 15.39/2.49  --lt_threshold                          2000
% 15.39/2.49  --clause_weak_htbl                      true
% 15.39/2.49  --gc_record_bc_elim                     false
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing Options
% 15.39/2.49  
% 15.39/2.49  --preprocessing_flag                    true
% 15.39/2.49  --time_out_prep_mult                    0.1
% 15.39/2.49  --splitting_mode                        input
% 15.39/2.49  --splitting_grd                         true
% 15.39/2.49  --splitting_cvd                         false
% 15.39/2.49  --splitting_cvd_svl                     false
% 15.39/2.49  --splitting_nvd                         32
% 15.39/2.49  --sub_typing                            true
% 15.39/2.49  --prep_gs_sim                           true
% 15.39/2.49  --prep_unflatten                        true
% 15.39/2.49  --prep_res_sim                          true
% 15.39/2.49  --prep_upred                            true
% 15.39/2.49  --prep_sem_filter                       exhaustive
% 15.39/2.49  --prep_sem_filter_out                   false
% 15.39/2.49  --pred_elim                             true
% 15.39/2.49  --res_sim_input                         true
% 15.39/2.49  --eq_ax_congr_red                       true
% 15.39/2.49  --pure_diseq_elim                       true
% 15.39/2.49  --brand_transform                       false
% 15.39/2.49  --non_eq_to_eq                          false
% 15.39/2.49  --prep_def_merge                        true
% 15.39/2.49  --prep_def_merge_prop_impl              false
% 15.39/2.49  --prep_def_merge_mbd                    true
% 15.39/2.49  --prep_def_merge_tr_red                 false
% 15.39/2.49  --prep_def_merge_tr_cl                  false
% 15.39/2.49  --smt_preprocessing                     true
% 15.39/2.49  --smt_ac_axioms                         fast
% 15.39/2.49  --preprocessed_out                      false
% 15.39/2.49  --preprocessed_stats                    false
% 15.39/2.49  
% 15.39/2.49  ------ Abstraction refinement Options
% 15.39/2.49  
% 15.39/2.49  --abstr_ref                             []
% 15.39/2.49  --abstr_ref_prep                        false
% 15.39/2.49  --abstr_ref_until_sat                   false
% 15.39/2.49  --abstr_ref_sig_restrict                funpre
% 15.39/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.39/2.49  --abstr_ref_under                       []
% 15.39/2.49  
% 15.39/2.49  ------ SAT Options
% 15.39/2.49  
% 15.39/2.49  --sat_mode                              false
% 15.39/2.49  --sat_fm_restart_options                ""
% 15.39/2.49  --sat_gr_def                            false
% 15.39/2.49  --sat_epr_types                         true
% 15.39/2.49  --sat_non_cyclic_types                  false
% 15.39/2.49  --sat_finite_models                     false
% 15.39/2.49  --sat_fm_lemmas                         false
% 15.39/2.49  --sat_fm_prep                           false
% 15.39/2.49  --sat_fm_uc_incr                        true
% 15.39/2.49  --sat_out_model                         small
% 15.39/2.49  --sat_out_clauses                       false
% 15.39/2.49  
% 15.39/2.49  ------ QBF Options
% 15.39/2.49  
% 15.39/2.49  --qbf_mode                              false
% 15.39/2.49  --qbf_elim_univ                         false
% 15.39/2.49  --qbf_dom_inst                          none
% 15.39/2.49  --qbf_dom_pre_inst                      false
% 15.39/2.49  --qbf_sk_in                             false
% 15.39/2.49  --qbf_pred_elim                         true
% 15.39/2.49  --qbf_split                             512
% 15.39/2.49  
% 15.39/2.49  ------ BMC1 Options
% 15.39/2.49  
% 15.39/2.49  --bmc1_incremental                      false
% 15.39/2.49  --bmc1_axioms                           reachable_all
% 15.39/2.49  --bmc1_min_bound                        0
% 15.39/2.49  --bmc1_max_bound                        -1
% 15.39/2.49  --bmc1_max_bound_default                -1
% 15.39/2.49  --bmc1_symbol_reachability              true
% 15.39/2.49  --bmc1_property_lemmas                  false
% 15.39/2.49  --bmc1_k_induction                      false
% 15.39/2.49  --bmc1_non_equiv_states                 false
% 15.39/2.49  --bmc1_deadlock                         false
% 15.39/2.49  --bmc1_ucm                              false
% 15.39/2.49  --bmc1_add_unsat_core                   none
% 15.39/2.49  --bmc1_unsat_core_children              false
% 15.39/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.39/2.49  --bmc1_out_stat                         full
% 15.39/2.49  --bmc1_ground_init                      false
% 15.39/2.49  --bmc1_pre_inst_next_state              false
% 15.39/2.49  --bmc1_pre_inst_state                   false
% 15.39/2.49  --bmc1_pre_inst_reach_state             false
% 15.39/2.49  --bmc1_out_unsat_core                   false
% 15.39/2.49  --bmc1_aig_witness_out                  false
% 15.39/2.49  --bmc1_verbose                          false
% 15.39/2.49  --bmc1_dump_clauses_tptp                false
% 15.39/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.39/2.49  --bmc1_dump_file                        -
% 15.39/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.39/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.39/2.49  --bmc1_ucm_extend_mode                  1
% 15.39/2.49  --bmc1_ucm_init_mode                    2
% 15.39/2.49  --bmc1_ucm_cone_mode                    none
% 15.39/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.39/2.49  --bmc1_ucm_relax_model                  4
% 15.39/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.39/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.39/2.49  --bmc1_ucm_layered_model                none
% 15.39/2.49  --bmc1_ucm_max_lemma_size               10
% 15.39/2.49  
% 15.39/2.49  ------ AIG Options
% 15.39/2.49  
% 15.39/2.49  --aig_mode                              false
% 15.39/2.49  
% 15.39/2.49  ------ Instantiation Options
% 15.39/2.49  
% 15.39/2.49  --instantiation_flag                    false
% 15.39/2.49  --inst_sos_flag                         true
% 15.39/2.49  --inst_sos_phase                        true
% 15.39/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel_side                     num_symb
% 15.39/2.49  --inst_solver_per_active                1400
% 15.39/2.49  --inst_solver_calls_frac                1.
% 15.39/2.49  --inst_passive_queue_type               priority_queues
% 15.39/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.39/2.49  --inst_passive_queues_freq              [25;2]
% 15.39/2.49  --inst_dismatching                      true
% 15.39/2.49  --inst_eager_unprocessed_to_passive     true
% 15.39/2.49  --inst_prop_sim_given                   true
% 15.39/2.49  --inst_prop_sim_new                     false
% 15.39/2.49  --inst_subs_new                         false
% 15.39/2.49  --inst_eq_res_simp                      false
% 15.39/2.49  --inst_subs_given                       false
% 15.39/2.49  --inst_orphan_elimination               true
% 15.39/2.49  --inst_learning_loop_flag               true
% 15.39/2.49  --inst_learning_start                   3000
% 15.39/2.49  --inst_learning_factor                  2
% 15.39/2.49  --inst_start_prop_sim_after_learn       3
% 15.39/2.49  --inst_sel_renew                        solver
% 15.39/2.49  --inst_lit_activity_flag                true
% 15.39/2.49  --inst_restr_to_given                   false
% 15.39/2.49  --inst_activity_threshold               500
% 15.39/2.49  --inst_out_proof                        true
% 15.39/2.49  
% 15.39/2.49  ------ Resolution Options
% 15.39/2.49  
% 15.39/2.49  --resolution_flag                       false
% 15.39/2.49  --res_lit_sel                           adaptive
% 15.39/2.49  --res_lit_sel_side                      none
% 15.39/2.49  --res_ordering                          kbo
% 15.39/2.49  --res_to_prop_solver                    active
% 15.39/2.49  --res_prop_simpl_new                    false
% 15.39/2.49  --res_prop_simpl_given                  true
% 15.39/2.49  --res_passive_queue_type                priority_queues
% 15.39/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.39/2.49  --res_passive_queues_freq               [15;5]
% 15.39/2.49  --res_forward_subs                      full
% 15.39/2.49  --res_backward_subs                     full
% 15.39/2.49  --res_forward_subs_resolution           true
% 15.39/2.49  --res_backward_subs_resolution          true
% 15.39/2.49  --res_orphan_elimination                true
% 15.39/2.49  --res_time_limit                        2.
% 15.39/2.49  --res_out_proof                         true
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Options
% 15.39/2.49  
% 15.39/2.49  --superposition_flag                    true
% 15.39/2.49  --sup_passive_queue_type                priority_queues
% 15.39/2.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.39/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.39/2.49  --demod_completeness_check              fast
% 15.39/2.49  --demod_use_ground                      true
% 15.39/2.49  --sup_to_prop_solver                    active
% 15.39/2.49  --sup_prop_simpl_new                    false
% 15.39/2.49  --sup_prop_simpl_given                  false
% 15.39/2.49  --sup_fun_splitting                     true
% 15.39/2.49  --sup_smt_interval                      10000
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Simplification Setup
% 15.39/2.49  
% 15.39/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.39/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.49  --sup_full_triv                         [TrivRules]
% 15.39/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.39/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_immed_triv                        [TrivRules]
% 15.39/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_bw_main                     []
% 15.39/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.39/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 15.39/2.49  
% 15.39/2.49  ------ Combination Options
% 15.39/2.49  
% 15.39/2.49  --comb_res_mult                         1
% 15.39/2.49  --comb_sup_mult                         1
% 15.39/2.49  --comb_inst_mult                        1000000
% 15.39/2.49  
% 15.39/2.49  ------ Debug Options
% 15.39/2.49  
% 15.39/2.49  --dbg_backtrace                         false
% 15.39/2.49  --dbg_dump_prop_clauses                 false
% 15.39/2.49  --dbg_dump_prop_clauses_file            -
% 15.39/2.49  --dbg_out_stat                          false
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  ------ Proving...
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  % SZS status Theorem for theBenchmark.p
% 15.39/2.49  
% 15.39/2.49   Resolution empty clause
% 15.39/2.49  
% 15.39/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  fof(f1,axiom,(
% 15.39/2.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f19,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f1])).
% 15.39/2.49  
% 15.39/2.49  fof(f3,axiom,(
% 15.39/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f21,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.39/2.49    inference(cnf_transformation,[],[f3])).
% 15.39/2.49  
% 15.39/2.49  fof(f9,axiom,(
% 15.39/2.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f27,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f9])).
% 15.39/2.49  
% 15.39/2.49  fof(f37,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 15.39/2.49    inference(definition_unfolding,[],[f21,f27,f27])).
% 15.39/2.49  
% 15.39/2.49  fof(f8,axiom,(
% 15.39/2.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f26,plain,(
% 15.39/2.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 15.39/2.49    inference(cnf_transformation,[],[f8])).
% 15.39/2.49  
% 15.39/2.49  fof(f2,axiom,(
% 15.39/2.49    k1_xboole_0 = o_0_0_xboole_0),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f20,plain,(
% 15.39/2.49    k1_xboole_0 = o_0_0_xboole_0),
% 15.39/2.49    inference(cnf_transformation,[],[f2])).
% 15.39/2.49  
% 15.39/2.49  fof(f41,plain,(
% 15.39/2.49    ( ! [X0] : (k5_xboole_0(X0,X0) = o_0_0_xboole_0) )),
% 15.39/2.49    inference(definition_unfolding,[],[f26,f20])).
% 15.39/2.49  
% 15.39/2.49  fof(f7,axiom,(
% 15.39/2.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f25,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f7])).
% 15.39/2.49  
% 15.39/2.49  fof(f6,axiom,(
% 15.39/2.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f24,plain,(
% 15.39/2.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.39/2.49    inference(cnf_transformation,[],[f6])).
% 15.39/2.49  
% 15.39/2.49  fof(f40,plain,(
% 15.39/2.49    ( ! [X0] : (k5_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 15.39/2.49    inference(definition_unfolding,[],[f24,f20])).
% 15.39/2.49  
% 15.39/2.49  fof(f4,axiom,(
% 15.39/2.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f22,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f4])).
% 15.39/2.49  
% 15.39/2.49  fof(f38,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 15.39/2.49    inference(definition_unfolding,[],[f22,f27])).
% 15.39/2.49  
% 15.39/2.49  fof(f5,axiom,(
% 15.39/2.49    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f23,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 15.39/2.49    inference(cnf_transformation,[],[f5])).
% 15.39/2.49  
% 15.39/2.49  fof(f39,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f23,f27,f27])).
% 15.39/2.49  
% 15.39/2.49  fof(f14,conjecture,(
% 15.39/2.49    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f15,negated_conjecture,(
% 15.39/2.49    ~! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 15.39/2.49    inference(negated_conjecture,[],[f14])).
% 15.39/2.49  
% 15.39/2.49  fof(f16,plain,(
% 15.39/2.49    ? [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) != k3_enumset1(X0,X1,X2,X3,X4)),
% 15.39/2.49    inference(ennf_transformation,[],[f15])).
% 15.39/2.49  
% 15.39/2.49  fof(f17,plain,(
% 15.39/2.49    ? [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) != k3_enumset1(X0,X1,X2,X3,X4) => k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 15.39/2.49    introduced(choice_axiom,[])).
% 15.39/2.49  
% 15.39/2.49  fof(f18,plain,(
% 15.39/2.49    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 15.39/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 15.39/2.49  
% 15.39/2.49  fof(f32,plain,(
% 15.39/2.49    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 15.39/2.49    inference(cnf_transformation,[],[f18])).
% 15.39/2.49  
% 15.39/2.49  fof(f13,axiom,(
% 15.39/2.49    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f31,plain,(
% 15.39/2.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f13])).
% 15.39/2.49  
% 15.39/2.49  fof(f36,plain,(
% 15.39/2.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f31,f27,f34])).
% 15.39/2.49  
% 15.39/2.49  fof(f10,axiom,(
% 15.39/2.49    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f28,plain,(
% 15.39/2.49    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f10])).
% 15.39/2.49  
% 15.39/2.49  fof(f12,axiom,(
% 15.39/2.49    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f30,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f12])).
% 15.39/2.49  
% 15.39/2.49  fof(f34,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k1_enumset1(X0,X1,X2)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f30,f27,f33])).
% 15.39/2.49  
% 15.39/2.49  fof(f11,axiom,(
% 15.39/2.49    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f29,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f11])).
% 15.39/2.49  
% 15.39/2.49  fof(f33,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f29,f27])).
% 15.39/2.49  
% 15.39/2.49  fof(f35,plain,(
% 15.39/2.49    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f28,f27,f34,f33])).
% 15.39/2.49  
% 15.39/2.49  fof(f42,plain,(
% 15.39/2.49    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))),
% 15.39/2.49    inference(definition_unfolding,[],[f32,f27,f36,f35])).
% 15.39/2.49  
% 15.39/2.49  cnf(c_0,plain,
% 15.39/2.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f19]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 15.39/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6,plain,
% 15.39/2.49      ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5,plain,
% 15.39/2.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.39/2.49      inference(cnf_transformation,[],[f25]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_45,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4,plain,
% 15.39/2.49      ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_33,plain,
% 15.39/2.49      ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_50,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_45,c_33]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_118,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_1,c_50]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_126,plain,
% 15.39/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_118,c_50]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2,plain,
% 15.39/2.49      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 15.39/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_235,plain,
% 15.39/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_126,c_2]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_238,plain,
% 15.39/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_235,c_2]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 15.39/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4744,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_238,c_3]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7,negated_conjecture,
% 15.39/2.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
% 15.39/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_20,negated_conjecture,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
% 15.39/2.49      inference(theory_normalisation,[status(thm)],[c_7,c_5,c_0]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_29,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)))))))),k1_tarski(sK0))) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_20,c_2]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60634,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_4744,c_29]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_32,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_498,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)),X3)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_3,c_32]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_148,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)),X3)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),X3) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_575,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X2,X1),X0),X3)) = k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_498,c_148,c_238]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60635,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))),k1_tarski(sK0))) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_60634,c_575]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_119,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X0),X2)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_141,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_119,c_126]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_134,plain,
% 15.39/2.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X3) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2,c_2]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_136,plain,
% 15.39/2.49      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X3,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_134,c_2]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_142,plain,
% 15.39/2.49      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X3,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_141,c_136]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_31,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_261,plain,
% 15.39/2.49      ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_4,c_31]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_302,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) = k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_3,c_261]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_346,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)) ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_302,c_238]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_347,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_346,c_33]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60636,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_60635,c_2,c_142,c_347]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60637,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_60636,c_141]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60638,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_60637,c_2,c_4744]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_62564,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_0,c_60638]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60659,plain,
% 15.39/2.49      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X3) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X0),X1)) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2,c_4744]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60986,plain,
% 15.39/2.49      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))),X3) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X0),X1)) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_60659,c_141]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_60987,plain,
% 15.39/2.49      ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X2),X0),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X3,X1)),X0)),X2) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_60986,c_2,c_4744]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_62566,plain,
% 15.39/2.49      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_62564,c_60987]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_62567,plain,
% 15.39/2.49      ( $false ),
% 15.39/2.49      inference(equality_resolution_simp,[status(thm)],[c_62566]) ).
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  ------                               Statistics
% 15.39/2.49  
% 15.39/2.49  ------ General
% 15.39/2.49  
% 15.39/2.49  abstr_ref_over_cycles:                  0
% 15.39/2.49  abstr_ref_under_cycles:                 0
% 15.39/2.49  gc_basic_clause_elim:                   0
% 15.39/2.49  forced_gc_time:                         0
% 15.39/2.49  parsing_time:                           0.006
% 15.39/2.49  unif_index_cands_time:                  0.
% 15.39/2.49  unif_index_add_time:                    0.
% 15.39/2.49  orderings_time:                         0.
% 15.39/2.49  out_proof_time:                         0.007
% 15.39/2.49  total_time:                             1.688
% 15.39/2.49  num_of_symbols:                         40
% 15.39/2.49  num_of_terms:                           154472
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing
% 15.39/2.49  
% 15.39/2.49  num_of_splits:                          0
% 15.39/2.49  num_of_split_atoms:                     0
% 15.39/2.49  num_of_reused_defs:                     0
% 15.39/2.49  num_eq_ax_congr_red:                    0
% 15.39/2.49  num_of_sem_filtered_clauses:            0
% 15.39/2.49  num_of_subtypes:                        0
% 15.39/2.49  monotx_restored_types:                  0
% 15.39/2.49  sat_num_of_epr_types:                   0
% 15.39/2.49  sat_num_of_non_cyclic_types:            0
% 15.39/2.49  sat_guarded_non_collapsed_types:        0
% 15.39/2.49  num_pure_diseq_elim:                    0
% 15.39/2.49  simp_replaced_by:                       0
% 15.39/2.49  res_preprocessed:                       21
% 15.39/2.49  prep_upred:                             0
% 15.39/2.49  prep_unflattend:                        0
% 15.39/2.49  smt_new_axioms:                         0
% 15.39/2.49  pred_elim_cands:                        0
% 15.39/2.49  pred_elim:                              0
% 15.39/2.49  pred_elim_cl:                           0
% 15.39/2.49  pred_elim_cycles:                       0
% 15.39/2.49  merged_defs:                            0
% 15.39/2.49  merged_defs_ncl:                        0
% 15.39/2.49  bin_hyper_res:                          0
% 15.39/2.49  prep_cycles:                            2
% 15.39/2.49  pred_elim_time:                         0.
% 15.39/2.49  splitting_time:                         0.
% 15.39/2.49  sem_filter_time:                        0.
% 15.39/2.49  monotx_time:                            0.
% 15.39/2.49  subtype_inf_time:                       0.
% 15.39/2.49  
% 15.39/2.49  ------ Problem properties
% 15.39/2.49  
% 15.39/2.49  clauses:                                8
% 15.39/2.49  conjectures:                            1
% 15.39/2.49  epr:                                    0
% 15.39/2.49  horn:                                   8
% 15.39/2.49  ground:                                 1
% 15.39/2.49  unary:                                  8
% 15.39/2.49  binary:                                 0
% 15.39/2.49  lits:                                   8
% 15.39/2.49  lits_eq:                                8
% 15.39/2.49  fd_pure:                                0
% 15.39/2.49  fd_pseudo:                              0
% 15.39/2.49  fd_cond:                                0
% 15.39/2.49  fd_pseudo_cond:                         0
% 15.39/2.49  ac_symbols:                             1
% 15.39/2.49  
% 15.39/2.49  ------ Propositional Solver
% 15.39/2.49  
% 15.39/2.49  prop_solver_calls:                      13
% 15.39/2.49  prop_fast_solver_calls:                 56
% 15.39/2.49  smt_solver_calls:                       0
% 15.39/2.49  smt_fast_solver_calls:                  0
% 15.39/2.49  prop_num_of_clauses:                    191
% 15.39/2.49  prop_preprocess_simplified:             360
% 15.39/2.49  prop_fo_subsumed:                       0
% 15.39/2.49  prop_solver_time:                       0.
% 15.39/2.49  smt_solver_time:                        0.
% 15.39/2.49  smt_fast_solver_time:                   0.
% 15.39/2.49  prop_fast_solver_time:                  0.
% 15.39/2.49  prop_unsat_core_time:                   0.
% 15.39/2.49  
% 15.39/2.49  ------ QBF
% 15.39/2.49  
% 15.39/2.49  qbf_q_res:                              0
% 15.39/2.49  qbf_num_tautologies:                    0
% 15.39/2.49  qbf_prep_cycles:                        0
% 15.39/2.49  
% 15.39/2.49  ------ BMC1
% 15.39/2.49  
% 15.39/2.49  bmc1_current_bound:                     -1
% 15.39/2.49  bmc1_last_solved_bound:                 -1
% 15.39/2.49  bmc1_unsat_core_size:                   -1
% 15.39/2.49  bmc1_unsat_core_parents_size:           -1
% 15.39/2.49  bmc1_merge_next_fun:                    0
% 15.39/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.39/2.49  
% 15.39/2.49  ------ Instantiation
% 15.39/2.49  
% 15.39/2.49  inst_num_of_clauses:                    0
% 15.39/2.49  inst_num_in_passive:                    0
% 15.39/2.49  inst_num_in_active:                     0
% 15.39/2.49  inst_num_in_unprocessed:                0
% 15.39/2.49  inst_num_of_loops:                      0
% 15.39/2.49  inst_num_of_learning_restarts:          0
% 15.39/2.49  inst_num_moves_active_passive:          0
% 15.39/2.49  inst_lit_activity:                      0
% 15.39/2.49  inst_lit_activity_moves:                0
% 15.39/2.49  inst_num_tautologies:                   0
% 15.39/2.49  inst_num_prop_implied:                  0
% 15.39/2.49  inst_num_existing_simplified:           0
% 15.39/2.49  inst_num_eq_res_simplified:             0
% 15.39/2.49  inst_num_child_elim:                    0
% 15.39/2.49  inst_num_of_dismatching_blockings:      0
% 15.39/2.49  inst_num_of_non_proper_insts:           0
% 15.39/2.49  inst_num_of_duplicates:                 0
% 15.39/2.49  inst_inst_num_from_inst_to_res:         0
% 15.39/2.49  inst_dismatching_checking_time:         0.
% 15.39/2.49  
% 15.39/2.49  ------ Resolution
% 15.39/2.49  
% 15.39/2.49  res_num_of_clauses:                     0
% 15.39/2.49  res_num_in_passive:                     0
% 15.39/2.49  res_num_in_active:                      0
% 15.39/2.49  res_num_of_loops:                       23
% 15.39/2.49  res_forward_subset_subsumed:            0
% 15.39/2.49  res_backward_subset_subsumed:           0
% 15.39/2.49  res_forward_subsumed:                   0
% 15.39/2.49  res_backward_subsumed:                  0
% 15.39/2.49  res_forward_subsumption_resolution:     0
% 15.39/2.49  res_backward_subsumption_resolution:    0
% 15.39/2.49  res_clause_to_clause_subsumption:       201683
% 15.39/2.49  res_orphan_elimination:                 0
% 15.39/2.49  res_tautology_del:                      0
% 15.39/2.49  res_num_eq_res_simplified:              0
% 15.39/2.49  res_num_sel_changes:                    0
% 15.39/2.49  res_moves_from_active_to_pass:          0
% 15.39/2.49  
% 15.39/2.49  ------ Superposition
% 15.39/2.49  
% 15.39/2.49  sup_time_total:                         0.
% 15.39/2.49  sup_time_generating:                    0.
% 15.39/2.49  sup_time_sim_full:                      0.
% 15.39/2.49  sup_time_sim_immed:                     0.
% 15.39/2.49  
% 15.39/2.49  sup_num_of_clauses:                     2908
% 15.39/2.49  sup_num_in_active:                      124
% 15.39/2.49  sup_num_in_passive:                     2784
% 15.39/2.49  sup_num_of_loops:                       127
% 15.39/2.49  sup_fw_superposition:                   21018
% 15.39/2.49  sup_bw_superposition:                   14548
% 15.39/2.49  sup_immediate_simplified:               21413
% 15.39/2.49  sup_given_eliminated:                   1
% 15.39/2.49  comparisons_done:                       0
% 15.39/2.49  comparisons_avoided:                    0
% 15.39/2.49  
% 15.39/2.49  ------ Simplifications
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  sim_fw_subset_subsumed:                 0
% 15.39/2.49  sim_bw_subset_subsumed:                 0
% 15.39/2.49  sim_fw_subsumed:                        558
% 15.39/2.49  sim_bw_subsumed:                        8
% 15.39/2.49  sim_fw_subsumption_res:                 0
% 15.39/2.49  sim_bw_subsumption_res:                 0
% 15.39/2.49  sim_tautology_del:                      0
% 15.39/2.49  sim_eq_tautology_del:                   4096
% 15.39/2.49  sim_eq_res_simp:                        0
% 15.39/2.49  sim_fw_demodulated:                     21123
% 15.39/2.49  sim_bw_demodulated:                     38
% 15.39/2.49  sim_light_normalised:                   5033
% 15.39/2.49  sim_joinable_taut:                      1139
% 15.39/2.49  sim_joinable_simp:                      0
% 15.39/2.49  sim_ac_normalised:                      0
% 15.39/2.49  sim_smt_subsumption:                    0
% 15.39/2.49  
%------------------------------------------------------------------------------
